//! The Mathlib target, which writes the certificate as witnesses for Mathlib's `primality` tactic
//! (`docs/targets/mathlib.md`).

use crate::input::Input;
use crate::targets::Target;
use crate::verify::Certificate;

/// Lean's default `exponentiation.threshold`. Unless the option is raised, `norm_num` evaluates
/// no power of a base above 1 with a larger exponent.
const LEAN_EXPONENT_THRESHOLD: u32 = 256;

/// The Mathlib target. Its text is checked against Mathlib's master, which is also the default
/// project of the Lean playground.
pub const TARGET: Target = Target {
    name: "mathlib",
    label: "Mathlib",
    tool: "Mathlib's `primality` tactic",
    release: None,
    playground: Some("https://live.lean-lang.org/"),
    render,
};

/// The imports and the `example` of `cert`. A `^` in the input makes the text import
/// `norm_num`'s power extension, which evaluates the goal's number.
fn render(cert: &Certificate, input: &Input) -> Result<(Vec<String>, String), String> {
    let mut imports = vec!["Mathlib.Tactic.Primality".to_string()];
    if input.max_exponent.is_some() {
        imports.push("Mathlib.Tactic.NormNum.Pow".to_string());
    }
    Ok((imports, render_example(cert, input)))
}

/// The `example` proving `input.term` prime with `cert`'s entries as witnesses, in the given
/// order and in exactly the layout of `docs/targets/mathlib.md` (`by primality` alone when there
/// is no entry). An exponent above Lean's default threshold raises it on the line above.
fn render_example(cert: &Certificate, input: &Input) -> String {
    let threshold = match input.max_exponent {
        Some(e) if e > LEAN_EXPONENT_THRESHOLD => {
            format!("set_option exponentiation.threshold {e} in\n")
        }
        _ => String::new(),
    };
    let term = &input.term;
    if cert.entries.is_empty() {
        return format!("{threshold}example : Nat.Prime {term} := by primality\n");
    }
    let lines: Vec<String> = cert
        .entries
        .iter()
        .map(|entry| {
            let factors: Vec<String> = entry.factors.iter().map(ToString::to_string).collect();
            format!(
                "    .lucas {{ root := {}, primeFactors := [{}] }}",
                entry.root,
                factors.join(", ")
            )
        })
        .collect();
    format!(
        "{threshold}example : Nat.Prime {term} := by\n  primality (cert := .witnesses [\n{}])\n",
        lines.join(",\n")
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith::BigUint;
    use crate::input::parse_input;
    use crate::verify::Entry;

    fn big(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
    }

    fn input(text: &str) -> Input {
        parse_input(text, 2000).unwrap()
    }

    fn entry(q: &str, root: u64, factors: &[u64]) -> Entry {
        Entry {
            q: big(q),
            root,
            factors: factors.iter().map(|&r| BigUint::from(r)).collect(),
        }
    }

    #[test]
    fn renders_a_two_entry_certificate() {
        // 649657 - 1 = 2^3 · 3^2 · 7 · 1289 and 1289 - 1 = 2^3 · 7 · 23.
        let cert = Certificate {
            n: big("649657"),
            entries: vec![
                entry("649657", 5, &[2, 3, 7, 1289]),
                entry("1289", 6, &[2, 7, 23]),
            ],
        };
        let expected = "example : Nat.Prime 649657 := by\n\
                        \x20 primality (cert := .witnesses [\n\
                        \x20   .lucas { root := 5, primeFactors := [2, 3, 7, 1289] },\n\
                        \x20   .lucas { root := 6, primeFactors := [2, 7, 23] }])\n";
        assert_eq!(render_example(&cert, &input("649657")), expected);
    }

    #[test]
    fn renders_a_one_entry_certificate() {
        let cert = Certificate {
            n: big("65537"),
            entries: vec![entry("65537", 3, &[2])],
        };
        let expected = "example : Nat.Prime 65537 := by\n\
                        \x20 primality (cert := .witnesses [\n\
                        \x20   .lucas { root := 3, primeFactors := [2] }])\n";
        assert_eq!(render_example(&cert, &input("65537")), expected);
        let expected = "example : Nat.Prime (2 ^ 16 + 1) := by\n\
                        \x20 primality (cert := .witnesses [\n\
                        \x20   .lucas { root := 3, primeFactors := [2] }])\n";
        assert_eq!(render_example(&cert, &input("2^16 + 1")), expected);
        // An exponent above 256 raises the threshold under which `norm_num` evaluates powers.
        let expected = "set_option exponentiation.threshold 300 in\n\
                        example : Nat.Prime (2 ^ 300 - 2 ^ 300 + 65537) := by\n\
                        \x20 primality (cert := .witnesses [\n\
                        \x20   .lucas { root := 3, primeFactors := [2] }])\n";
        assert_eq!(
            render_example(&cert, &input("2^300 - 2^300 + 65537")),
            expected
        );
    }

    #[test]
    fn renders_the_empty_certificate() {
        let cert = Certificate {
            n: big("997"),
            entries: vec![],
        };
        assert_eq!(
            render_example(&cert, &input("997")),
            "example : Nat.Prime 997 := by primality\n"
        );
    }

    #[test]
    fn imports_the_power_extension_for_a_power() {
        let cert = Certificate {
            n: big("997"),
            entries: vec![],
        };
        let (imports, text) = render(&cert, &input("997")).unwrap();
        assert_eq!(imports, ["Mathlib.Tactic.Primality"]);
        assert_eq!(text, render_example(&cert, &input("997")));
        let (imports, _) = render(&cert, &input("10^3 - 3")).unwrap();
        assert_eq!(
            imports,
            ["Mathlib.Tactic.Primality", "Mathlib.Tactic.NormNum.Pow"]
        );
    }
}
