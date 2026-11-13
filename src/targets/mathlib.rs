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
