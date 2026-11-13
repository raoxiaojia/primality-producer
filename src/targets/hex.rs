//! The HexPrime target: the certificate as a literal of Hex's `PrimeCert` (the `hex-primality`
//! library), its check against the rules of Hex's checker, and its Lean text
//! (`docs/targets/hex.md`).

use std::collections::BTreeMap;

use num_traits::{One, Zero};

use crate::arith::{is_small_prime, to_u64, BigUint};
use crate::input::Input;
use crate::targets::Target;
use crate::verify::{Certificate, Entry};

/// Hex's table holds every prime below this bound (`primeTableBound`).
const TABLE_BOUND: u64 = 100_000;

/// The HexPrime target. No online editor has the library.
pub const TARGET: Target = Target {
    name: "hexprime",
    label: "HexPrime",
    tool: "Hex's `hex-primality` library",
    release: Some("hex-primality v0.10.0"),
    playground: None,
    render,
};

/// The import and the `example` of `cert`'s tree (`render_example`), once the tree passes
/// `check`.
fn render(cert: &Certificate, input: &Input) -> Result<(Vec<String>, String), String> {
    let tree = HexCert::from_certificate(cert)?;
    check(&tree, cert)?;
    Ok((
        vec!["HexPrimality".to_string()],
        render_example(&tree, &input.term),
    ))
}

/// A literal of Hex's `PrimeCert`, in the two constructors we emit.
#[derive(Clone, Debug, PartialEq, Eq)]
enum HexCert {
    /// `.small n`: `n` is a prime of Hex's table.
    Small(u64),
    /// `.pock n factors`: Pocklington's test with the factor entries of `n − 1`.
    Pock { n: BigUint, factors: Vec<HexFactor> },
}

/// The factor entry `(base, e, child)` of a `.pock` node: the prime `child.subject()` divides
/// `n − 1` exactly `e + 1` times. The exponent is stored off by one, as Hex stores it.
#[derive(Clone, Debug, PartialEq, Eq)]
struct HexFactor {
    base: u64,
    e: u32,
    child: HexCert,
}

impl HexCert {
    /// The number the certificate is about.
    fn subject(&self) -> BigUint {
        match self {
            HexCert::Small(n) => BigUint::from(*n),
            HexCert::Pock { n, .. } => n.clone(),
        }
    }

    /// The tree of `cert.n`: `.small q` for every prime `q < TABLE_BOUND`, else `.pock q` with one
    /// entry per factor of `q`'s entry, in its order, each with the entry's root as base and its
    /// multiplicity in `q − 1`. A prime met twice is written out twice. Errors when a prime at or
    /// above `TABLE_BOUND` has no entry. Only for a certificate `verify::verify` accepted (a
    /// factor 1, or an entry that reaches itself, would not terminate).
    fn from_certificate(cert: &Certificate) -> Result<HexCert, String> {
        build(&cert.n, &index(cert))
    }
}

/// The entries of `cert` by their prime.
fn index(cert: &Certificate) -> BTreeMap<&BigUint, &Entry> {
    cert.entries.iter().map(|entry| (&entry.q, entry)).collect()
}

/// The tree of the prime `q` (see `HexCert::from_certificate`).
fn build(q: &BigUint, index: &BTreeMap<&BigUint, &Entry>) -> Result<HexCert, String> {
    if let Some(small) = to_u64(q).filter(|&x| x < TABLE_BOUND) {
        return Ok(HexCert::Small(small));
    }
    let entry = index
        .get(q)
        .ok_or_else(|| format!("{q} is at least {TABLE_BOUND} and has no entry"))?;
    let mut rest = q - 1u32;
    let mut factors = Vec::with_capacity(entry.factors.len());
    for r in &entry.factors {
        // `verify` has checked that `r` divides `q − 1`, so it is divided out once; `e` counts
        // the further divisions.
        rest /= r;
        let mut e = 0;
        while (&rest % r).is_zero() {
            rest /= r;
            e += 1;
        }
        factors.push(HexFactor {
            base: entry.root,
            e,
            child: build(r, index)?,
        });
    }
    Ok(HexCert::Pock {
        n: q.clone(),
        factors,
    })
}

/// Hex's `checkPrime` for the two constructors, on the tree `tree` of `cert.n`: `.small n` needs
/// `n < TABLE_BOUND` prime by trial division; `.pock n` needs `n` odd and at least 2, the subjects
/// each at least 2 and strictly ascending, `F = ∏ subject ^ (e + 1)` dividing `n − 1` with
/// `n < F²`, and its children to pass.
///
/// The modular conditions of each entry (`base ^ (n − 1) ≡ 1` and `gcd(base ^ ((n − 1) / q) − 1,
/// n) = 1`) are not recomputed. The node's subjects must equal the factors of `cert`'s entry for
/// `n` and every base its root, and `verify::verify` has shown that root to be a primitive root
/// of the prime `n` for those factors, which gives both conditions. So the check means something
/// only after `verify` accepted `cert`. The error names the node and the condition.
fn check(tree: &HexCert, cert: &Certificate) -> Result<(), String> {
    if tree.subject() != cert.n {
        return Err(format!(
            "the tree is about {}, not about n = {}",
            tree.subject(),
            cert.n
        ));
    }
    check_node(tree, &index(cert))
}

/// `check` for the node `node`.
fn check_node(node: &HexCert, index: &BTreeMap<&BigUint, &Entry>) -> Result<(), String> {
    let (n, factors) = match node {
        HexCert::Small(n) => {
            return if *n < TABLE_BOUND && is_small_prime(*n) {
                Ok(())
            } else {
                Err(format!(".small {n}: not a prime below {TABLE_BOUND}"))
            };
        }
        HexCert::Pock { n, factors } => (n, factors),
    };
    let label = format!(".pock {n}");
    if *n < BigUint::from(2u32) || (n % 2u32).is_zero() {
        return Err(format!("{label}: n is not odd and at least 2"));
    }
    let subjects: Vec<BigUint> = factors.iter().map(|f| f.child.subject()).collect();
    let mut lower = BigUint::one();
    for subject in &subjects {
        if *subject <= lower {
            return Err(format!(
                "{label}: the subject {subject} is not above {lower}"
            ));
        }
        lower = subject.clone();
    }
    let mut product = BigUint::one();
    for (factor, subject) in factors.iter().zip(&subjects) {
        product *= subject.pow(factor.e + 1);
    }
    let n_minus_1 = n - 1u32;
    if !(&n_minus_1 % &product).is_zero() {
        return Err(format!("{label}: the factored part does not divide n - 1"));
    }
    if *n >= &product * &product {
        return Err(format!(
            "{label}: the factored part is not above the square root of n"
        ));
    }
    let entry = index
        .get(n)
        .ok_or_else(|| format!("{label}: no verified entry"))?;
    if subjects != entry.factors {
        return Err(format!(
            "{label}: the subjects are not the verified entry's factors"
        ));
    }
    if let Some(factor) = factors.iter().find(|f| f.base != entry.root) {
        return Err(format!(
            "{label}: the base {} is not the verified root {}",
            factor.base, entry.root
        ));
    }
    factors
        .iter()
        .try_for_each(|factor| check_node(&factor.child, index))
}

/// The complete `example : Hex.Nat.Prime term := by exact Hex.Nat.prime_of_checkPrimeAt
/// (c := …) (by decide +kernel)` of the tree `tree`, in exactly the layout of
/// `docs/targets/hex.md`: each factor entry of a `.pock` node on its own line, two spaces deeper
/// than the line that opened the node (four for the input's node). The text ends in a newline.
fn render_example(tree: &HexCert, term: &str) -> String {
    let mut text = format!(
        "example : Hex.Nat.Prime {term} := by\n  exact Hex.Nat.prime_of_checkPrimeAt (c := "
    );
    write_node(&mut text, tree, 4);
    text.push_str(")\n    (by decide +kernel)\n");
    text
}

/// Appends `.small n`, or `.pock n [` with its factor entries indented by `indent` spaces and
/// the closing `]`, to `text`.
fn write_node(text: &mut String, node: &HexCert, indent: usize) {
    match node {
        HexCert::Small(n) => text.push_str(&format!(".small {n}")),
        HexCert::Pock { n, factors } => {
            text.push_str(&format!(".pock {n} ["));
            for (i, factor) in factors.iter().enumerate() {
                text.push_str(if i == 0 { "\n" } else { ",\n" });
                text.push_str(&format!("{:indent$}({}, {}, ", "", factor.base, factor.e));
                write_node(text, &factor.child, indent + 2);
                text.push(')');
            }
            text.push(']');
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::input::parse_input;

    fn big(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
    }

    /// The certificate of `n` from `(q, root, factors)` triples, the input first.
    fn cert(n: &str, entries: &[(&str, u64, &[u64])]) -> Certificate {
        Certificate {
            n: big(n),
            entries: entries
                .iter()
                .map(|&(q, root, factors)| Entry {
                    q: big(q),
                    root,
                    factors: factors.iter().map(|&r| BigUint::from(r)).collect(),
                })
                .collect(),
        }
    }

    fn pock(n: &str, factors: Vec<HexFactor>) -> HexCert {
        HexCert::Pock { n: big(n), factors }
    }

    fn factor(base: u64, e: u32, child: HexCert) -> HexFactor {
        HexFactor { base, e, child }
    }

    /// `1000003 - 1 = 2 · 3 · 166667` and `166667 - 1 = 2 · 167 · 499`.
    fn cert_1000003() -> Certificate {
        cert(
            "1000003",
            &[
                ("1000003", 2, &[2, 3, 166667]),
                ("166667", 2, &[2, 167, 499]),
            ],
        )
    }

    fn tree_1000003() -> HexCert {
        pock(
            "1000003",
            vec![
                factor(2, 0, HexCert::Small(2)),
                factor(2, 0, HexCert::Small(3)),
                factor(
                    2,
                    0,
                    pock(
                        "166667",
                        vec![
                            factor(2, 0, HexCert::Small(2)),
                            factor(2, 0, HexCert::Small(167)),
                            factor(2, 0, HexCert::Small(499)),
                        ],
                    ),
                ),
            ],
        )
    }

    /// `483869221641199 - 1 = 2 · 3^2 · 4200127 · 6400193`, and `100003` divides both
    /// `4200127 - 1 = 2 · 3 · 7 · 100003` and `6400193 - 1 = 2^6 · 100003`.
    fn cert_twice() -> Certificate {
        cert(
            "483869221641199",
            &[
                ("483869221641199", 3, &[2, 3, 4200127, 6400193]),
                ("6400193", 3, &[2, 100003]),
                ("4200127", 3, &[2, 3, 7, 100003]),
                ("100003", 2, &[2, 3, 7, 2381]),
                ("2381", 3, &[2, 5, 7, 17]),
            ],
        )
    }

    /// Applies `edit` to the first `.pock` node of `tree` about `n` (depth first).
    fn edit_node(tree: &mut HexCert, n: &str, edit: &dyn Fn(&mut Vec<HexFactor>)) -> bool {
        match tree {
            HexCert::Small(_) => false,
            HexCert::Pock { n: m, factors } => {
                if *m == big(n) {
                    edit(factors);
                    return true;
                }
                factors.iter_mut().any(|f| edit_node(&mut f.child, n, edit))
            }
        }
    }

    #[test]
    fn builds_a_two_level_tree() {
        let cert = cert_1000003();
        let tree = HexCert::from_certificate(&cert).unwrap();
        assert_eq!(tree, tree_1000003());
        assert_eq!(check(&tree, &cert), Ok(()));
    }

    #[test]
    fn a_prime_below_the_table_bound_is_small() {
        // `1033` has an entry, since it is at least 1024, but Hex's table covers it.
        let cert = cert("1033", &[("1033", 5, &[2, 3, 43])]);
        let tree = HexCert::from_certificate(&cert).unwrap();
        assert_eq!(tree, HexCert::Small(1033));
        assert_eq!(check(&tree, &cert), Ok(()));
        let cert = Certificate {
            n: big("97"),
            entries: vec![],
        };
        assert_eq!(HexCert::from_certificate(&cert), Ok(HexCert::Small(97)));
    }

    #[test]
    fn exponents_are_the_multiplicities_less_one() {
        // `17007377 - 1 = 2^4 · 1031^2`.
        let cert = cert(
            "17007377",
            &[("17007377", 3, &[2, 1031]), ("1031", 14, &[2, 5, 103])],
        );
        let tree = HexCert::from_certificate(&cert).unwrap();
        assert_eq!(
            tree,
            pock(
                "17007377",
                vec![
                    factor(3, 3, HexCert::Small(2)),
                    factor(3, 1, HexCert::Small(1031))
                ]
            )
        );
        assert_eq!(check(&tree, &cert), Ok(()));
    }

    #[test]
    fn a_prime_met_twice_is_written_out_twice() {
        let cert = cert_twice();
        let tree = HexCert::from_certificate(&cert).unwrap();
        let node_100003 = pock(
            "100003",
            vec![
                factor(2, 0, HexCert::Small(2)),
                factor(2, 0, HexCert::Small(3)),
                factor(2, 0, HexCert::Small(7)),
                factor(2, 0, HexCert::Small(2381)),
            ],
        );
        let expected = pock(
            "483869221641199",
            vec![
                factor(3, 0, HexCert::Small(2)),
                factor(3, 1, HexCert::Small(3)),
                factor(
                    3,
                    0,
                    pock(
                        "4200127",
                        vec![
                            factor(3, 0, HexCert::Small(2)),
                            factor(3, 0, HexCert::Small(3)),
                            factor(3, 0, HexCert::Small(7)),
                            factor(3, 0, node_100003.clone()),
                        ],
                    ),
                ),
                factor(
                    3,
                    0,
                    pock(
                        "6400193",
                        vec![factor(3, 5, HexCert::Small(2)), factor(3, 0, node_100003)],
                    ),
                ),
            ],
        );
        assert_eq!(tree, expected);
        assert_eq!(check(&tree, &cert), Ok(()));
    }

    #[test]
    fn a_missing_entry_is_an_error() {
        // With a witness bound above 166667 that prime needs no Lucas entry, but Hex's table
        // stops at 100000, so the Hex tree needs one.
        let mut cert = cert_1000003();
        cert.entries.pop();
        assert_eq!(
            HexCert::from_certificate(&cert),
            Err("166667 is at least 100000 and has no entry".to_string())
        );
        assert_eq!(
            TARGET.output(&cert, &parse_input("1000003", 2000).unwrap()),
            Err("the HexPrime target: 166667 is at least 100000 and has no entry".to_string())
        );
    }

    /// The error of `check` on the tree of `1000003` after `edit` changed its node `n`.
    fn rejection(n: &str, edit: &dyn Fn(&mut Vec<HexFactor>)) -> String {
        let mut tree = tree_1000003();
        assert!(edit_node(&mut tree, n, edit));
        check(&tree, &cert_1000003()).unwrap_err()
    }

    #[test]
    fn check_rejects_bad_leaves() {
        assert_eq!(
            check(&HexCert::Small(169), &cert("169", &[])),
            Err(".small 169: not a prime below 100000".to_string())
        );
        // `100003` is prime but not below the bound.
        assert_eq!(
            check(&HexCert::Small(100_003), &cert("100003", &[])),
            Err(".small 100003: not a prime below 100000".to_string())
        );
    }

    #[test]
    fn check_rejects_bad_structure() {
        assert_eq!(
            rejection("166667", &|factors| factors.swap(1, 2)),
            ".pock 166667: the subject 167 is not above 499"
        );
        assert_eq!(
            rejection("166667", &|factors| factors[2].child = HexCert::Small(167)),
            ".pock 166667: the subject 167 is not above 167"
        );
        assert_eq!(
            rejection("166667", &|factors| factors[0].e = 1),
            ".pock 166667: the factored part does not divide n - 1"
        );
        // Without the factor 166667, `F = 6` is far below the square root of 1000003.
        assert_eq!(
            rejection("1000003", &|factors| {
                factors.pop();
            }),
            ".pock 1000003: the factored part is not above the square root of n"
        );
        assert_eq!(
            check(&pock("1000004", vec![]), &cert("1000004", &[])),
            Err(".pock 1000004: n is not odd and at least 2".to_string())
        );
    }

    #[test]
    fn check_ties_every_node_to_its_verified_entry() {
        assert_eq!(
            rejection("166667", &|factors| factors[1].base = 3),
            ".pock 166667: the base 3 is not the verified root 2"
        );
        // `F = 2 · 499` passes Hex's own conditions, but the subjects are not the entry's.
        assert_eq!(
            rejection("166667", &|factors| {
                factors.remove(1);
            }),
            ".pock 166667: the subjects are not the verified entry's factors"
        );
        let mut short = cert_1000003();
        short.entries.pop();
        assert_eq!(
            check(&tree_1000003(), &short),
            Err(".pock 166667: no verified entry".to_string())
        );
        let other = cert("1000033", &[]);
        assert_eq!(
            check(&tree_1000003(), &other),
            Err("the tree is about 1000003, not about n = 1000033".to_string())
        );
    }

    #[test]
    fn renders_a_small_certificate() {
        assert_eq!(
            render_example(&HexCert::Small(997), "997"),
            "example : Hex.Nat.Prime 997 := by\n  \
             exact Hex.Nat.prime_of_checkPrimeAt (c := .small 997)\n    (by decide +kernel)\n"
        );
        assert_eq!(
            render_example(&HexCert::Small(65537), "(2 ^ 16 + 1)"),
            "example : Hex.Nat.Prime (2 ^ 16 + 1) := by\n  \
             exact Hex.Nat.prime_of_checkPrimeAt (c := .small 65537)\n    (by decide +kernel)\n"
        );
    }

    #[test]
    fn renders_a_two_level_certificate() {
        let expected = "example : Hex.Nat.Prime 1000003 := by\n\
                        \x20 exact Hex.Nat.prime_of_checkPrimeAt (c := .pock 1000003 [\n\
                        \x20   (2, 0, .small 2),\n\
                        \x20   (2, 0, .small 3),\n\
                        \x20   (2, 0, .pock 166667 [\n\
                        \x20     (2, 0, .small 2),\n\
                        \x20     (2, 0, .small 167),\n\
                        \x20     (2, 0, .small 499)])])\n\
                        \x20   (by decide +kernel)\n";
        assert_eq!(render_example(&tree_1000003(), "1000003"), expected);
    }

    #[test]
    fn renders_exponents_and_a_repeated_subtree_twice() {
        let shared = pock("100003", vec![factor(2, 0, HexCert::Small(2))]);
        let tree = pock(
            "483869221641199",
            vec![
                factor(3, 1, HexCert::Small(3)),
                factor(3, 0, shared.clone()),
                factor(3, 5, shared),
            ],
        );
        let expected = "example : Hex.Nat.Prime 483869221641199 := by\n\
                        \x20 exact Hex.Nat.prime_of_checkPrimeAt (c := .pock 483869221641199 [\n\
                        \x20   (3, 1, .small 3),\n\
                        \x20   (3, 0, .pock 100003 [\n\
                        \x20     (2, 0, .small 2)]),\n\
                        \x20   (3, 5, .pock 100003 [\n\
                        \x20     (2, 0, .small 2)])])\n\
                        \x20   (by decide +kernel)\n";
        assert_eq!(render_example(&tree, "483869221641199"), expected);
    }

    #[test]
    fn renders_the_checked_tree_with_its_import() {
        let (imports, text) =
            render(&cert_1000003(), &parse_input("10^6 + 3", 2000).unwrap()).unwrap();
        assert_eq!(imports, ["HexPrimality"]);
        assert_eq!(text, render_example(&tree_1000003(), "(10 ^ 6 + 3)"));
    }
}
