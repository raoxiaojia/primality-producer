//! Independent certificate checker, using only the certificate and `arith`.

use std::collections::BTreeMap;

use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};

use crate::arith::{is_small_prime, lucas_powers, to_u64, BigUint};

/// The largest witness bound `verify` accepts. The tactic proves primes below `2^10` by
/// `norm_num` and looks every larger prime up in the certificate.
pub const MAX_WITNESS_BOUND: u64 = 1 << 10;

/// Fails when `witness_bound` exceeds `MAX_WITNESS_BOUND`.
pub fn check_witness_bound(witness_bound: u64) -> Result<(), String> {
    if witness_bound > MAX_WITNESS_BOUND {
        return Err(format!(
            "witness_bound is {witness_bound}, above the ceiling {MAX_WITNESS_BOUND}: the tactic \
             proves primes below 2^10 itself and needs an entry for every larger prime"
        ));
    }
    Ok(())
}

/// One Lucas witness. In JSON, `q` and `factors` are decimal strings.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Entry {
    /// The prime this entry certifies.
    #[serde(with = "crate::arith::big_str")]
    pub q: BigUint,
    /// A primitive root modulo `q`.
    pub root: u64,
    /// The distinct prime factors of `q − 1`, ascending.
    #[serde(with = "crate::arith::big_str_vec")]
    pub factors: Vec<BigUint>,
}

/// A Lucas certificate that `n` is prime.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Certificate {
    /// The number certified.
    #[serde(with = "crate::arith::big_str")]
    pub n: BigUint,
    /// The entries, input first, then descending.
    pub entries: Vec<Entry>,
}

/// Checks that `cert` proves `n` prime. A `witness_bound` above `MAX_WITNESS_BOUND` is refused.
/// 1. `n ≥ 2`. If `n < witness_bound`, `entries` is empty and `n` is prime by trial division.
///    Else `entries[0].q == n` and the `q`s are strictly descending (so distinct).
/// 2. Each entry has `q ≥ witness_bound` and a nonempty, strictly ascending list of factors, each
///    at least 2. Each factor `r` is prime by trial division when `r < witness_bound`, and else
///    has an entry. Dividing every factor's maximal power out of `q − 1` leaves exactly 1. The
///    root satisfies `2 ≤ root < q`, `root^(q−1) ≡ 1 (mod q)` and `root^((q−1)/r) ≢ 1 (mod q)`
///    for every factor `r`.
/// 3. Every entry is reachable from `n` through factor lists.
///
/// By Lucas's theorem and induction, every `q` and `n` are then prime. The error names the entry
/// (its position and `q`) and the failed check.
pub fn verify(cert: &Certificate, witness_bound: u64) -> Result<(), String> {
    check_witness_bound(witness_bound)?;
    let n = &cert.n;
    let bound = BigUint::from(witness_bound);

    // 1. The shape of the certificate.
    if *n < BigUint::from(2u32) {
        return Err(format!("n = {n} is below 2"));
    }
    if *n < bound {
        if !cert.entries.is_empty() {
            return Err(format!(
                "n = {n} is below the witness bound {witness_bound} but the certificate has \
                 entries ({})",
                cert.entries.len()
            ));
        }
        // `n < witness_bound` fits a `u64`.
        return match to_u64(n) {
            Some(x) if is_small_prime(x) => Ok(()),
            _ => Err(format!("n = {n} is not prime")),
        };
    }
    let first = cert
        .entries
        .first()
        .ok_or_else(|| format!("n = {n} has no entry"))?;
    if first.q != *n {
        return Err(format!(
            "the first entry is for q = {}, not for n = {n}",
            first.q
        ));
    }
    for (i, pair) in cert.entries.windows(2).enumerate() {
        if pair[1].q >= pair[0].q {
            return Err(format!(
                "entry {} (q = {}) is not below entry {i} (q = {})",
                i + 1,
                pair[1].q,
                pair[0].q
            ));
        }
    }
    // The `q`s are distinct, so the map identifies each entry.
    let index: BTreeMap<&BigUint, usize> = cert
        .entries
        .iter()
        .enumerate()
        .map(|(i, entry)| (&entry.q, i))
        .collect();

    // 2. Each entry on its own.
    for (i, entry) in cert.entries.iter().enumerate() {
        check_entry(i, entry, witness_bound, &index)?;
    }

    // 3. Reachability from `n`. Every factor at or above the bound has an entry, and no factor
    // below it does, since every `q` is at or above the bound.
    let mut reached = vec![false; cert.entries.len()];
    reached[0] = true;
    let mut stack = vec![0];
    while let Some(i) = stack.pop() {
        for r in &cert.entries[i].factors {
            if let Some(&j) = index.get(r) {
                if !reached[j] {
                    reached[j] = true;
                    stack.push(j);
                }
            }
        }
    }
    if let Some(i) = reached.iter().position(|&r| !r) {
        return Err(format!(
            "entry {i} (q = {}) is not reachable from n = {n}",
            cert.entries[i].q
        ));
    }
    Ok(())
}

/// Check 2 of `verify` for the entry at position `i`. `index` maps every `q` of the certificate
/// to its position.
fn check_entry(
    i: usize,
    entry: &Entry,
    witness_bound: u64,
    index: &BTreeMap<&BigUint, usize>,
) -> Result<(), String> {
    let q = &entry.q;
    let label = format!("entry {i} (q = {q})");
    if *q < BigUint::from(witness_bound) {
        return Err(format!(
            "{label}: q is below the witness bound {witness_bound}"
        ));
    }
    if entry.factors.is_empty() {
        return Err(format!("{label}: no factors"));
    }
    let q_minus_1 = q - 1u32;
    let mut rest = q_minus_1.clone();
    let mut preceding: Option<&BigUint> = None;
    for r in &entry.factors {
        if *r < BigUint::from(2u32) {
            return Err(format!("{label}: factor {r} is below 2"));
        }
        if let Some(p) = preceding {
            if r <= p {
                return Err(format!(
                    "{label}: factor {r} is not above the preceding factor {p}"
                ));
            }
        }
        preceding = Some(r);
        if *r < BigUint::from(witness_bound) {
            // `r < witness_bound` fits a `u64`.
            if !to_u64(r).is_some_and(is_small_prime) {
                return Err(format!("{label}: factor {r} is not prime"));
            }
        } else if !index.contains_key(r) {
            return Err(format!("{label}: factor {r} has no entry"));
        }
        if !(&rest % r).is_zero() {
            return Err(format!("{label}: factor {r} does not divide q - 1"));
        }
        while (&rest % r).is_zero() {
            rest /= r;
        }
    }
    if !rest.is_one() {
        return Err(format!(
            "{label}: dividing the factors out of q - 1 leaves {rest}"
        ));
    }
    let root = BigUint::from(entry.root);
    if entry.root < 2 || root >= *q {
        return Err(format!("{label}: root {} is not in 2..q", entry.root));
    }
    let (powers, full) = lucas_powers(&root, q, &entry.factors);
    if !full.is_one() {
        return Err(format!(
            "{label}: root {} ^ (q - 1) is not 1 mod q",
            entry.root
        ));
    }
    for (r, power) in entry.factors.iter().zip(&powers) {
        if power.is_one() {
            return Err(format!(
                "{label}: root {} ^ ((q - 1) / {r}) is 1 mod q",
                entry.root
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arith::{powmod, trial_division};

    const WITNESS_BOUND: u64 = 1000;

    /// `2^127 - 1`.
    const MERSENNE_127: &str = "170141183460469231731687303715884105727";

    /// The certificate of `2^127 - 1` as `(q, root, factors)`, the input first, then descending.
    /// `n - 1 = 2 · 3^3 · 7^2 · 19 · 43 · 73 · 127 · 337 · 5419 · 92737 · 649657 · 77158673929`.
    const MERSENNE_127_TREE: &[(&str, u64, &[u64])] = &[
        (
            MERSENNE_127,
            43,
            &[
                2,
                3,
                7,
                19,
                43,
                73,
                127,
                337,
                5419,
                92737,
                649657,
                77158673929,
            ],
        ),
        ("77158673929", 11, &[2, 3, 7, 73, 699053]),
        ("699053", 2, &[2, 174763]),
        ("649657", 5, &[2, 3, 7, 1289]),
        ("174763", 17, &[2, 3, 7, 19, 73]),
        ("92737", 5, &[2, 3, 7, 23]),
        ("5419", 3, &[2, 3, 7, 43]),
        ("1289", 6, &[2, 7, 23]),
    ];

    fn big(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
    }

    fn bigs(values: &[u64]) -> Vec<BigUint> {
        values.iter().map(|&v| BigUint::from(v)).collect()
    }

    fn entry(q: &str, root: u64, factors: &[u64]) -> Entry {
        Entry {
            q: big(q),
            root,
            factors: bigs(factors),
        }
    }

    /// The distinct prime factors of `m`, ascending. The cofactor left by trial division up to
    /// `2^16` must be prime, as it is for every `q - 1` below the root of the tree.
    fn prime_factors(m: &BigUint) -> Vec<BigUint> {
        let (pairs, rest) = trial_division(m, 1 << 16);
        let mut factors: Vec<BigUint> = pairs.iter().map(|&(p, _)| BigUint::from(p)).collect();
        if !rest.is_one() {
            let r = to_u64(&rest).expect("a cofactor below 2^64");
            assert!(is_small_prime(r), "the cofactor {rest} should be prime");
            factors.push(rest);
        }
        factors
    }

    /// The smallest primitive root modulo the prime `q`, given the prime factors of `q - 1`.
    fn smallest_primitive_root(q: &BigUint, factors: &[BigUint]) -> u64 {
        let q_minus_1 = q - 1u32;
        (2u64..)
            .find(|&a| {
                let a = BigUint::from(a);
                factors
                    .iter()
                    .all(|r| !powmod(&a, &(&q_minus_1 / r), q).is_one())
            })
            .expect("a primitive root")
    }

    /// The certificate of the prime `n`, whose `n - 1` has the prime factors `n_factors`, with an
    /// entry for every prime at or above `WITNESS_BOUND` in its tree.
    fn build(n: &BigUint, n_factors: Vec<BigUint>) -> Certificate {
        let bound = BigUint::from(WITNESS_BOUND);
        let mut entries: Vec<Entry> = Vec::new();
        let mut todo = vec![(n.clone(), n_factors)];
        while let Some((q, factors)) = todo.pop() {
            if q < bound || entries.iter().any(|e| e.q == q) {
                continue;
            }
            for r in &factors {
                if *r >= bound {
                    todo.push((r.clone(), prime_factors(&(r - 1u32))));
                }
            }
            let root = smallest_primitive_root(&q, &factors);
            entries.push(Entry { q, root, factors });
        }
        entries.sort_by(|a, b| a.q.cmp(&b.q));
        entries.reverse();
        Certificate {
            n: n.clone(),
            entries,
        }
    }

    /// The certificate of `2^127 - 1` built by `build`, checked against the pinned tree.
    fn mersenne_127() -> Certificate {
        let n = big(MERSENNE_127);
        let n_factors = bigs(MERSENNE_127_TREE[0].2);
        let product = n_factors.iter().fold(BigUint::one(), |acc, r| acc * r);
        assert!(((&n - 1u32) % product).is_zero());
        let cert = build(&n, n_factors);
        let pinned: Vec<Entry> = MERSENNE_127_TREE
            .iter()
            .map(|&(q, root, factors)| entry(q, root, factors))
            .collect();
        assert_eq!(cert.entries, pinned);
        cert
    }

    /// Asserts that `verify` rejects `cert` with a message mentioning `detail`.
    fn rejects(cert: &Certificate, detail: &str) {
        let err = verify(cert, WITNESS_BOUND).expect_err("the certificate should be rejected");
        assert!(err.contains(detail), "{err:?} should mention {detail:?}");
    }

    #[test]
    fn accepts_the_certificate_of_2_127_minus_1() {
        assert_eq!(verify(&mersenne_127(), WITNESS_BOUND), Ok(()));
    }

    #[test]
    fn rejects_a_wrong_root() {
        // 4 is a square, so `4^((q - 1) / 2) = 2^(q - 1) ≡ 1`.
        let mut cert = mersenne_127();
        cert.entries[0].root = 4;
        rejects(&cert, "entry 0 (q = 1701411834604692317316873037158841057");
        rejects(&cert, "root 4 ^ ((q - 1) / 2) is 1 mod q");
        let mut cert = mersenne_127();
        cert.entries[7].root = 1;
        rejects(&cert, "entry 7 (q = 1289): root 1 is not in 2..q");
        let mut cert = mersenne_127();
        cert.entries[7].root = 1289;
        rejects(&cert, "entry 7 (q = 1289): root 1289 is not in 2..q");
    }

    #[test]
    fn rejects_a_composite_q_by_fermat() {
        // 1001 = 7 · 11 · 13 with 1000 = 2^3 · 5^3, and 2^1000 ≢ 1 (mod 1001).
        let cert = Certificate {
            n: big("1001"),
            entries: vec![entry("1001", 2, &[2, 5])],
        };
        rejects(&cert, "entry 0 (q = 1001): root 2 ^ (q - 1) is not 1 mod q");
    }

    #[test]
    fn rejects_a_missing_factor() {
        let mut cert = mersenne_127();
        cert.entries[0].factors.remove(3); // 19
        rejects(&cert, "entry 0 (q = ");
        rejects(&cert, ": dividing the factors out of q - 1 leaves 19");
    }

    #[test]
    fn rejects_an_extra_factor() {
        let mut cert = mersenne_127();
        cert.entries[0].factors.insert(2, BigUint::from(5u32));
        rejects(&cert, ": factor 5 does not divide q - 1");
    }

    #[test]
    fn rejects_a_factor_out_of_order() {
        let mut cert = mersenne_127();
        cert.entries[0].factors.swap(3, 4); // 19 and 43
        rejects(&cert, ": factor 19 is not above the preceding factor 43");
        let mut cert = mersenne_127();
        cert.entries[7].factors[1] = BigUint::from(2u32); // 2, 2, 23
        rejects(
            &cert,
            "entry 7 (q = 1289): factor 2 is not above the preceding factor 2",
        );
    }

    #[test]
    fn rejects_a_missing_entry() {
        let mut cert = mersenne_127();
        cert.entries.remove(6); // 5419
        rejects(&cert, ": factor 5419 has no entry");
    }

    #[test]
    fn rejects_a_stray_entry() {
        // A correct witness for a prime outside the tree, in its place in the descending order.
        let mut cert = mersenne_127();
        cert.entries.insert(6, entry("65537", 3, &[2]));
        rejects(&cert, "entry 6 (q = 65537) is not reachable from n = ");
    }

    #[test]
    fn rejects_a_composite_factor_below_the_bound() {
        let mut cert = mersenne_127();
        cert.entries[0].factors[7] = BigUint::from(999u32); // 27 · 37 in place of 337
        rejects(&cert, ": factor 999 is not prime");
    }

    #[test]
    fn rejects_bad_factor_lists() {
        let mut cert = mersenne_127();
        cert.entries[7].factors.clear();
        rejects(&cert, "entry 7 (q = 1289): no factors");
        let mut cert = mersenne_127();
        cert.entries[7].factors[0] = BigUint::from(1u32);
        rejects(&cert, "entry 7 (q = 1289): factor 1 is below 2");
    }

    #[test]
    fn rejects_n_with_no_entry() {
        let cert = Certificate {
            n: big(MERSENNE_127),
            entries: vec![],
        };
        rejects(
            &cert,
            "n = 170141183460469231731687303715884105727 has no entry",
        );
    }

    #[test]
    fn rejects_n_below_2() {
        for n in ["0", "1"] {
            let cert = Certificate {
                n: big(n),
                entries: vec![],
            };
            rejects(&cert, &format!("n = {n} is below 2"));
        }
    }

    #[test]
    fn rejects_a_misplaced_first_entry_and_a_wrong_order() {
        let mut cert = mersenne_127();
        cert.entries.remove(0);
        rejects(
            &cert,
            "the first entry is for q = 77158673929, not for n = 170141183460469231731687303715884105727",
        );
        let mut cert = mersenne_127();
        cert.entries.swap(1, 2);
        rejects(
            &cert,
            "entry 2 (q = 77158673929) is not below entry 1 (q = 699053)",
        );
        let mut cert = mersenne_127();
        cert.entries.insert(2, cert.entries[1].clone());
        rejects(
            &cert,
            "entry 2 (q = 77158673929) is not below entry 1 (q = 77158673929)",
        );
    }

    #[test]
    fn rejects_an_entry_below_the_bound() {
        let cert = Certificate {
            n: big("65537"),
            entries: vec![entry("65537", 3, &[2]), entry("257", 3, &[2])],
        };
        rejects(
            &cert,
            "entry 1 (q = 257): q is below the witness bound 1000",
        );
    }

    #[test]
    fn small_n_needs_no_entries() {
        let cert = Certificate {
            n: big("997"),
            entries: vec![],
        };
        assert_eq!(verify(&cert, WITNESS_BOUND), Ok(()));
        let cert = Certificate {
            n: big("997"),
            entries: vec![entry("65537", 3, &[2])],
        };
        rejects(
            &cert,
            "n = 997 is below the witness bound 1000 but the certificate has entries (1)",
        );
        let cert = Certificate {
            n: big("999"),
            entries: vec![],
        };
        rejects(&cert, "n = 999 is not prime");
        let cert = Certificate {
            n: big("2"),
            entries: vec![],
        };
        assert_eq!(verify(&cert, WITNESS_BOUND), Ok(()));
    }

    #[test]
    fn certificates_round_trip_through_json_as_decimal_strings() {
        let cert = Certificate {
            n: big("649657"),
            entries: vec![
                entry("649657", 5, &[2, 3, 7, 1289]),
                entry("1289", 6, &[2, 7, 23]),
            ],
        };
        let json = serde_json::to_string(&cert).unwrap();
        assert_eq!(
            json,
            r#"{"n":"649657","entries":[{"q":"649657","root":5,"factors":["2","3","7","1289"]},{"q":"1289","root":6,"factors":["2","7","23"]}]}"#
        );
        assert_eq!(serde_json::from_str::<Certificate>(&json).unwrap(), cert);
        let cert = mersenne_127();
        let json = serde_json::to_string(&cert).unwrap();
        assert!(json.contains(r#""q":"170141183460469231731687303715884105727""#));
        assert_eq!(serde_json::from_str::<Certificate>(&json).unwrap(), cert);
        assert!(serde_json::from_str::<Certificate>(r#"{"n":649657,"entries":[]}"#).is_err());
    }

    #[test]
    fn the_bound_is_a_parameter_up_to_2_10() {
        // 2027 - 1 = 2 · 1013, so at the bound 2^10 the entry of 2027 suffices.
        let cert = Certificate {
            n: big("2027"),
            entries: vec![entry("2027", 2, &[2, 1013])],
        };
        assert_eq!(verify(&cert, MAX_WITNESS_BOUND), Ok(()));
        rejects(&cert, ": factor 1013 has no entry");
        // At 2^16 this certificate would pass, while the tactic needs the entries it lacks.
        let mut cert = mersenne_127();
        cert.entries.retain(|e| e.q >= BigUint::from(1u32 << 16));
        assert!(verify(&cert, 1 << 16)
            .is_err_and(|e| e.starts_with("witness_bound is 65536, above the ceiling 1024")));
    }
}
