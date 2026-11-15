//! The hints text: its parsing, and its rendering from the primes of a tree.

use std::collections::{BTreeMap, BTreeSet};

use crate::arith::{self, parse_decimal, BigUint};

/// The largest integer a JavaScript number holds exactly. The page passes tasks through JSON
/// numbers, which would round a larger root.
const MAX_EXACT_JS_INTEGER: u64 = (1 << 53) - 1;

/// The hints parsed from the hints text.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Hints {
    /// The factor hints, each at least 2.
    pub(crate) factors: BTreeSet<BigUint>,
    /// The root hints, a residue in `2..=MAX_EXACT_JS_INTEGER` modulo each prime they name.
    pub(crate) roots: BTreeMap<BigUint, u64>,
}

/// Parses the hints text. A token is a maximal run of ASCII digits and colons, and anything else
/// separates tokens (so `3^2` yields 3 and 2). A token `q` is a factor hint, and `q:a` adds the
/// root hint `a mod q` for `q`. Tokens of other shapes (`:5`, `7:`, `1:2:3`) are ignored. A factor
/// below 2 is dropped with its root, and a root alone when its residue is below 2 or above
/// `MAX_EXACT_JS_INTEGER`. Duplicates are removed, and the first root for a prime wins.
pub fn parse_hints(text: &str) -> Hints {
    let two = BigUint::from(2u32);
    let mut hints = Hints::default();
    for token in text.split(|c: char| !c.is_ascii_digit() && c != ':') {
        let (factor, root) = match token.split_once(':') {
            None => (parse_decimal(token), None),
            Some((q, a)) => match (parse_decimal(q), parse_decimal(a)) {
                (Some(q), Some(a)) => (Some(q), Some(a)),
                _ => (None, None),
            },
        };
        let Some(factor) = factor.filter(|q| *q >= two) else {
            continue;
        };
        if let Some(root) = root
            .and_then(|a| arith::to_u64(&(a % &factor)))
            .filter(|a| (2..=MAX_EXACT_JS_INTEGER).contains(a))
        {
            hints.roots.entry(factor.clone()).or_insert(root);
        }
        hints.factors.insert(factor);
    }
    hints
}

/// The hints text of the tree primes `primes`, one line `q:root` (or `q` without a root) per
/// prime in the given order. An interrupted run's factors paste back as hints with their roots.
pub fn render_hints<'a>(primes: impl IntoIterator<Item = (&'a BigUint, Option<u64>)>) -> String {
    let mut text = String::new();
    for (prime, root) in primes {
        text.push_str(&prime.to_str_radix(10));
        if let Some(root) = root {
            text.push_str(&format!(":{root}"));
        }
        text.push('\n');
    }
    text
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bigs(values: &[u64]) -> BTreeSet<BigUint> {
        values.iter().map(|&v| BigUint::from(v)).collect()
    }

    fn roots(pairs: &[(u64, u64)]) -> BTreeMap<BigUint, u64> {
        pairs.iter().map(|&(q, a)| (BigUint::from(q), a)).collect()
    }

    #[test]
    fn digit_runs_become_sorted_distinct_factor_hints() {
        let parsed = parse_hints("2, 3 * 5\n7^2 · 11; 1 0 3");
        assert_eq!(parsed.factors, bigs(&[2, 3, 5, 7, 11]));
        assert!(parsed.roots.is_empty());
        assert_eq!(parse_hints(""), Hints::default());
        assert_eq!(parse_hints("abc · , ^"), Hints::default());
        assert_eq!(parse_hints("0 1 00 01"), Hints::default());
        assert_eq!(parse_hints("0002\t2\r\n002").factors, bigs(&[2]));
        assert_eq!(parse_hints("11x7y11").factors, bigs(&[7, 11]));
    }

    #[test]
    fn a_colon_token_yields_a_factor_and_its_root() {
        let parsed = parse_hints("77158673929:11, 649657:5\n7 2");
        assert_eq!(parsed.factors, bigs(&[2, 7, 649657, 77158673929]));
        assert_eq!(parsed.roots, roots(&[(649657, 5), (77158673929, 11)]));
        // Tokens of a bad shape are ignored like other junk; `x:3` is the token `:3`.
        let parsed = parse_hints(":5 7: 1:2:3 x:3 5:7:");
        assert_eq!(parsed, Hints::default());
        // A factor below 2 goes with its root; a root whose residue is below 2 goes alone.
        let parsed = parse_hints("1:9 0:3 13:1 17:0 19:20 23:46");
        assert_eq!(parsed.factors, bigs(&[13, 17, 19, 23]));
        assert!(parsed.roots.is_empty());
    }

    #[test]
    fn a_root_is_reduced_and_kept_only_below_2_to_the_53() {
        // 65542 is 5 modulo 65537, and 65539 · (2^64 − 1) + 7 is 7 modulo 65539.
        let huge = BigUint::from(65539u32) * BigUint::from(u64::MAX) + 7u32;
        let parsed = parse_hints(&format!("65537:65542 65539:{huge}"));
        assert_eq!(parsed.roots, roots(&[(65537, 5), (65539, 7)]));
        // 43^11 is a primitive root of 2^127 − 1 above 2^53, which the page could not carry.
        let parsed = parse_hints("170141183460469231731687303715884105727:929293739471222707");
        assert!(parsed.roots.is_empty());
    }

    #[test]
    fn duplicates_are_removed_and_the_first_root_wins() {
        let parsed = parse_hints("7:3 7 7:5 3 3:2");
        assert_eq!(parsed.factors, bigs(&[3, 7]));
        assert_eq!(parsed.roots, roots(&[(3, 2), (7, 3)]));
        // A bare token before the colon token does not block the root.
        let parsed = parse_hints("7 7:5");
        assert_eq!(parsed.roots, roots(&[(7, 5)]));
    }
}
