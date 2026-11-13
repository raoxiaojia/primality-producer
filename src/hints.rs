//! The hints text: its parsing, and its rendering from the primes of a tree.

use std::collections::{BTreeMap, BTreeSet};

use crate::arith::{parse_decimal, BigUint};

/// The hints parsed from the hints text.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Hints {
    /// The factor hints, ascending and distinct, each at least 2.
    pub factors: Vec<BigUint>,
    /// The root hints, a primitive root (at least 2) for each prime they name.
    pub roots: BTreeMap<BigUint, BigUint>,
}

/// Parses the hints text. A token is a maximal run of ASCII digits and colons, and anything else
/// separates tokens (so `3^2` yields 3 and 2). A token `q` is a factor hint, and `q:a` adds the
/// root hint `a` for `q`. Tokens of other shapes (`:5`, `7:`, `1:2:3`) are ignored. A factor
/// below 2 is dropped with its root, and a root below 2 alone. Duplicates are removed, and the
/// first root for a prime wins.
pub fn parse_hints(text: &str) -> Hints {
    let two = BigUint::from(2u32);
    let mut factors = BTreeSet::new();
    let mut roots = BTreeMap::new();
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
        if let Some(root) = root.filter(|a| *a >= two) {
            roots.entry(factor.clone()).or_insert(root);
        }
        factors.insert(factor);
    }
    Hints {
        factors: factors.into_iter().collect(),
        roots,
    }
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

    fn bigs(values: &[u64]) -> Vec<BigUint> {
        values.iter().map(|&v| BigUint::from(v)).collect()
    }

    fn roots(pairs: &[(u64, u64)]) -> BTreeMap<BigUint, BigUint> {
        pairs
            .iter()
            .map(|&(q, a)| (BigUint::from(q), BigUint::from(a)))
            .collect()
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
        // A factor below 2 goes with its root; a root below 2 goes alone.
        let parsed = parse_hints("1:9 0:3 13:1 17:0");
        assert_eq!(parsed.factors, bigs(&[13, 17]));
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

    #[test]
    fn large_values_and_the_order_of_magnitude() {
        let parsed =
            parse_hints("18446744073709551616 9 18446744073709551615:18446744073709551617");
        let expected = vec![
            BigUint::from(9u32),
            BigUint::from(u64::MAX),
            BigUint::from(u64::MAX) + 1u32,
        ];
        assert_eq!(parsed.factors, expected);
        assert_eq!(
            parsed.roots.get(&BigUint::from(u64::MAX)),
            Some(&(BigUint::from(u64::MAX) + 2u32))
        );
    }

    #[test]
    fn renders_hints_one_per_line_with_the_known_roots() {
        assert_eq!(render_hints([]), "");
        let (q1, q2) = (BigUint::from(5419u32), BigUint::from(77158673929u64));
        assert_eq!(
            render_hints([(&q1, Some(3)), (&q2, None)]),
            "5419:3\n77158673929\n"
        );
    }
}
