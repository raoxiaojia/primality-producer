//! The HexPrime target end to end: its text from the driver's certificate of `2^127 - 1`.

use primality_producer::hints::parse_hints;
use primality_producer::{Config, Driver};

#[test]
fn certifies_2_127_minus_1() {
    let config = Config {
        max_ecm_levels: Some(2),
        ..Config::default()
    };
    let snap = Driver::new(
        "170141183460469231731687303715884105727",
        parse_hints(""),
        config,
    )
    .expect("a valid input")
    .run_to_completion();
    assert_eq!(snap.status, "certified", "{}", snap.message);
    let hex = snap
        .outputs
        .iter()
        .find(|output| output.target == "hexprime")
        .map(|output| output.code.as_str())
        .expect("the HexPrime file");
    // `n - 1 = 2 · 3^3 · 7^2 · …`, so Hex's off-by-one exponents start 0, 2, 1. Five primes of
    // the tree are at least 100000: the input, 649657, 77158673929, 699053 and 174763.
    assert!(
        hex.starts_with(
            "import HexPrimality\n\n\
             example : Hex.Nat.Prime 170141183460469231731687303715884105727 := by\n  exact \
             Hex.Nat.prime_of_checkPrimeAt (c := .pock 170141183460469231731687303715884105727 \
             [\n    (43, 0, .small 2),\n    (43, 2, .small 3),\n    (43, 1, .small 7),\n"
        ),
        "{hex}"
    );
    assert!(hex.ends_with("])\n    (by decide +kernel)\n"), "{hex}");
    assert_eq!(hex.matches(".pock ").count(), 5, "{hex}");
}
