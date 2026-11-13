//! End-to-end runs of the driver with the real `run_task`, and of the CLI against the library.

use std::process::Command;

use primality_producer::arith::miller_rabin;
use primality_producer::hints::parse_hints;
use primality_producer::{BigUint, Config, Driver, Snapshot, TARGETS};

/// `2^127 - 1`.
const M127: &str = "170141183460469231731687303715884105727";

/// `2 · 5^5 · 100000007 · 998244353 · 999999937 + 1`, a 30-digit prime whose `p - 1` has three
/// 9-digit prime factors, so that its tree needs trial division and Pollard rho only.
const P30: &str = "623902724992316292964002043751";

fn big(s: &str) -> BigUint {
    BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
}

/// Two ECM levels at most, so a wrong tree fails within minutes instead of hours.
fn two_levels() -> Config {
    Config {
        max_ecm_levels: Some(2),
        ..Config::default()
    }
}

fn run(n: &str, hints: &str, config: Config) -> Snapshot {
    Driver::new(n, parse_hints(hints), config)
        .expect("a valid input")
        .run_to_completion()
}

/// The Lean file of the target named `target` in the certified snapshot `snap`.
fn code(snap: &Snapshot, target: &str) -> String {
    snap.outputs
        .iter()
        .find(|output| output.target == target)
        .map(|output| output.code.clone())
        .expect("the Lean file")
}

#[test]
fn certifies_2_127_minus_1() {
    let snap = run(M127, "", two_levels());
    assert_eq!(snap.status, "certified", "{}", snap.message);
    let targets: Vec<&str> = snap.outputs.iter().map(|o| o.target.as_str()).collect();
    let names: Vec<&str> = TARGETS.iter().map(|target| target.name).collect();
    assert_eq!(targets, names);
    let output = code(&snap, "mathlib");
    // The first two entries are those of the input and of 77158673929.
    assert!(
        output.starts_with(
            "import Mathlib.Tactic.Primality\n\n\
             example : Nat.Prime 170141183460469231731687303715884105727 := by\n  primality \
             (cert := .witnesses [\n    .lucas { root := 43, primeFactors := \
             [2, 3, 7, 19, 43, 73, 127, 337, 5419, 92737, 649657, 77158673929] },\n    \
             .lucas { root := 11, primeFactors := [2, 3, 7, 73, 699053] },\n"
        ),
        "{output}"
    );
    assert!(output.ends_with(" }])\n"), "{output}");
    assert_eq!(output.matches("\n    .lucas { root := ").count(), 8);
    assert_eq!(snap.primes.len(), 8);
    assert_eq!(snap.primes[1].value, "77158673929");
    assert!(snap.primes.iter().all(|p| p.state == "done"));
    assert_eq!(snap.open_composites, 0);
    assert_eq!(snap.tasks_in_flight, 0);
}

#[test]
fn certifies_a_30_digit_prime() {
    assert!(miller_rabin(&big(P30)).is_ok());
    let snap = run(P30, "", two_levels());
    assert_eq!(snap.status, "certified", "{}", snap.message);
    let output = code(&snap, "mathlib");
    assert!(
        output.starts_with(
            "import Mathlib.Tactic.Primality\n\nexample : Nat.Prime 623902724992316292964002043751 := by"
        ),
        "{output}"
    );
    // One entry per prime of the tree, the input's first.
    assert_eq!(
        output.matches("\n    .lucas { root := ").count(),
        snap.primes.len()
    );
    assert!(
        output.contains(
            "\n    .lucas { root := 11, primeFactors := [2, 5, 100000007, 998244353, 999999937] },\n"
        ),
        "{output}"
    );
    let values: Vec<&str> = snap.primes.iter().map(|p| p.value.as_str()).collect();
    for q in ["100000007", "998244353", "999999937"] {
        assert!(values.contains(&q), "{q} in {values:?}");
    }
    assert_eq!(
        snap.primes[0].factors,
        ["2", "5", "100000007", "998244353", "999999937"]
    );
    assert!(snap.hints_used.is_empty() && snap.hints_unused.is_empty());
}

#[test]
fn composite_inputs_are_reported() {
    let snap = run("1000001", "", Config::default());
    assert_eq!(snap.status, "composite");
    assert_eq!(snap.message, "1000001 = 101 × 9901");
    assert!(snap.outputs.is_empty());
    // 3215031751 = 151 · 751 · 28351 is a strong pseudoprime to the bases 2, 3, 5 and 7. Trial
    // division to 100 leaves it whole, so Miller–Rabin reports it with its first witness.
    let small_trial = Config {
        trial_bound: 100,
        ..Config::default()
    };
    let snap = run("3215031751", "", small_trial);
    assert_eq!(snap.status, "composite");
    assert_eq!(
        snap.message,
        "Miller–Rabin base 11 shows 3215031751 is composite"
    );
    // With the default trial bound its smallest factor is found first.
    let snap = run("3215031751", "", Config::default());
    assert_eq!(snap.status, "composite");
    assert_eq!(snap.message, "3215031751 = 151 × 21291601");
    let snap = run("1", "", Config::default());
    assert_eq!(snap.status, "composite");
    assert_eq!(snap.message, "1 is not prime");
}

#[test]
fn a_hint_is_used_and_the_certificate_is_the_same() {
    let plain = run(M127, "", two_levels());
    let hinted = run(M127, "77158673929", two_levels());
    assert_eq!(hinted.status, "certified", "{}", hinted.message);
    assert_eq!(hinted.hints_used, ["77158673929"]);
    assert!(hinted.hints_unused.is_empty());
    assert_eq!(hinted.outputs, plain.outputs);
    let unused = run(M127, "65537", two_levels());
    assert_eq!(unused.status, "certified");
    assert!(unused.hints_used.is_empty());
    assert_eq!(unused.hints_unused, ["65537"]);
    // The complete factorization of `n - 1` as hints. The largest prime is reached as a whole
    // part rather than as a divisor, and counts as used all the same.
    let all = [
        "2",
        "3",
        "7",
        "19",
        "43",
        "73",
        "127",
        "337",
        "5419",
        "92737",
        "649657",
        "77158673929",
    ];
    let complete = run(M127, &all.join(" "), two_levels());
    assert_eq!(complete.status, "certified", "{}", complete.message);
    assert_eq!(complete.hints_used, all);
    assert!(complete.hints_unused.is_empty());
    assert_eq!(complete.outputs, plain.outputs);
}

#[test]
fn a_root_hint_is_used_and_the_certificate_is_the_same() {
    let plain = run(M127, "", two_levels());
    // 11 is the smallest primitive root of 77158673929, so the text does not change.
    let rooted = run(M127, "77158673929:11", two_levels());
    assert_eq!(rooted.status, "certified", "{}", rooted.message);
    assert_eq!(rooted.hints_used, ["77158673929"]);
    assert!(rooted.hints_unused.is_empty());
    assert_eq!(rooted.outputs, plain.outputs);
    // 23 is another primitive root of 77158673929, and the entry takes it.
    let other = run(M127, "77158673929:23", two_levels());
    assert_eq!(other.status, "certified", "{}", other.message);
    assert_eq!(other.primes[1].value, "77158673929");
    assert_eq!(other.primes[1].root, Some(23));
    let output = code(&other, "mathlib");
    assert!(
        output.contains("\n    .lucas { root := 23, primeFactors := [2, 3, 7, 73, 699053] },\n"),
        "{output}"
    );
    // No other entry has the root 23, so that root is the only difference.
    assert_eq!(
        output.replace("root := 23,", "root := 11,"),
        code(&plain, "mathlib")
    );
    // 4 is a square, so not a root: the search from 2 finds 11 as without the hint.
    let wrong = run(M127, "77158673929:4", two_levels());
    assert_eq!(wrong.status, "certified", "{}", wrong.message);
    assert_eq!(wrong.outputs, rooted.outputs);
}

#[test]
fn cli_root_hint_on_2_127_minus_1_gives_the_same_certificate() {
    let expected = code(&run(M127, "", Config::default()), "mathlib");
    let out = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args([M127, "--threads", "2", "--hints", "77158673929:11"])
        .output()
        .expect("the binary runs");
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(out.stdout, expected.as_bytes());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("\nhints used: 77158673929\n"), "{stderr}");
    assert!(!stderr.contains("hints dividing nothing"), "{stderr}");
}

#[test]
fn cli_output_on_2_127_minus_1_matches_the_library() {
    let snap = run(M127, "", Config::default());
    let out = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args([M127, "--threads", "2"])
        .output()
        .expect("the binary runs");
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(out.stdout, code(&snap, TARGETS[0].name).as_bytes());
    for target in TARGETS {
        let chosen = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
            .args([M127, "--threads", "2", "--quiet", "--target", target.name])
            .output()
            .expect("the binary runs");
        assert!(chosen.status.success(), "{}", target.name);
        assert_eq!(chosen.stdout, code(&snap, target.name).as_bytes());
    }
    // Whether the first report shows the input under analysis or already in the tree depends on
    // when the worker returns, so only the reports' shape and the final tree are checked.
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.lines().any(|line| {
            line.starts_with('[') && (line.contains("running:") || line.contains("certified:"))
        }),
        "{stderr}"
    );
    assert!(
        stderr.contains(
            "  170141183460469231731687303715884105727 (39 digits) done root 43 factors \
             2 3 7 19 43 73 127 337 5419 92737 649657 77158673929\n"
        ),
        "{stderr}"
    );
}
