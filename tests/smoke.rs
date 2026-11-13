//! Smoke tests of the defaults, the JSON glue and the CLI. The end-to-end runs are in
//! `end_to_end.rs`.

use std::process::Command;

use primality_producer::ecm::default_levels;
use primality_producer::{
    BigUint, Certificate, Config, Entry, Outcome, Rest, Task, TaskResult, TARGETS,
};

#[test]
fn config_defaults_are_the_production_values() {
    let config = Config::default();
    assert_eq!(config.witness_bound, 1024);
    assert_eq!(config.trial_bound, 65_536);
    assert_eq!(config.rho_steps, 1 << 17);
    assert_eq!(config.rho_tasks, 2);
    assert_eq!(config.pm1_b1, 100_000);
    assert_eq!(config.pm1_b2, 10_000_000);
    assert_eq!(config.ecm_levels, default_levels());
    assert_eq!(config.max_ecm_levels, None);
    assert_eq!(config.root_bound, 100_000);
    assert_eq!(config.max_digits, 1000);
}

#[test]
fn default_levels_match_the_table() {
    let levels = default_levels();
    let table: Vec<(u32, u64, u64, u32, u32)> = levels
        .iter()
        .map(|l| (l.digits, l.b1, l.b2, l.curves, l.curves_per_task))
        .collect();
    assert_eq!(
        table,
        vec![
            (15, 2_000, 200_000, 25, 5),
            (20, 11_000, 1_100_000, 90, 3),
            (25, 50_000, 5_000_000, 300, 1),
            (30, 250_000, 25_000_000, 700, 1),
            (35, 1_000_000, 100_000_000, 1800, 1),
            (40, 3_000_000, 300_000_000, 5100, 1),
        ]
    );
    assert!(levels.iter().all(|l| l.b2 == 100 * l.b1));
}

#[test]
fn task_id_is_the_id_field_of_every_variant() {
    let m = BigUint::from(91u32);
    let tasks = [
        Task::Analyze {
            id: 1,
            m: m.clone(),
            trial_bound: 100,
        },
        Task::Rho {
            id: 2,
            m: m.clone(),
            c: 1,
            steps: 10,
        },
        Task::Pm1 {
            id: 3,
            m: m.clone(),
            b1: 10,
            b2: 100,
        },
        Task::Ecm {
            id: 4,
            m: m.clone(),
            b1: 10,
            b2: 100,
            sigma_start: 6,
            curves: 2,
        },
        Task::Root {
            id: 5,
            q: m.clone(),
            factors: vec![BigUint::from(2u32), BigUint::from(3u32)],
            bound: 100,
            hint: None,
        },
        Task::Verify {
            id: 6,
            cert: Certificate {
                n: m.clone(),
                entries: vec![Entry {
                    q: m,
                    root: 2,
                    factors: vec![BigUint::from(2u32)],
                }],
            },
            witness_bound: 1000,
            term: "91".to_string(),
        },
    ];
    let ids: Vec<u32> = tasks.iter().map(Task::id).collect();
    assert_eq!(ids, vec![1, 2, 3, 4, 5, 6]);
}

#[test]
fn tasks_and_results_round_trip_through_json_as_decimal_strings() {
    let big =
        BigUint::parse_bytes(b"123456789012345678901234567890123456789012345678901", 10).unwrap();
    let task = Task::Root {
        id: 7,
        q: big.clone(),
        factors: vec![BigUint::from(2u32), big.clone()],
        bound: 100_000,
        hint: Some(big.clone() + 2u32),
    };
    let json = serde_json::to_string(&task).unwrap();
    assert!(json.contains(r#""kind":"Root""#), "{json}");
    assert!(
        json.contains(r#""q":"123456789012345678901234567890123456789012345678901""#),
        "{json}"
    );
    assert!(
        json.contains(r#""factors":["2","123456789012345678901234567890123456789012345678901"]"#),
        "{json}"
    );
    assert!(
        json.contains(r#""hint":"123456789012345678901234567890123456789012345678903""#),
        "{json}"
    );
    let back: Task = serde_json::from_str(&json).unwrap();
    assert_eq!(back, task);
    // A missing hint is `null`, and a task without the field parses too.
    let unhinted = Task::Root {
        id: 7,
        q: BigUint::from(65537u32),
        factors: vec![BigUint::from(2u32)],
        bound: 100_000,
        hint: None,
    };
    let json = serde_json::to_string(&unhinted).unwrap();
    assert!(json.contains(r#""hint":null"#), "{json}");
    assert_eq!(serde_json::from_str::<Task>(&json).unwrap(), unhinted);
    let without_field = r#"{"kind":"Root","id":7,"q":"65537","factors":["2"],"bound":100000}"#;
    assert_eq!(
        serde_json::from_str::<Task>(without_field).unwrap(),
        unhinted
    );

    let result = TaskResult {
        id: 7,
        outcome: Outcome::Analyzed {
            small: vec![(2, 3), (5, 1)],
            rest: Rest::Composite {
                value: big,
                witness: Some(2),
            },
        },
    };
    let json = serde_json::to_string(&result).unwrap();
    assert!(json.contains(r#""kind":"Analyzed""#), "{json}");
    assert!(json.contains(r#""rest":{"kind":"Composite""#), "{json}");
    let back: TaskResult = serde_json::from_str(&json).unwrap();
    assert_eq!(back, result);

    let one = TaskResult {
        id: 8,
        outcome: Outcome::Analyzed {
            small: vec![(3, 1)],
            rest: Rest::One,
        },
    };
    let json = serde_json::to_string(&one).unwrap();
    assert!(json.contains(r#""rest":{"kind":"One"}"#), "{json}");
    assert_eq!(serde_json::from_str::<TaskResult>(&json).unwrap(), one);

    let bad = r#"{"id":1,"outcome":{"kind":"Divisor","d":"12a"}}"#;
    assert!(serde_json::from_str::<TaskResult>(bad).is_err());
    let signed = r#"{"id":1,"outcome":{"kind":"Divisor","d":"+12"}}"#;
    assert!(serde_json::from_str::<TaskResult>(signed).is_err());
}

#[test]
fn cli_certifies_65537() {
    let out = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args(["65537", "--quiet"])
        .output()
        .expect("the binary runs");
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(
        text.starts_with(
            "import Mathlib.Tactic.Primality\n\nexample : Nat.Prime 65537 := by\n  \
             primality (cert := .witnesses ["
        ),
        "{text}"
    );
    assert!(
        text.contains("\n    .lucas { root := 3, primeFactors := [2] }])\n"),
        "{text}"
    );
}

#[test]
fn cli_refuses_an_unknown_target() {
    let out = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args(["65537", "--quiet", "--target", "lean"])
        .output()
        .expect("the binary runs");
    assert_eq!(out.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.starts_with("--target needs one of mathlib"),
        "{stderr}"
    );
}

#[test]
fn cli_states_an_expression_input_in_lean_syntax() {
    let out = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args(["2^16+1"])
        .output()
        .expect("the binary runs");
    assert!(out.status.success());
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "import Mathlib.Tactic.Primality\nimport Mathlib.Tactic.NormNum.Pow\n\n\
         example : Nat.Prime (2 ^ 16 + 1) := by\n  primality (cert := .witnesses [\n    \
         .lucas { root := 3, primeFactors := [2] }])\n"
    );
    let out = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args(["2^16 - 2^17", "--quiet"])
        .output()
        .expect("the binary runs");
    assert_eq!(out.status.code(), Some(1));
    assert_eq!(
        String::from_utf8_lossy(&out.stderr),
        "the subtraction 65536 - 131072 goes below zero\n"
    );
}

#[test]
fn cli_reports_the_hint_usage_on_stderr_only() {
    // 4 and 8 both divide 65536, 3 does not.
    let out = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args(["65537", "--hints", "4 8 3"])
        .output()
        .expect("the binary runs");
    assert!(out.status.success());
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "import Mathlib.Tactic.Primality\n\nexample : Nat.Prime 65537 := by\n  \
         primality (cert := .witnesses [\n    .lucas { root := 3, primeFactors := [2] }])\n"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("\nhints used: 4, 8\n"), "{stderr}");
    assert!(stderr.contains("\nhints dividing nothing: 3\n"), "{stderr}");
    let quiet = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args(["65537", "--hints", "4 8 3", "--quiet"])
        .output()
        .expect("the binary runs");
    assert_eq!(quiet.stdout, out.stdout);
    assert!(
        quiet.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&quiet.stderr)
    );
}

#[test]
fn cli_json_prints_the_final_snapshot() {
    let out = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args(["65537", "--json", "--quiet"])
        .output()
        .expect("the binary runs");
    assert!(
        out.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let snapshot: serde_json::Value =
        serde_json::from_slice(&out.stdout).expect("a JSON snapshot on stdout");
    assert_eq!(snapshot["status"], "certified");
    assert_eq!(snapshot["message"], "65537 is prime (1 witness entry)");
    let prime = &snapshot["primes"][0];
    assert_eq!(prime["value"], "65537");
    assert_eq!(prime["digits"], 5);
    assert_eq!(prime["state"], "done");
    assert_eq!(prime["root"], 3);
    assert_eq!(prime["factors"], serde_json::json!(["2"]));
    assert_eq!(snapshot["hints_used"], serde_json::json!([]));
    assert_eq!(snapshot["hints_unused"], serde_json::json!([]));
    assert_eq!(snapshot["outputs"][0]["target"], "mathlib");
    assert_eq!(
        snapshot["outputs"][0]["code"],
        "import Mathlib.Tactic.Primality\n\nexample : Nat.Prime 65537 := by\n  \
         primality (cert := .witnesses [\n    .lucas { root := 3, primeFactors := [2] }])\n"
    );
    assert_eq!(snapshot["found_factors"], "");
    let targets: Vec<&str> = snapshot["outputs"]
        .as_array()
        .expect("the outputs")
        .iter()
        .map(|output| output["target"].as_str().expect("a target name"))
        .collect();
    let names: Vec<&str> = TARGETS.iter().map(|target| target.name).collect();
    assert_eq!(targets, names);
    assert!(out.stderr.is_empty());
    // A composite gets the snapshot on stdout and the exit code it has without `--json`.
    let out = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args(["1000001", "--json", "--quiet"])
        .output()
        .expect("the binary runs");
    assert_eq!(out.status.code(), Some(2));
    let snapshot: serde_json::Value =
        serde_json::from_slice(&out.stdout).expect("a JSON snapshot on stdout");
    assert_eq!(snapshot["status"], "composite");
    assert_eq!(snapshot["message"], "1000001 = 101 × 9901");
    assert_eq!(snapshot["outputs"], serde_json::json!([]));
}

#[test]
fn cli_reports_a_composite_with_exit_code_2() {
    let out = Command::new(env!("CARGO_BIN_EXE_primality-cert"))
        .args(["1000001", "--quiet"])
        .output()
        .expect("the binary runs");
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "1000001 = 101 × 9901\n"
    );
    assert!(
        out.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
