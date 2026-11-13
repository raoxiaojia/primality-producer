//! The unit of work handed to a worker (`Task`), what comes back (`Outcome`, `TaskResult`) and
//! `run_task`, which executes one task.

use num_integer::Integer;
use num_traits::{One, Zero};
use serde::{Deserialize, Serialize};

use crate::arith::{self, BigUint};
use crate::input;
use crate::targets::{self, Output};
use crate::verify::{self, Certificate};
use crate::{ecm, pm1, rho};

/// One unit of work for a worker.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum Task {
    /// Divides `m` by every prime below `trial_bound`, then tests the cofactor by Miller–Rabin
    /// and for being a perfect power.
    Analyze {
        id: u32,
        #[serde(with = "crate::arith::big_str")]
        m: BigUint,
        trial_bound: u32,
    },
    Rho {
        id: u32,
        #[serde(with = "crate::arith::big_str")]
        m: BigUint,
        c: u64,
        steps: u64,
    },
    Pm1 {
        id: u32,
        #[serde(with = "crate::arith::big_str")]
        m: BigUint,
        b1: u64,
        b2: u64,
    },
    /// `curves` curves with `sigma = sigma_start, sigma_start + 1, …`.
    Ecm {
        id: u32,
        #[serde(with = "crate::arith::big_str")]
        m: BigUint,
        b1: u64,
        b2: u64,
        sigma_start: u64,
        curves: u32,
    },
    /// The smallest primitive root of the prime `q` with the distinct prime factors `factors` of
    /// `q − 1`, among `2, …, bound`. A hinted root (`hint`, from a `q:a` hint) is tried first.
    Root {
        id: u32,
        #[serde(with = "crate::arith::big_str")]
        q: BigUint,
        #[serde(with = "crate::arith::big_str_vec")]
        factors: Vec<BigUint>,
        bound: u64,
        #[serde(default, with = "crate::arith::big_str_opt")]
        hint: Option<BigUint>,
    },
    /// The independent check of the finished certificate by `verify::verify`, then the rendering
    /// of every target's text, which states the input as `term` (`input::Input::term`).
    Verify {
        id: u32,
        cert: Certificate,
        witness_bound: u64,
        term: String,
    },
}

impl Task {
    /// The task's id, which its `TaskResult` repeats.
    pub fn id(&self) -> u32 {
        match self {
            Task::Analyze { id, .. }
            | Task::Rho { id, .. }
            | Task::Pm1 { id, .. }
            | Task::Ecm { id, .. }
            | Task::Root { id, .. }
            | Task::Verify { id, .. } => *id,
        }
    }
}

/// The cofactor left by trial division in an `Analyze` task.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum Rest {
    One,
    Prime {
        #[serde(with = "crate::arith::big_str")]
        value: BigUint,
    },
    /// `witness` is a Miller–Rabin base proving `value` composite (`None` for 0, which no base
    /// proves).
    Composite {
        #[serde(with = "crate::arith::big_str")]
        value: BigUint,
        witness: Option<u64>,
    },
    Power {
        #[serde(with = "crate::arith::big_str")]
        base: BigUint,
        exp: u32,
    },
}

/// What a task found.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind")]
pub enum Outcome {
    Analyzed {
        small: Vec<(u64, u32)>,
        rest: Rest,
    },
    /// A nontrivial divisor of the task's `m` (the driver checks it again).
    Divisor {
        #[serde(with = "crate::arith::big_str")]
        d: BigUint,
    },
    NoFactor,
    /// The primitive root found (the hint when it is one, else the smallest). `None` means no root
    /// up to the bound, which is practically impossible for a prime `q`.
    Root {
        root: Option<u64>,
    },
    /// The certificate of a `Verify` task passed the checks, with the Lean file of every target in
    /// the order of `targets::TARGETS`.
    Verified {
        outputs: Vec<Output>,
    },
    /// The certificate of a `Verify` task failed a check, with its message.
    VerifyFailed {
        message: String,
    },
    Error {
        message: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TaskResult {
    pub id: u32,
    pub outcome: Outcome,
}

/// Runs one task. `progress(done)` is called after each ECM curve with the number of curves
/// finished so far in this task; other tasks never call it. An ECM task polls `stop()` during its
/// curves and ends with `NoFactor` once it is true, so it is set only for a task whose result is
/// no longer wanted (`Driver::submit` returns their ids).
pub fn run_task(task: &Task, progress: &mut dyn FnMut(u32), stop: &dyn Fn() -> bool) -> TaskResult {
    let outcome = match task {
        Task::Analyze { m, trial_bound, .. } => analyze(m, *trial_bound),
        Task::Rho { m, c, steps, .. } => factor_outcome(rho::pollard_rho(m, *c, *steps)),
        Task::Pm1 { m, b1, b2, .. } => factor_outcome(pm1::pollard_pm1(m, *b1, *b2)),
        Task::Ecm {
            m,
            b1,
            b2,
            sigma_start,
            curves,
            ..
        } => run_ecm(m, *b1, *b2, *sigma_start, *curves, progress, stop),
        Task::Root {
            q,
            factors,
            bound,
            hint,
            ..
        } => Outcome::Root {
            root: primitive_root(q, factors, *bound, hint.as_ref()),
        },
        Task::Verify {
            cert,
            witness_bound,
            term,
            ..
        } => match verify_and_render(cert, *witness_bound, term) {
            Ok(outputs) => Outcome::Verified { outputs },
            Err(message) => Outcome::VerifyFailed { message },
        },
    };
    TaskResult {
        id: task.id(),
        outcome,
    }
}

fn analyze(m: &BigUint, trial_bound: u32) -> Outcome {
    let (small, rest) = arith::trial_division(m, trial_bound);
    let rest = if rest.is_one() {
        Rest::One
    } else if arith::to_u64(&rest).is_some_and(|r| r >= 2 && r < u64::from(trial_bound).pow(2)) {
        // No prime below `trial_bound` divides the cofactor, so below `trial_bound²` it is prime.
        Rest::Prime { value: rest }
    } else {
        match arith::miller_rabin(&rest) {
            Ok(()) => Rest::Prime { value: rest },
            Err(witness) => match arith::perfect_power(&rest) {
                Some((base, exp)) => Rest::Power { base, exp },
                None => Rest::Composite {
                    value: rest,
                    witness: (witness != 0).then_some(witness),
                },
            },
        }
    };
    Outcome::Analyzed { small, rest }
}

/// Every target's Lean file for `cert`, once `verify::verify` accepts `cert` and `term` evaluates
/// to `cert.n`. The error is the message of the first failed check, a target's own checks included.
fn verify_and_render(
    cert: &Certificate,
    witness_bound: u64,
    term: &str,
) -> Result<Vec<Output>, String> {
    verify::verify(cert, witness_bound)?;
    let input = match input::parse_term(term) {
        Ok(input) if input.n == cert.n => input,
        _ => return Err(format!("the term {term} does not evaluate to {}", cert.n)),
    };
    targets::render_outputs(cert, &input)
}

fn factor_outcome(divisor: Option<BigUint>) -> Outcome {
    match divisor {
        Some(d) => Outcome::Divisor { d },
        None => Outcome::NoFactor,
    }
}

/// Runs the curves of an `Ecm` task, stopping at the first divisor or once `stop()` is true.
fn run_ecm(
    m: &BigUint,
    b1: u64,
    b2: u64,
    sigma_start: u64,
    curves: u32,
    progress: &mut dyn FnMut(u32),
    stop: &dyn Fn() -> bool,
) -> Outcome {
    for i in 0..curves {
        let sigma = sigma_start.wrapping_add(u64::from(i));
        let divisor = ecm::ecm_curve(m, sigma, b1, b2, stop);
        if divisor.is_none() && stop() {
            break;
        }
        progress(i + 1);
        if let Some(d) = divisor {
            return Outcome::Divisor { d };
        }
    }
    Outcome::NoFactor
}

/// The hint when it is a root, else the smallest root in `2..=bound` below `q`. A root is an `a`
/// with `a^(q−1) ≡ 1` and `a^((q−1)/r) ≢ 1` modulo `q` for every `r` in `factors`, the distinct
/// prime factors of `q − 1`. A prime `q` has its primitive roots as roots, and a composite `q`
/// has none. The hint is reduced modulo `q` and skipped when the residue does not fit a `u64`.
///
/// The search drops a candidate at its first failing factor, in ascending order. For the factor
/// 2 it tests `(a | q) = -1`, which for a prime `q` is `a^((q−1)/2) ≢ 1` (Euler's criterion) at
/// the cost of a gcd. The first candidate passing every factor is returned if `a^(q−1) ≡ 1`.
/// Otherwise `q` is composite and the search ends with no root. For a composite `q` the Jacobi
/// test can pass where the power test fails, so a returned candidate need not be a root.
fn primitive_root(
    q: &BigUint,
    factors: &[BigUint],
    bound: u64,
    hint: Option<&BigUint>,
) -> Option<u64> {
    if q.bits() < 2 {
        return None; // `q < 2` has no residues to test
    }
    let q_minus_1 = q - 1u32;
    let mut factors: Vec<BigUint> = factors.iter().filter(|r| !r.is_zero()).cloned().collect();
    factors.sort();
    factors.dedup();
    if let Some(a) = hint.map(|a| a % q).as_ref().and_then(arith::to_u64) {
        if a >= 2 {
            let (powers, full) = arith::lucas_powers(&BigUint::from(a), q, &factors);
            if full.is_one() && powers.iter().all(|p| !p.is_one()) {
                return Some(a);
            }
        }
    }
    let top = arith::to_u64(&q_minus_1).map_or(bound, |q1| q1.min(bound));
    let by_jacobi = q.is_odd() && factors.first() == Some(&BigUint::from(2u32));
    let exponents: Vec<BigUint> = factors
        .iter()
        .skip(usize::from(by_jacobi))
        .map(|r| &q_minus_1 / r)
        .collect();
    for a in 2..=top {
        let candidate = BigUint::from(a);
        if by_jacobi && arith::jacobi(&candidate, q) != -1 {
            continue;
        }
        if exponents
            .iter()
            .any(|e| arith::powmod(&candidate, e, q).is_one())
        {
            continue;
        }
        return arith::powmod(&candidate, &q_minus_1, q)
            .is_one()
            .then_some(a);
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn big(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).unwrap()
    }

    fn run(task: Task) -> Outcome {
        let mut calls = Vec::new();
        let result = run_task(&task, &mut |done| calls.push(done), &|| false);
        assert_eq!(result.id, task.id());
        if !matches!(task, Task::Ecm { .. }) {
            assert!(calls.is_empty(), "progress called by {task:?}");
        }
        result.outcome
    }

    fn analyze(m: &str, trial_bound: u32) -> Outcome {
        run(Task::Analyze {
            id: 1,
            m: big(m),
            trial_bound,
        })
    }

    #[test]
    fn analyze_classifies_the_cofactor() {
        assert_eq!(
            analyze("1000001", 65_536),
            Outcome::Analyzed {
                small: vec![(101, 1), (9901, 1)],
                rest: Rest::One
            }
        );
        // 65537 is below the trial bound, so it is a small prime with the cofactor 1.
        assert_eq!(
            analyze("65537", 100_000),
            Outcome::Analyzed {
                small: vec![(65537, 1)],
                rest: Rest::One
            }
        );
        // A cofactor below `trial_bound²` is prime without a test.
        assert_eq!(
            analyze("4294967291", 65_536), // 2^32 - 5
            Outcome::Analyzed {
                small: vec![],
                rest: Rest::Prime {
                    value: big("4294967291")
                }
            }
        );
        let m127 = "170141183460469231731687303715884105727";
        assert_eq!(
            analyze(m127, 65_536),
            Outcome::Analyzed {
                small: vec![],
                rest: Rest::Prime { value: big(m127) }
            }
        );
        assert_eq!(
            analyze("1000006000009", 1000), // 1000003^2
            Outcome::Analyzed {
                small: vec![],
                rest: Rest::Power {
                    base: big("1000003"),
                    exp: 2
                }
            }
        );
        // 3215031751 = 151 · 751 · 28351 is a strong pseudoprime to the bases 2, 3, 5 and 7.
        assert_eq!(
            analyze("3215031751", 100),
            Outcome::Analyzed {
                small: vec![],
                rest: Rest::Composite {
                    value: big("3215031751"),
                    witness: Some(11)
                }
            }
        );
        let Outcome::Analyzed { small, rest } = analyze("1000000000100000000002379", 65_536) else {
            panic!("not analyzed");
        };
        assert!(small.is_empty());
        assert!(matches!(
            rest,
            Rest::Composite {
                witness: Some(_),
                ..
            }
        ));
        assert_eq!(
            analyze("1", 100),
            Outcome::Analyzed {
                small: vec![],
                rest: Rest::One
            }
        );
    }

    #[test]
    fn factoring_tasks_return_a_checked_divisor_or_no_factor() {
        let m = big("1000003") * big("1000033");
        let outcome = run(Task::Rho {
            id: 2,
            m: m.clone(),
            c: 1,
            steps: 1 << 17,
        });
        let Outcome::Divisor { d } = outcome else {
            panic!("{outcome:?}");
        };
        assert!(d == big("1000003") || d == big("1000033"));
        assert_eq!(
            run(Task::Rho {
                id: 2,
                m: big("2305843009213693951"),
                c: 1,
                steps: 1000,
            }),
            Outcome::NoFactor
        );
        // 200560490131 - 1 is 1000-smooth.
        let m = big("200560490131") * big("1000000000039");
        assert_eq!(
            run(Task::Pm1 {
                id: 3,
                m,
                b1: 1000,
                b2: 1000,
            }),
            Outcome::Divisor {
                d: big("200560490131")
            }
        );
    }

    #[test]
    fn ecm_reports_every_curve_and_stops_at_the_first_divisor() {
        // `sigma = 10` finds 314159265359 at the first level and `sigma = 9` does not.
        let m = big("314159265359") * big("27182818284590452387");
        let mut calls = Vec::new();
        let task = Task::Ecm {
            id: 4,
            m: m.clone(),
            b1: 2000,
            b2: 200_000,
            sigma_start: 9,
            curves: 5,
        };
        let result = run_task(&task, &mut |done| calls.push(done), &|| false);
        assert_eq!(result.id, 4);
        assert_eq!(
            result.outcome,
            Outcome::Divisor {
                d: big("314159265359")
            }
        );
        assert_eq!(calls, [1, 2]);
        let mut calls = Vec::new();
        let task = Task::Ecm {
            id: 5,
            m: big("10000000000000000051"),
            b1: 2000,
            b2: 2000,
            sigma_start: 6,
            curves: 3,
        };
        let result = run_task(&task, &mut |done| calls.push(done), &|| false);
        assert_eq!(result.outcome, Outcome::NoFactor);
        assert_eq!(calls, [1, 2, 3]);
    }

    #[test]
    fn ecm_ends_with_no_factor_once_stop_is_true() {
        // The task above, asked to stop after its first curve: the second, which finds the
        // factor, ends at once.
        let task = Task::Ecm {
            id: 4,
            m: big("314159265359") * big("27182818284590452387"),
            b1: 2000,
            b2: 200_000,
            sigma_start: 9,
            curves: 5,
        };
        let stopped = std::cell::Cell::new(false);
        let mut calls = Vec::new();
        let result = run_task(
            &task,
            &mut |done| {
                calls.push(done);
                stopped.set(true);
            },
            &|| stopped.get(),
        );
        assert_eq!(result.outcome, Outcome::NoFactor);
        assert_eq!(calls, [1]);
    }

    fn root_task(q: &str, factors: &[u64], bound: u64, hint: Option<BigUint>) -> Task {
        Task::Root {
            id: 6,
            q: big(q),
            factors: factors.iter().map(|&r| BigUint::from(r)).collect(),
            bound,
            hint,
        }
    }

    #[test]
    fn root_finds_the_smallest_primitive_root_or_none_for_a_composite() {
        let root = |q: &str, factors: &[u64], bound: u64| run(root_task(q, factors, bound, None));
        assert_eq!(
            root("65537", &[2], 100_000),
            Outcome::Root { root: Some(3) }
        );
        assert_eq!(
            root("1289", &[2, 7, 23], 100_000),
            Outcome::Root { root: Some(6) }
        );
        // The search stays below `q`, so a bound beyond it changes nothing.
        assert_eq!(
            root("1009", &[2, 3, 7], 100_000),
            Outcome::Root { root: Some(11) }
        );
        assert_eq!(
            root(
                "170141183460469231731687303715884105727",
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
                    77158673929
                ],
                100_000
            ),
            Outcome::Root { root: Some(43) }
        );
        // The factors are taken in ascending order whatever their order, and duplicates and
        // zeros are dropped.
        assert_eq!(
            root("1289", &[23, 2, 7, 2, 0], 100_000),
            Outcome::Root { root: Some(6) }
        );
        // 1022117 = 1009 · 1013 with "factors" of 1022116 = 2^2 · 255529: no root exists. The
        // candidate 2 passes the Jacobi test and `2^4 ≢ 1`, and fails the Fermat test.
        assert_eq!(
            root("1022117", &[2, 255529], 100_000),
            Outcome::Root { root: None }
        );
        // An even composite, whose factor 2 is tested by its power.
        assert_eq!(root("4", &[3], 100), Outcome::Root { root: None });
        assert_eq!(root("3", &[2], 100), Outcome::Root { root: Some(2) });
        assert_eq!(root("3", &[], 100), Outcome::Root { root: Some(2) });
        assert_eq!(root("65537", &[2], 2), Outcome::Root { root: None });
        assert_eq!(root("2", &[], 100), Outcome::Root { root: None });
        assert_eq!(root("0", &[], 100), Outcome::Root { root: None });
    }

    #[test]
    fn a_hinted_root_is_tried_first_and_a_wrong_one_falls_back_to_the_search() {
        let root = |q: &str, factors: &[u64], hint: &str| {
            run(root_task(q, factors, 100_000, Some(big(hint))))
        };
        // 5 is a primitive root of 65537 but not the smallest, 3.
        assert_eq!(root("65537", &[2], "5"), Outcome::Root { root: Some(5) });
        // 4 is a square, so not a root: the search from 2 finds 3.
        assert_eq!(root("65537", &[2], "4"), Outcome::Root { root: Some(3) });
        for bad in ["0", "1", "65537"] {
            assert_eq!(
                root("65537", &[2], bad),
                Outcome::Root { root: Some(3) },
                "{bad}"
            );
        }
        // A hint is reduced modulo `q`, even one beyond `u64`.
        assert_eq!(
            root("65537", &[2], "65542"),
            Outcome::Root { root: Some(5) }
        );
        let huge = big("65537") * BigUint::from(u64::MAX) + 5u32;
        assert_eq!(
            run(root_task("65537", &[2], 100_000, Some(huge))),
            Outcome::Root { root: Some(5) }
        );
        assert_eq!(
            root("1289", &[2, 7, 23], "6"),
            Outcome::Root { root: Some(6) }
        );
        // A composite has no root, hinted or not.
        assert_eq!(
            root("1022117", &[2, 255529], "2"),
            Outcome::Root { root: None }
        );
        // The hint is tried even when the search bound rules the search out.
        assert_eq!(
            run(root_task("65537", &[2], 2, Some(big("5")))),
            Outcome::Root { root: Some(5) }
        );
        // A large prime: the hinted root 43 (its smallest) and 53 are accepted, the square 4
        // falls back to the search.
        let m127 = "170141183460469231731687303715884105727";
        let factors = [
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
        ];
        for (hint, expected) in [("43", 43), ("53", 53), ("4", 43)] {
            assert_eq!(
                root(m127, &factors, hint),
                Outcome::Root {
                    root: Some(expected)
                },
                "hint {hint}"
            );
        }
    }

    #[test]
    fn verify_checks_the_certificate_through_json() {
        let entry = |q: &str, root: u64, factors: &[u64]| crate::verify::Entry {
            q: big(q),
            root,
            factors: factors.iter().map(|&r| BigUint::from(r)).collect(),
        };
        let good = Certificate {
            n: big("1000003"),
            entries: vec![
                entry("1000003", 2, &[2, 3, 166667]),
                entry("166667", 2, &[2, 167, 499]),
            ],
        };
        let task = Task::Verify {
            id: 9,
            cert: good.clone(),
            witness_bound: 1000,
            term: "(10 ^ 6 + 3)".to_string(),
        };
        let json = serde_json::to_string(&task).unwrap();
        assert_eq!(
            json,
            r#"{"kind":"Verify","id":9,"cert":{"n":"1000003","entries":[{"q":"1000003","root":2,"factors":["2","3","166667"]},{"q":"166667","root":2,"factors":["2","167","499"]}]},"witness_bound":1000,"term":"(10 ^ 6 + 3)"}"#
        );
        let back: Task = serde_json::from_str(&json).unwrap();
        assert_eq!(back, task);
        let result = run_task(&back, &mut |_| panic!("no progress"), &|| false);
        assert_eq!(result.id, 9);
        assert_eq!(
            result.outcome,
            Outcome::Verified {
                outputs: targets::render_outputs(
                    &good,
                    &input::parse_input("(10 ^ 6 + 3)", 2000).unwrap()
                )
                .unwrap()
            }
        );
        let json = serde_json::to_string(&result).unwrap();
        assert!(
            json.starts_with(
                r#"{"id":9,"outcome":{"kind":"Verified","outputs":[{"target":"mathlib","code":"import Mathlib.Tactic.Primality\nimport Mathlib.Tactic.NormNum.Pow\n\nexample : Nat.Prime (10 ^ 6 + 3) := by\n"#
            ),
            "{json}"
        );
        // A term of another value is refused rather than rendered.
        assert_eq!(
            run(Task::Verify {
                id: 14,
                cert: good.clone(),
                witness_bound: 1000,
                term: "(10 ^ 6 + 5)".to_string(),
            }),
            Outcome::VerifyFailed {
                message: "the term (10 ^ 6 + 5) does not evaluate to 1000003".to_string()
            }
        );
        // The term of an input at the token limit, whose outer parentheses take it past the
        // limit, verifies.
        let chain = format!("1000003{}", " + 0".repeat(199));
        let term = input::parse_input(&chain, 2000).unwrap().term;
        let Outcome::Verified { outputs } = run(Task::Verify {
            id: 15,
            cert: good.clone(),
            witness_bound: 1000,
            term: term.clone(),
        }) else {
            panic!("the term at the token limit verifies");
        };
        assert!(outputs.iter().all(|output| output.code.contains(&term)));
        // A term that does not print back as itself is refused, although its value is right.
        assert!(matches!(
            run(Task::Verify {
                id: 16,
                cert: good.clone(),
                witness_bound: 1000,
                term: "(10^6 + 3)".to_string(),
            }),
            Outcome::VerifyFailed { .. }
        ));
        assert_eq!(serde_json::from_str::<TaskResult>(&json).unwrap(), result);
        // A wrong root and a missing entry: each failure carries `verify`'s message.
        let mut bad = good.clone();
        bad.entries[0].root = 4;
        let task = Task::Verify {
            id: 10,
            cert: bad,
            witness_bound: 1000,
            term: "1000003".to_string(),
        };
        let json = serde_json::to_string(&task).unwrap();
        let result = run_task(
            &serde_json::from_str::<Task>(&json).unwrap(),
            &mut |_| {},
            &|| false,
        );
        assert_eq!(
            result.outcome,
            Outcome::VerifyFailed {
                message: "entry 0 (q = 1000003): root 4 ^ ((q - 1) / 2) is 1 mod q".to_string()
            }
        );
        let json = serde_json::to_string(&result).unwrap();
        assert!(json.contains(r#""kind":"VerifyFailed""#), "{json}");
        assert_eq!(serde_json::from_str::<TaskResult>(&json).unwrap(), result);
        let mut bad = good.clone();
        bad.entries.pop();
        assert_eq!(
            run(Task::Verify {
                id: 11,
                cert: bad,
                witness_bound: 1000,
                term: "1000003".to_string(),
            }),
            Outcome::VerifyFailed {
                message: "entry 0 (q = 1000003): factor 166667 has no entry".to_string()
            }
        );
    }
}
