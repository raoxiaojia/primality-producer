//! The state machine: the tree of primes, the open composites with their level-synchronous
//! schedule, and the snapshot the front ends render.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_traits::{One, Zero};
use serde::Serialize;

use crate::arith::{self, BigUint};
use crate::ecm::{self, EcmLevel};
use crate::hints::{render_hints, Hints};
use crate::input::{parse_input, Input};
use crate::targets::Output;
use crate::task::{self, Outcome, Rest, Task, TaskResult};
use crate::verify::{check_witness_bound, Certificate, Entry, MAX_WITNESS_BOUND};

/// The parameters of a run. `Default` gives the production values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Config {
    /// Primes below this need no certificate entry (at most `MAX_WITNESS_BOUND`).
    pub witness_bound: u64,
    /// The trial division bound.
    pub trial_bound: u32,
    /// The iterations of one rho task.
    pub rho_steps: u64,
    /// The number of rho tasks per composite, with `c = 1, 2, …`.
    pub rho_tasks: u32,
    /// The Pollard p−1 stage 1 bound.
    pub pm1_b1: u64,
    /// The Pollard p−1 stage 2 bound.
    pub pm1_b2: u64,
    /// The ECM levels in order.
    pub ecm_levels: Vec<EcmLevel>,
    /// The number of ECM levels to run (all when `None`).
    pub max_ecm_levels: Option<usize>,
    /// Primitive roots are searched among `2, …, root_bound`.
    pub root_bound: u64,
    /// The maximal number of decimal digits of the input.
    pub max_digits: usize,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            witness_bound: MAX_WITNESS_BOUND,
            trial_bound: 65_536,
            rho_steps: 1 << 17,
            rho_tasks: 2,
            pm1_b1: 100_000,
            pm1_b2: 10_000_000,
            ecm_levels: ecm::default_levels(),
            max_ecm_levels: None,
            root_bound: 100_000,
            max_digits: 1000,
        }
    }
}

/// An open composite as the page shows it.
#[derive(Clone, Debug, Serialize)]
pub struct CompositeView {
    pub value: String,
    pub digits: usize,
    pub stage: String,
    pub done: u32,
    pub total: u32,
}

/// A prime of the tree as the page shows it.
#[derive(Clone, Debug, Serialize)]
pub struct PrimeView {
    pub value: String,
    pub digits: usize,
    /// The state is "factoring" while a part of `q - 1` is open, "rooting" while the primitive
    /// root is searched, and "done" once it is found.
    pub state: String,
    pub root: Option<u64>,
    pub factors: Vec<String>,
    pub open: Vec<CompositeView>,
}

/// The lowest stage any open composite is at, with the work summed over the composites at it.
#[derive(Clone, Debug, Serialize)]
pub struct LevelView {
    pub name: String,
    pub done: u32,
    pub total: u32,
    /// The unit of `done` and `total`, "curves" for an ECM stage and "tasks" otherwise.
    pub unit: String,
}

/// The state of a run as the front ends render it.
#[derive(Clone, Debug, Serialize)]
pub struct Snapshot {
    /// The status is "running" until the run ends, then "certified", "composite" or "failed".
    pub status: String,
    /// One human-readable line (reason, summary).
    pub message: String,
    pub input: String,
    /// Entries `≥ witness_bound`, input first, then descending.
    pub primes: Vec<PrimeView>,
    /// `None` while no composite is open.
    pub level: Option<LevelView>,
    /// Every open composite has finished the ECM level for this many digits (0 before).
    pub searched_digits: u32,
    pub open_composites: usize,
    pub tasks_in_flight: usize,
    pub hints_used: Vec<String>,
    pub hints_unused: Vec<String>,
    /// The prime factors found at or above the witness bound as hints text, ascending, each with
    /// its primitive root when known. A run that stops or fails offers it to paste back as hints.
    pub found_factors: String,
    /// The Lean file of every target in the order of `targets::TARGETS`, nonempty only when
    /// `status == "certified"`.
    pub outputs: Vec<Output>,
}

/// Whether the run is over, and how.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Status {
    Running,
    Certified,
    Composite,
    Failed,
}

impl Status {
    /// The name the snapshot reports.
    fn name(self) -> &'static str {
        match self {
            Status::Running => "running",
            Status::Certified => "certified",
            Status::Composite => "composite",
            Status::Failed => "failed",
        }
    }
}

/// A prime `q ≥ witness_bound` of the tree.
struct Node {
    /// The primes whose `q - 1` this prime divides (empty for the input).
    parents: BTreeSet<BigUint>,
    /// The distinct prime factors of `q - 1` found so far.
    factors: BTreeSet<BigUint>,
    /// The primitive root, once found.
    root: Option<u64>,
    /// The id of the `Root` task queued or in flight for this prime.
    root_task: Option<u32>,
}

/// One stage of a composite's schedule.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StageKind {
    Rho {
        c: u64,
    },
    Pm1,
    /// The ECM level with this index in `Config::ecm_levels`.
    Ecm {
        level: usize,
    },
}

/// Where one task of a stage stands.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SlotState {
    Unassigned,
    /// Handed out as the task `id`; `done` is the progress reported so far.
    InFlight {
        id: u32,
        done: u32,
    },
    Done,
}

/// One task of the current stage of a composite. A rho or p-1 stage has one slot of one unit of
/// work. An ECM stage has a slot per task, whose units are its curves.
struct Slot {
    units: u32,
    sigma_start: u64,
    state: SlotState,
}

/// An open composite with its schedule.
struct Composite {
    /// The primes whose `q - 1` this composite divides.
    parents: BTreeSet<BigUint>,
    /// The index of the current stage in the schedule.
    stage: usize,
    kind: StageKind,
    slots: Vec<Slot>,
    /// The next unused `sigma` for ECM curves.
    sigma_next: u64,
}

impl Composite {
    fn has_unassigned(&self) -> bool {
        self.slots
            .iter()
            .any(|slot| slot.state == SlotState::Unassigned)
    }

    fn is_done(&self) -> bool {
        self.slots.iter().all(|slot| slot.state == SlotState::Done)
    }

    /// The work done and the work of the whole stage, in curves for ECM and in tasks otherwise.
    fn progress(&self) -> (u32, u32) {
        let mut done = 0;
        let mut total = 0;
        for slot in &self.slots {
            total += slot.units;
            done += match slot.state {
                SlotState::Unassigned => 0,
                SlotState::InFlight { done, .. } => done.min(slot.units),
                SlotState::Done => slot.units,
            };
        }
        (done, total)
    }
}

/// Whose part an `Analyze` task analyzes.
#[derive(Clone, Debug)]
enum Parents {
    Input,
    /// The primes whose `q - 1` the part divides. Empty once every parent was removed, in which
    /// case the result is discarded.
    Nodes(BTreeSet<BigUint>),
}

/// What a task is about, for routing its result.
enum Work {
    Analyze {
        m: BigUint,
        parents: Parents,
    },
    /// A task of the current stage of the composite `m`.
    Factor {
        m: BigUint,
    },
    Root {
        q: BigUint,
    },
    /// The check of the finished certificate, which ends the run.
    Verify {
        cert: Certificate,
    },
}

/// One run. Front ends take tasks from `take_tasks`, hand their results to `submit` and
/// render `snapshot`.
pub struct Driver {
    config: Config,
    /// The input's value.
    n: BigUint,
    /// The input as the Lean term the certificates state (`Input::term`).
    term: String,
    /// The factor hints, ascending and distinct, each at least 2.
    hints: Vec<BigUint>,
    hints_used: BTreeSet<BigUint>,
    /// A primitive root to try first, for each prime a root hint names.
    root_hints: BTreeMap<BigUint, BigUint>,
    status: Status,
    /// The message of a finished run.
    message: String,
    outputs: Vec<Output>,
    next_id: u32,
    nodes: BTreeMap<BigUint, Node>,
    composites: BTreeMap<BigUint, Composite>,
    /// Tasks created but not handed out, with their ids.
    queue: VecDeque<(u32, Work)>,
    /// Tasks handed out and not returned.
    in_flight: BTreeMap<u32, Work>,
}

impl Driver {
    /// A driver for the input `n`, a numeral or an expression (`input::parse_input`). Fails when
    /// `parse_input` rejects `n` or `config.witness_bound` exceeds `MAX_WITNESS_BOUND`.
    pub fn new(n: &str, hints: Hints, config: Config) -> Result<Driver, String> {
        check_witness_bound(config.witness_bound)?;
        let Input { n: value, term, .. } = parse_input(n, config.max_digits)?;
        let Hints { factors, roots } = hints;
        let mut hints: Vec<BigUint> = factors
            .into_iter()
            .filter(|h| *h >= BigUint::from(2u32))
            .collect();
        hints.sort();
        hints.dedup();
        let mut driver = Driver {
            config,
            n: value,
            term,
            hints,
            hints_used: BTreeSet::new(),
            root_hints: roots,
            status: Status::Running,
            message: String::new(),
            outputs: Vec::new(),
            next_id: 1,
            nodes: BTreeMap::new(),
            composites: BTreeMap::new(),
            queue: VecDeque::new(),
            in_flight: BTreeMap::new(),
        };
        driver.start();
        Ok(driver)
    }

    /// Up to `max` tasks, marked in flight. May return fewer, or none while results are awaited.
    pub fn take_tasks(&mut self, max: usize) -> Vec<Task> {
        let mut tasks = Vec::new();
        if max == 0 || self.is_finished() {
            return tasks;
        }
        while tasks.len() < max {
            let Some((id, work)) = self.queue.pop_front() else {
                break;
            };
            if let Some(task) = self.issue(id, &work) {
                self.in_flight.insert(id, work);
                tasks.push(task);
            }
        }
        if tasks.len() < max {
            self.issue_factor_tasks(max - tasks.len(), &mut tasks);
        }
        debug_assert!(
            !tasks.is_empty() || !self.in_flight.is_empty() || self.is_finished(),
            "take_tasks found nothing to do while nothing is in flight"
        );
        tasks
    }

    /// Updates the curve count of the in-flight task `id`, so the snapshot's `done` figures move
    /// during long tasks.
    pub fn report_progress(&mut self, id: u32, done: u32) {
        let Some(Work::Factor { m }) = self.in_flight.get(&id) else {
            return;
        };
        let Some(composite) = self.composites.get_mut(m) else {
            return;
        };
        for slot in &mut composite.slots {
            if let SlotState::InFlight {
                id: slot_id,
                done: progress,
            } = &mut slot.state
            {
                if *slot_id == id {
                    *progress = done.min(slot.units);
                }
            }
        }
    }

    /// Takes the result of an in-flight task and returns the ids of the factoring tasks it left
    /// stale, whose composite is gone. Those stop counting as in flight, so their results are
    /// discarded like those of unknown tasks and of a finished run.
    pub fn submit(&mut self, result: TaskResult) -> Vec<u32> {
        let id = result.id;
        let Some(work) = self.in_flight.remove(&id) else {
            return Vec::new();
        };
        if self.is_finished() {
            return Vec::new();
        }
        match (work, result.outcome) {
            (Work::Analyze { m, parents }, Outcome::Analyzed { small, rest }) => {
                self.on_analyzed(&m, parents, &small, &rest);
            }
            (Work::Factor { m }, Outcome::Divisor { d }) => self.on_divisor(id, &m, &d),
            (Work::Factor { m }, Outcome::NoFactor) => self.on_no_factor(id, &m),
            (Work::Root { q }, Outcome::Root { root }) => self.on_root(id, &q, root),
            (Work::Verify { cert }, Outcome::Verified { outputs }) => {
                self.on_verified(&cert, outputs);
            }
            (Work::Verify { .. }, Outcome::VerifyFailed { message }) => self.end(
                Status::Failed,
                format!("internal error: the certificate did not verify: {message}"),
            ),
            (_, Outcome::Error { message }) => self.end(
                Status::Failed,
                format!("internal error: task {id} failed: {message}"),
            ),
            (_, outcome) => self.end(
                Status::Failed,
                format!(
                    "internal error: task {id} returned an outcome of the wrong kind: {outcome:?}"
                ),
            ),
        }
        let stale = self.remove_stale_factor_tasks();
        if self.status == Status::Running {
            self.schedule_roots();
            self.try_finish();
        }
        stale
    }

    /// Removes the factoring tasks in flight whose composite is gone, split by another task or
    /// dropped with its parents, and returns their ids.
    fn remove_stale_factor_tasks(&mut self) -> Vec<u32> {
        let mut stale = Vec::new();
        self.in_flight.retain(|&id, work| {
            let gone = matches!(work, Work::Factor { m } if !self.composites.contains_key(m));
            if gone {
                stale.push(id);
            }
            !gone
        });
        stale
    }

    pub fn snapshot(&self) -> Snapshot {
        // Every prime of the tree other than the input divides some `q - 1` below it, so the
        // descending order puts the input first.
        let mut order: Vec<&BigUint> = self.nodes.keys().collect();
        order.reverse();
        let primes = order.into_iter().map(|q| self.prime_view(q)).collect();
        let (level, searched_digits) = self.level_view();
        let message = if self.status == Status::Running {
            self.running_message()
        } else {
            self.message.clone()
        };
        Snapshot {
            status: self.status.name().to_string(),
            message,
            input: self.n.to_string(),
            primes,
            level,
            searched_digits,
            open_composites: self.composites.len(),
            tasks_in_flight: self.in_flight.len(),
            hints_used: self.hints_used.iter().map(ToString::to_string).collect(),
            hints_unused: self
                .hints
                .iter()
                .filter(|h| !self.hints_used.contains(h))
                .map(ToString::to_string)
                .collect(),
            // The primes of the tree other than the input are the factors found at or above the
            // witness bound (`detach_node` removes a prime with its last parent).
            found_factors: render_hints(
                self.nodes
                    .iter()
                    .filter(|(q, _)| **q != self.n)
                    .map(|(q, node)| (q, node.root)),
            ),
            outputs: self.outputs.clone(),
        }
    }

    /// Whether the run is over.
    pub fn is_finished(&self) -> bool {
        self.status != Status::Running
    }

    /// Runs every task in this thread with `run_task`, one at a time (for tests).
    pub fn run_to_completion(&mut self) -> Snapshot {
        self.run_with(&mut |task| task::run_task(task, &mut |_| {}))
    }

    /// Runs the driver to completion with `exec` running each task. The unit tests pass a fake
    /// executor.
    fn run_with(&mut self, exec: &mut dyn FnMut(&Task) -> TaskResult) -> Snapshot {
        while !self.is_finished() {
            let Some(task) = self.take_tasks(1).pop() else {
                break;
            };
            let result = exec(&task);
            self.submit(result);
        }
        self.snapshot()
    }

    /// Reports an input below 2 or one split by a hint, and otherwise queues its analysis.
    fn start(&mut self) {
        let n = self.n.clone();
        if n < BigUint::from(2u32) {
            self.end(Status::Composite, format!("{n} is not prime"));
        } else if let Some(h) = self.hint_divisor(&n) {
            self.hints_used.insert(h.clone());
            self.end(Status::Composite, split_message(&n, &h, &(&n / &h)));
        } else {
            // A hint naming the input carries its root (a gallery entry stores `n:root`), so it
            // counts as used rather than as dividing nothing.
            if self.hints.binary_search(&n).is_ok() {
                self.hints_used.insert(n.clone());
            }
            self.push_analyze(n, Parents::Input);
        }
    }

    fn fresh_id(&mut self) -> u32 {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    fn push_analyze(&mut self, m: BigUint, parents: Parents) {
        let id = self.fresh_id();
        self.queue.push_back((id, Work::Analyze { m, parents }));
    }

    /// Ends the run. Tasks in flight stay counted until their results arrive and are discarded.
    fn end(&mut self, status: Status, message: String) {
        self.status = status;
        self.message = message;
        self.queue.clear();
    }

    /// Whether the certificate needs an entry for the prime `p`.
    fn needs_witness(&self, p: &BigUint) -> bool {
        *p >= BigUint::from(self.config.witness_bound)
    }

    /// The smallest hint `h` with `1 < h < m` dividing `m`.
    fn hint_divisor(&self, m: &BigUint) -> Option<BigUint> {
        self.hints
            .iter()
            .find(|h| **h < *m && (m % *h).is_zero())
            .cloned()
    }

    /// Adds `m`, a divisor of `parent - 1`, to the tree. The smallest hint dividing `m` splits it
    /// first. Otherwise `m` is attached as a known prime or composite, made an open composite when
    /// `known_composite`, or queued for analysis.
    fn add_part(&mut self, m: BigUint, parent: &BigUint, known_composite: bool) {
        if m <= BigUint::one() {
            return;
        }
        // A hint equal to `m` cannot split it but names a factor of `parent - 1`, so it counts as
        // used. Otherwise the largest hint of a complete factorization would be reported as
        // dividing nothing.
        if self.hints.binary_search(&m).is_ok() {
            self.hints_used.insert(m.clone());
        }
        let dividing: Vec<BigUint> = self
            .hints
            .iter()
            .filter(|h| **h < m && (&m % *h).is_zero())
            .cloned()
            .collect();
        if let Some(h) = dividing.first().cloned() {
            // The split by the smallest hint divides out its maximal power, which takes a larger
            // hint sharing a prime factor with it (4 and 8) along before that hint could split
            // anything. So every hint dividing `m` is recorded as used before the split.
            self.hints_used.extend(dividing);
            let mut rest = &m / &h;
            while (&rest % &h).is_zero() {
                rest /= &h;
            }
            self.add_part(h, parent, false);
            self.add_part(rest, parent, false);
            return;
        }
        let mut parents = BTreeSet::new();
        parents.insert(parent.clone());
        if self.nodes.contains_key(&m) {
            self.add_prime(m, &parents);
        } else if known_composite || self.composites.contains_key(&m) {
            self.add_composite(m, &parents);
        } else {
            self.queue_analyze(m, parent);
        }
    }

    /// Queues `Analyze(m)` for a part of `parent - 1`, or adds the parent to the task already
    /// queued or in flight for `m`.
    fn queue_analyze(&mut self, m: BigUint, parent: &BigUint) {
        let existing = self
            .queue
            .iter_mut()
            .map(|(_, work)| work)
            .chain(self.in_flight.values_mut())
            .find_map(|work| match work {
                Work::Analyze {
                    m: other,
                    parents: Parents::Nodes(set),
                } if *other == m => Some(set),
                _ => None,
            });
        match existing {
            Some(set) => {
                set.insert(parent.clone());
            }
            None => {
                let mut set = BTreeSet::new();
                set.insert(parent.clone());
                self.push_analyze(m, Parents::Nodes(set));
            }
        }
    }

    /// Records the prime `p` as a factor of `q - 1` for every parent `q`, and makes it a node of
    /// the tree when it needs a witness.
    fn add_prime(&mut self, p: BigUint, parents: &BTreeSet<BigUint>) {
        for parent in parents {
            if let Some(node) = self.nodes.get_mut(parent) {
                node.factors.insert(p.clone());
            }
        }
        if !self.needs_witness(&p) {
            return;
        }
        if let Some(node) = self.nodes.get_mut(&p) {
            node.parents.extend(parents.iter().cloned());
            return;
        }
        let node = Node {
            parents: parents.clone(),
            factors: BTreeSet::new(),
            root: None,
            root_task: None,
        };
        self.nodes.insert(p.clone(), node);
        self.add_part(&p - 1u32, &p, false);
    }

    /// Makes `m` an open composite under `parents` at the first stage, or adds the parents to
    /// the existing one.
    fn add_composite(&mut self, m: BigUint, parents: &BTreeSet<BigUint>) {
        if let Some(composite) = self.composites.get_mut(&m) {
            composite.parents.extend(parents.iter().cloned());
            return;
        }
        let composite = Composite {
            parents: parents.clone(),
            stage: 0,
            kind: StageKind::Pm1,
            slots: Vec::new(),
            sigma_next: 6,
        };
        self.composites.insert(m.clone(), composite);
        self.enter_stage(&m, 0);
    }

    /// The number of ECM levels the run goes through.
    fn ecm_level_count(&self) -> usize {
        let all = self.config.ecm_levels.len();
        self.config.max_ecm_levels.map_or(all, |cap| cap.min(all))
    }

    /// The stage with this index of the schedule, or `None` past the last one.
    fn stage_kind(&self, stage: usize) -> Option<StageKind> {
        let rho_tasks = self.config.rho_tasks as usize;
        if stage < rho_tasks {
            Some(StageKind::Rho {
                c: stage as u64 + 1,
            })
        } else if stage == rho_tasks {
            Some(StageKind::Pm1)
        } else {
            let level = stage - rho_tasks - 1;
            (level < self.ecm_level_count()).then_some(StageKind::Ecm { level })
        }
    }

    /// Moves the composite `m` to the stage `stage`, skipping stages without tasks. Past the
    /// last stage the composite is exhausted and the run fails.
    fn enter_stage(&mut self, m: &BigUint, stage: usize) {
        let mut stage = stage;
        loop {
            let Some(kind) = self.stage_kind(stage) else {
                let message = match self.ecm_level_count().checked_sub(1) {
                    Some(last) => format!(
                        "no factor found up to ECM level {} digits",
                        self.config.ecm_levels[last].digits
                    ),
                    None => {
                        "no factor found by Pollard rho and p-1 (no ECM level enabled)".to_string()
                    }
                };
                self.end(Status::Failed, message);
                return;
            };
            let Some(composite) = self.composites.get_mut(m) else {
                return;
            };
            let slots = build_slots(&self.config, kind, &mut composite.sigma_next);
            composite.stage = stage;
            composite.kind = kind;
            if slots.is_empty() {
                stage += 1;
                continue;
            }
            composite.slots = slots;
            return;
        }
    }

    /// The task for a queued item, or `None` for a `Root` whose prime is gone.
    fn issue(&self, id: u32, work: &Work) -> Option<Task> {
        match work {
            Work::Analyze { m, .. } => Some(Task::Analyze {
                id,
                m: m.clone(),
                trial_bound: self.config.trial_bound,
            }),
            Work::Root { q } => {
                let node = self.nodes.get(q)?;
                Some(Task::Root {
                    id,
                    q: q.clone(),
                    factors: node.factors.iter().cloned().collect(),
                    bound: self.config.root_bound,
                    hint: self.root_hints.get(q).cloned(),
                })
            }
            Work::Verify { cert } => Some(Task::Verify {
                id,
                cert: cert.clone(),
                witness_bound: self.config.witness_bound,
                term: self.term.clone(),
            }),
            Work::Factor { .. } => None,
        }
    }

    /// Hands out up to `max` tasks of the composites at the lowest stage that still has
    /// unassigned work, by ascending value.
    fn issue_factor_tasks(&mut self, max: usize, tasks: &mut Vec<Task>) {
        let Some(stage) = self
            .composites
            .values()
            .filter(|c| c.has_unassigned())
            .map(|c| c.stage)
            .min()
        else {
            return;
        };
        let values: Vec<BigUint> = self
            .composites
            .iter()
            .filter(|(_, c)| c.stage == stage && c.has_unassigned())
            .map(|(m, _)| m.clone())
            .collect();
        let mut issued = 0;
        for m in values {
            let Some(composite) = self.composites.get_mut(&m) else {
                continue;
            };
            let kind = composite.kind;
            for slot in &mut composite.slots {
                if issued == max {
                    return;
                }
                if slot.state != SlotState::Unassigned {
                    continue;
                }
                let id = self.next_id;
                self.next_id += 1;
                slot.state = SlotState::InFlight { id, done: 0 };
                tasks.push(factor_task(&self.config, kind, &m, slot, id));
                self.in_flight.insert(id, Work::Factor { m: m.clone() });
                issued += 1;
            }
        }
    }

    /// Takes an `Analyze` result after checking that its parts multiply back to `m`.
    fn on_analyzed(&mut self, m: &BigUint, parents: Parents, small: &[(u64, u32)], rest: &Rest) {
        let mut product = rest_value(rest);
        for &(p, e) in small {
            product *= BigUint::from(p).pow(e);
        }
        if product != *m {
            self.end(
                Status::Failed,
                format!("internal error: the analysis of {m} does not multiply back to it"),
            );
            return;
        }
        match parents {
            Parents::Input => self.on_input_analyzed(small, rest),
            Parents::Nodes(set) => {
                if set.is_empty() {
                    return;
                }
                for &(p, _) in small {
                    self.add_prime(BigUint::from(p), &set);
                }
                match rest {
                    Rest::One => {}
                    Rest::Prime { value } => self.add_prime(value.clone(), &set),
                    Rest::Composite { value, .. } => self.add_composite(value.clone(), &set),
                    Rest::Power { base, .. } => {
                        for parent in &set {
                            self.add_part(base.clone(), parent, false);
                        }
                    }
                }
            }
        }
    }

    /// Makes a prime input the root of the tree, or reports why it is composite.
    fn on_input_analyzed(&mut self, small: &[(u64, u32)], rest: &Rest) {
        let n = self.n.clone();
        let prime = match (small, rest) {
            ([], Rest::Prime { value }) => *value == n,
            ([(p, 1)], Rest::One) => BigUint::from(*p) == n,
            _ => false,
        };
        if prime {
            if self.needs_witness(&n) {
                let node = Node {
                    parents: BTreeSet::new(),
                    factors: BTreeSet::new(),
                    root: None,
                    root_task: None,
                };
                self.nodes.insert(n.clone(), node);
                self.add_part(&n - 1u32, &n, false);
            }
            return;
        }
        let message = if let Some(&(p, _)) = small.first() {
            let d = BigUint::from(p);
            split_message(&n, &d, &(&n / &d))
        } else {
            match rest {
                Rest::Composite {
                    witness: Some(a), ..
                } => format!("Miller–Rabin base {a} shows {n} is composite"),
                Rest::Power { base, exp } => format!("{n} = {base}^{exp}"),
                _ => format!("{n} is composite"),
            }
        };
        self.end(Status::Composite, message);
    }

    /// Splits the composite `m` by the divisor `d` under every parent, after checking `d`.
    fn on_divisor(&mut self, id: u32, m: &BigUint, d: &BigUint) {
        if arith::nontrivial_divisor(m, d.clone()).is_none() {
            self.end(
                Status::Failed,
                format!("internal error: task {id} returned {d}, which is not a nontrivial divisor of {m}"),
            );
            return;
        }
        let Some(composite) = self.composites.remove(m) else {
            return;
        };
        let e = m / d;
        for parent in &composite.parents {
            self.add_part(d.clone(), parent, false);
            self.add_part(e.clone(), parent, false);
        }
    }

    /// Marks the task `id` of the composite `m` done and advances the composite when its stage
    /// is complete.
    fn on_no_factor(&mut self, id: u32, m: &BigUint) {
        let Some(composite) = self.composites.get_mut(m) else {
            return;
        };
        let Some(slot) = composite.slots.iter_mut().find(
            |slot| matches!(slot.state, SlotState::InFlight { id: slot_id, .. } if slot_id == id),
        ) else {
            return;
        };
        slot.state = SlotState::Done;
        if composite.is_done() {
            let next = composite.stage + 1;
            self.enter_stage(m, next);
        }
    }

    /// Records the root of `q`, or, when none was found, turns `q` into a composite part of its
    /// parents again.
    fn on_root(&mut self, id: u32, q: &BigUint, root: Option<u64>) {
        let is_input = match self.nodes.get_mut(q) {
            Some(node) if node.root_task == Some(id) => {
                node.root_task = None;
                node.parents.is_empty()
            }
            _ => return,
        };
        match root {
            Some(a) => {
                if let Some(node) = self.nodes.get_mut(q) {
                    node.root = Some(a);
                }
            }
            None if is_input => {
                let bound = self.config.root_bound;
                self.end(
                    Status::Failed,
                    format!("{q} has no primitive root up to {bound}, so it is probably composite"),
                );
            }
            None => {
                let parents = self.detach_node(q);
                for parent in &parents {
                    self.cancel_root(parent);
                    self.add_part(q.clone(), parent, true);
                }
            }
        }
    }

    /// Removes the node `q` and everything only it holds: the nodes of its factors that lose
    /// their last parent (recursively), and the composites and queued analyses under it alone.
    /// Returns the parents of `q`, whose factor sets no longer contain it.
    fn detach_node(&mut self, q: &BigUint) -> BTreeSet<BigUint> {
        let Some(node) = self.nodes.remove(q) else {
            return BTreeSet::new();
        };
        for parent in &node.parents {
            if let Some(p) = self.nodes.get_mut(parent) {
                p.factors.remove(q);
            }
        }
        for f in &node.factors {
            let orphaned = match self.nodes.get_mut(f) {
                Some(child) => {
                    child.parents.remove(q);
                    child.parents.is_empty()
                }
                None => false,
            };
            if orphaned {
                self.detach_node(f);
            }
        }
        let mut gone = Vec::new();
        for (m, composite) in &mut self.composites {
            composite.parents.remove(q);
            if composite.parents.is_empty() {
                gone.push(m.clone());
            }
        }
        for m in gone {
            self.composites.remove(&m);
        }
        self.queue.retain_mut(|(_, work)| match work {
            Work::Analyze {
                parents: Parents::Nodes(set),
                ..
            } => {
                set.remove(q);
                !set.is_empty()
            }
            Work::Root { q: other } => other != q,
            _ => true,
        });
        for work in self.in_flight.values_mut() {
            if let Work::Analyze {
                parents: Parents::Nodes(set),
                ..
            } = work
            {
                set.remove(q);
            }
        }
        node.parents
    }

    /// Forgets the root of `p` and its queued `Root` task, because its factor list changed. A
    /// `Root` task in flight is discarded on arrival, since its id no longer matches.
    fn cancel_root(&mut self, p: &BigUint) {
        let Some(node) = self.nodes.get_mut(p) else {
            return;
        };
        node.root = None;
        if let Some(id) = node.root_task.take() {
            self.queue.retain(|(queued, _)| *queued != id);
        }
    }

    /// Queues a `Root` task for every prime whose `q - 1` is fully factored and that has
    /// neither a root nor a `Root` task.
    fn schedule_roots(&mut self) {
        let ready: Vec<BigUint> = self
            .nodes
            .iter()
            .filter(|(q, node)| {
                node.root.is_none() && node.root_task.is_none() && !self.has_open_parts(q)
            })
            .map(|(q, _)| q.clone())
            .collect();
        for q in ready {
            let id = self.fresh_id();
            if let Some(node) = self.nodes.get_mut(&q) {
                node.root_task = Some(id);
            }
            self.queue.push_back((id, Work::Root { q }));
        }
    }

    /// Whether a part of `q - 1` is still being analyzed or factored.
    fn has_open_parts(&self, q: &BigUint) -> bool {
        self.works().any(|work| matches!(work, Work::Analyze { parents: Parents::Nodes(set), .. } if set.contains(q)))
            || self.composites.values().any(|c| c.parents.contains(q))
    }

    /// Builds the certificate once every prime of the tree has its root and queues its check,
    /// whose result ends the run. The `Verify` task is the one task queued or in flight from
    /// then on, so the check is queued once.
    fn try_finish(&mut self) {
        if !self.queue.is_empty() || !self.in_flight.is_empty() || !self.composites.is_empty() {
            return;
        }
        if self.nodes.values().any(|node| node.root.is_none()) {
            return;
        }
        match self.build_certificate() {
            Ok(cert) => {
                let id = self.fresh_id();
                self.queue.push_back((id, Work::Verify { cert }));
            }
            Err(message) => self.end(Status::Failed, message),
        }
    }

    /// Keeps the texts of the checked certificate and ends the run as certified.
    fn on_verified(&mut self, cert: &Certificate, outputs: Vec<Output>) {
        self.outputs = outputs;
        let entries = match cert.entries.len() {
            1 => "1 witness entry".to_string(),
            k => format!("{k} witness entries"),
        };
        self.end(
            Status::Certified,
            format!("{} is prime ({entries})", self.n),
        );
    }

    fn is_verifying(&self) -> bool {
        self.works().any(|work| matches!(work, Work::Verify { .. }))
    }

    /// The work queued or in flight.
    fn works(&self) -> impl Iterator<Item = &Work> {
        self.queue
            .iter()
            .map(|(_, work)| work)
            .chain(self.in_flight.values())
    }

    /// The certificate with an entry for each prime reachable from the input, the input first,
    /// then descending.
    fn build_certificate(&self) -> Result<Certificate, String> {
        let mut entries = Vec::new();
        if self.nodes.contains_key(&self.n) {
            let mut seen = BTreeSet::new();
            let mut stack = vec![self.n.clone()];
            while let Some(q) = stack.pop() {
                if !seen.insert(q.clone()) {
                    continue;
                }
                if let Some(node) = self.nodes.get(&q) {
                    stack.extend(
                        node.factors
                            .iter()
                            .filter(|f| self.nodes.contains_key(*f))
                            .cloned(),
                    );
                }
            }
            for q in seen.iter().rev() {
                let node = &self.nodes[q];
                let root = node
                    .root
                    .ok_or_else(|| format!("internal error: {q} has no primitive root"))?;
                entries.push(Entry {
                    q: q.clone(),
                    root,
                    factors: node.factors.iter().cloned().collect(),
                });
            }
        }
        Ok(Certificate {
            n: self.n.clone(),
            entries,
        })
    }

    fn prime_view(&self, q: &BigUint) -> PrimeView {
        let node = &self.nodes[q];
        let state = if node.root.is_some() {
            "done"
        } else if node.root_task.is_some() {
            "rooting"
        } else {
            "factoring"
        };
        let mut open = Vec::new();
        let analyzing = self.works().filter_map(|work| match work {
            Work::Analyze {
                m,
                parents: Parents::Nodes(set),
            } if set.contains(q) => Some(m),
            _ => None,
        });
        for m in analyzing {
            open.push(CompositeView {
                value: m.to_string(),
                digits: arith::digits(m),
                stage: "analyzing".to_string(),
                done: 0,
                total: 1,
            });
        }
        for (m, composite) in &self.composites {
            if composite.parents.contains(q) {
                let (done, total) = composite.progress();
                open.push(CompositeView {
                    value: m.to_string(),
                    digits: arith::digits(m),
                    stage: self.stage_name(composite.kind),
                    done,
                    total,
                });
            }
        }
        PrimeView {
            value: q.to_string(),
            digits: arith::digits(q),
            state: state.to_string(),
            root: node.root,
            factors: node.factors.iter().map(ToString::to_string).collect(),
            open,
        }
    }

    /// The snapshot's `level` and `searched_digits`.
    fn level_view(&self) -> (Option<LevelView>, u32) {
        let Some(stage) = self.composites.values().map(|c| c.stage).min() else {
            return (None, 0);
        };
        let mut done = 0;
        let mut total = 0;
        let mut kind = None;
        for composite in self.composites.values().filter(|c| c.stage == stage) {
            let (d, t) = composite.progress();
            done += d;
            total += t;
            kind = Some(composite.kind);
        }
        let level = kind.map(|kind| LevelView {
            name: self.level_name(kind),
            done,
            total,
            unit: if matches!(kind, StageKind::Ecm { .. }) {
                "curves"
            } else {
                "tasks"
            }
            .to_string(),
        });
        let first_ecm_stage = self.config.rho_tasks as usize + 1;
        let finished_levels = self
            .composites
            .values()
            .map(|c| c.stage.saturating_sub(first_ecm_stage))
            .min()
            .unwrap_or(0);
        let searched = finished_levels
            .checked_sub(1)
            .and_then(|last| self.config.ecm_levels.get(last))
            .map_or(0, |level| level.digits);
        (level, searched)
    }

    /// The message of a running snapshot. The front ends append the composite and task counts.
    fn running_message(&self) -> String {
        if self.is_verifying() {
            "verifying the certificate".to_string()
        } else if self.nodes.is_empty() && self.composites.is_empty() {
            format!("analyzing {}", self.n)
        } else {
            format!("{} in the tree", plural(self.nodes.len(), "prime"))
        }
    }

    /// The stage name of a composite view.
    fn stage_name(&self, kind: StageKind) -> String {
        match kind {
            StageKind::Rho { .. } => "rho".to_string(),
            StageKind::Pm1 => "p-1".to_string(),
            StageKind::Ecm { level } => {
                let level = &self.config.ecm_levels[level];
                format!("ecm {} digits (B1 = {})", level.digits, level.b1)
            }
        }
    }

    /// The name of a level view.
    fn level_name(&self, kind: StageKind) -> String {
        match kind {
            StageKind::Rho { c } => format!("Pollard rho (c = {c})"),
            StageKind::Pm1 => format!("Pollard p-1 (B1 = {})", self.config.pm1_b1),
            StageKind::Ecm { level } => {
                let level = &self.config.ecm_levels[level];
                format!(
                    "ECM for factors up to {} digits (B1 = {})",
                    level.digits, level.b1
                )
            }
        }
    }
}

/// The tasks of a stage. An ECM level is cut into tasks of `curves_per_task` curves (the last
/// one smaller), with consecutive `sigma` values from the composite's counter.
fn build_slots(config: &Config, kind: StageKind, sigma_next: &mut u64) -> Vec<Slot> {
    match kind {
        StageKind::Rho { .. } | StageKind::Pm1 => vec![Slot {
            units: 1,
            sigma_start: 0,
            state: SlotState::Unassigned,
        }],
        StageKind::Ecm { level } => {
            let level = &config.ecm_levels[level];
            let per_task = level.curves_per_task.max(1);
            let mut slots = Vec::new();
            let mut remaining = level.curves;
            while remaining > 0 {
                let curves = remaining.min(per_task);
                slots.push(Slot {
                    units: curves,
                    sigma_start: *sigma_next,
                    state: SlotState::Unassigned,
                });
                *sigma_next += u64::from(curves);
                remaining -= curves;
            }
            slots
        }
    }
}

fn factor_task(config: &Config, kind: StageKind, m: &BigUint, slot: &Slot, id: u32) -> Task {
    match kind {
        StageKind::Rho { c } => Task::Rho {
            id,
            m: m.clone(),
            c,
            steps: config.rho_steps,
        },
        StageKind::Pm1 => Task::Pm1 {
            id,
            m: m.clone(),
            b1: config.pm1_b1,
            b2: config.pm1_b2,
        },
        StageKind::Ecm { level } => {
            let level = &config.ecm_levels[level];
            Task::Ecm {
                id,
                m: m.clone(),
                b1: level.b1,
                b2: level.b2,
                sigma_start: slot.sigma_start,
                curves: slot.units,
            }
        }
    }
}

/// The cofactor an `Analyze` result describes, as a number.
fn rest_value(rest: &Rest) -> BigUint {
    match rest {
        Rest::One => BigUint::one(),
        Rest::Prime { value } | Rest::Composite { value, .. } => value.clone(),
        Rest::Power { base, exp } => base.pow(*exp),
    }
}

/// The report of a split `n = d × e`, the smaller factor first.
fn split_message(n: &BigUint, d: &BigUint, e: &BigUint) -> String {
    let (d, e) = if d <= e { (d, e) } else { (e, d) };
    format!("{n} = {d} × {e}")
}

/// `count` followed by `noun`, which gets an `s` unless `count` is 1 ("1 prime", "2 primes").
pub fn plural(count: usize, noun: &str) -> String {
    if count == 1 {
        format!("1 {noun}")
    } else {
        format!("{count} {noun}s")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::targets::mathlib;

    fn big(s: &str) -> BigUint {
        BigUint::parse_bytes(s.as_bytes(), 10).expect("a decimal literal")
    }

    /// A worker's `Verified` answer for `cert`, with the Mathlib text alone. The driver keeps
    /// whatever texts the worker sends.
    fn verified(cert: &Certificate) -> Outcome {
        let input = parse_input(&cert.n.to_string(), usize::MAX).unwrap();
        Outcome::Verified {
            outputs: vec![mathlib::TARGET.output(cert, &input).unwrap()],
        }
    }

    /// The Mathlib file of `snap`, if any.
    fn mathlib_code(snap: &Snapshot) -> Option<&str> {
        snap.outputs
            .iter()
            .find(|output| output.target == mathlib::TARGET.name)
            .map(|output| output.code.as_str())
    }

    /// The number a task is about.
    fn number(task: &Task) -> &BigUint {
        match task {
            Task::Analyze { m, .. }
            | Task::Rho { m, .. }
            | Task::Pm1 { m, .. }
            | Task::Ecm { m, .. } => m,
            Task::Root { q, .. } => q,
            Task::Verify { cert, .. } => &cert.n,
        }
    }

    fn kind(task: &Task) -> &'static str {
        match task {
            Task::Analyze { .. } => "Analyze",
            Task::Rho { .. } => "Rho",
            Task::Pm1 { .. } => "Pm1",
            Task::Ecm { .. } => "Ecm",
            Task::Root { .. } => "Root",
            Task::Verify { .. } => "Verify",
        }
    }

    /// A certificate as `n=N;q:root:[factors];…`, for the task descriptions.
    fn flat(cert: &Certificate) -> String {
        let mut text = format!("n={}", cert.n);
        for entry in &cert.entries {
            let factors: Vec<String> = entry.factors.iter().map(ToString::to_string).collect();
            text.push_str(&format!(
                ";{}:{}:[{}]",
                entry.q,
                entry.root,
                factors.join(",")
            ));
        }
        text
    }

    /// A one-line description of a task, for comparing schedules.
    fn describe(task: &Task) -> String {
        match task {
            Task::Analyze { m, .. } => format!("Analyze {m}"),
            Task::Rho { m, c, .. } => format!("Rho {m} c={c}"),
            Task::Pm1 { m, .. } => format!("Pm1 {m}"),
            Task::Ecm {
                m,
                b1,
                sigma_start,
                curves,
                ..
            } => format!("Ecm {m} b1={b1} sigma={sigma_start} curves={curves}"),
            Task::Root {
                q, factors, hint, ..
            } => {
                let factors: Vec<String> = factors.iter().map(ToString::to_string).collect();
                let hint = hint
                    .as_ref()
                    .map_or(String::new(), |a| format!(" hint={a}"));
                format!("Root {q} [{}]{hint}", factors.join(","))
            }
            Task::Verify { cert, .. } => format!("Verify {}", flat(cert)),
        }
    }

    fn trace(log: &[Task]) -> Vec<String> {
        log.iter().map(describe).collect()
    }

    /// The certificate of the one `Verify` task in `log`, as `flat` writes it.
    fn certificate(log: &[Task]) -> String {
        let mut certs = log.iter().filter_map(|task| match task {
            Task::Verify { cert, .. } => Some(cert),
            _ => None,
        });
        let cert = certs.next().expect("a Verify task");
        assert!(certs.next().is_none(), "more than one Verify task");
        flat(cert)
    }

    /// A fake executor. It answers a task with the next outcome queued under its kind and number,
    /// and logs every task. A factoring task with no outcome left gets `NoFactor` and a `Verify`
    /// task `Verified`; an `Analyze` or `Root` task with none is a test error.
    struct Table {
        answers: BTreeMap<(&'static str, BigUint), VecDeque<Outcome>>,
        log: Vec<Task>,
    }

    impl Table {
        fn new() -> Table {
            Table {
                answers: BTreeMap::new(),
                log: Vec::new(),
            }
        }

        fn add(&mut self, kind: &'static str, n: &str, outcome: Outcome) -> &mut Table {
            self.answers
                .entry((kind, big(n)))
                .or_default()
                .push_back(outcome);
            self
        }

        fn exec(&mut self, task: &Task) -> TaskResult {
            self.log.push(task.clone());
            let key = (kind(task), number(task).clone());
            let outcome = match self.answers.get_mut(&key).and_then(VecDeque::pop_front) {
                Some(outcome) => outcome,
                None => match task {
                    Task::Rho { .. } | Task::Pm1 { .. } | Task::Ecm { .. } => no_factor(),
                    Task::Verify { cert, .. } => verified(cert),
                    _ => panic!("no answer for {}", describe(task)),
                },
            };
            TaskResult {
                id: task.id(),
                outcome,
            }
        }

        /// Runs one task of `driver` and returns its description.
        fn step(&mut self, driver: &mut Driver) -> String {
            let task = driver.take_tasks(1).pop().expect("a task");
            let result = self.exec(&task);
            driver.submit(result);
            describe(&task)
        }

        fn run(&mut self, driver: &mut Driver) -> Snapshot {
            driver.run_with(&mut |task| self.exec(task))
        }
    }

    fn analyzed(small: &[(u64, u32)], rest: Rest) -> Outcome {
        Outcome::Analyzed {
            small: small.to_vec(),
            rest,
        }
    }

    fn prime(s: &str) -> Rest {
        Rest::Prime { value: big(s) }
    }

    fn composite(s: &str) -> Rest {
        Rest::Composite {
            value: big(s),
            witness: Some(2),
        }
    }

    fn divisor(s: &str) -> Outcome {
        Outcome::Divisor { d: big(s) }
    }

    fn no_factor() -> Outcome {
        Outcome::NoFactor
    }

    fn root(a: u64) -> Outcome {
        Outcome::Root { root: Some(a) }
    }

    /// A driver for `n`. `hints` are hint tokens (`"1009"`, `"1009:11"`).
    fn driver(n: &str, hints: &[&str], config: Config) -> Driver {
        let hints = crate::hints::parse_hints(&hints.join(" "));
        Driver::new(n, hints, config).expect("a valid input")
    }

    /// Trial division to 100 only and the witness bound 1000, so that four-digit primes are
    /// "large", and two ECM levels.
    fn config() -> Config {
        Config {
            witness_bound: 1000,
            trial_bound: 100,
            max_ecm_levels: Some(2),
            ..Config::default()
        }
    }

    /// `N1 - 1 = 2^15 · 1009 · 1013`: a prime whose cofactor `C1` is split by rho.
    const N1: &str = "33492729857";
    const N1_MINUS_1: &str = "33492729856";
    const C1: &str = "1022117";
    const N1_CERT: &str =
        "n=33492729857;33492729857:3:[2,1009,1013];1013:3:[2,11,23];1009:11:[2,3,7]";

    fn two_level_table() -> Table {
        let mut t = Table::new();
        t.add("Analyze", N1, analyzed(&[], prime(N1)))
            .add("Analyze", N1_MINUS_1, analyzed(&[(2, 15)], composite(C1)))
            .add("Rho", C1, no_factor())
            .add("Rho", C1, divisor("1009"))
            .add("Analyze", "1009", analyzed(&[], prime("1009")))
            .add("Analyze", "1013", analyzed(&[], prime("1013")))
            .add(
                "Analyze",
                "1008",
                analyzed(&[(2, 4), (3, 2), (7, 1)], Rest::One),
            )
            .add(
                "Analyze",
                "1012",
                analyzed(&[(2, 2), (11, 1), (23, 1)], Rest::One),
            )
            .add("Root", "1009", root(11))
            .add("Root", "1013", root(3))
            .add("Root", N1, root(3));
        t
    }

    #[test]
    fn certifies_65537_with_one_entry() {
        let mut table = Table::new();
        table
            .add("Analyze", "65537", analyzed(&[], prime("65537")))
            .add("Analyze", "65536", analyzed(&[(2, 16)], Rest::One))
            .add("Root", "65537", root(3));
        let mut d = driver("65537", &[], Config::default());
        assert!(!d.is_finished());
        let snap = table.run(&mut d);
        assert!(d.is_finished());
        assert_eq!(snap.status, "certified");
        assert_eq!(certificate(&table.log), "n=65537;65537:3:[2]");
        assert_eq!(
            mathlib_code(&snap),
            Some(
                "import Mathlib.Tactic.Primality\n\nexample : Nat.Prime 65537 := by\n  \
                 primality (cert := .witnesses [\n    .lucas { root := 3, primeFactors := [2] }])\n"
            )
        );
        assert_eq!(snap.message, "65537 is prime (1 witness entry)");
        assert_eq!(
            trace(&table.log),
            [
                "Analyze 65537",
                "Analyze 65536",
                "Root 65537 [2]",
                "Verify n=65537;65537:3:[2]"
            ]
        );
        let ids: Vec<u32> = table.log.iter().map(Task::id).collect();
        assert_eq!(ids, [1, 2, 3, 4]);
        assert!(matches!(
            table.log[3],
            Task::Verify {
                witness_bound: 1024,
                ..
            }
        ));
        assert_eq!(snap.input, "65537");
        assert_eq!(snap.primes.len(), 1);
        let p = &snap.primes[0];
        assert_eq!(p.value, "65537");
        assert_eq!(p.digits, 5);
        assert_eq!(p.state, "done");
        assert_eq!(p.root, Some(3));
        assert_eq!(p.factors, ["2"]);
        assert!(p.open.is_empty());
        assert!(snap.level.is_none());
        assert_eq!(snap.searched_digits, 0);
        assert_eq!(snap.open_composites, 0);
        assert_eq!(snap.tasks_in_flight, 0);
        assert!(snap.hints_used.is_empty() && snap.hints_unused.is_empty());
        assert!(d.take_tasks(5).is_empty());
    }

    #[test]
    fn primes_below_the_witness_bound_get_an_empty_certificate() {
        let mut table = Table::new();
        table.add("Analyze", "7", analyzed(&[(7, 1)], Rest::One));
        let snap = table.run(&mut driver("7", &[], Config::default()));
        assert_eq!(snap.status, "certified");
        assert_eq!(certificate(&table.log), "n=7");
        assert_eq!(
            mathlib_code(&snap),
            Some("import Mathlib.Tactic.Primality\n\nexample : Nat.Prime 7 := by primality\n")
        );
        assert!(snap.primes.is_empty());
        // A small prime at or above the bound found by trial division is the root node.
        let mut table = Table::new();
        table
            .add("Analyze", "1033", analyzed(&[(1033, 1)], Rest::One))
            .add(
                "Analyze",
                "1032",
                analyzed(&[(2, 3), (3, 1), (43, 1)], Rest::One),
            )
            .add("Root", "1033", root(5));
        let snap = table.run(&mut driver("1033", &[], Config::default()));
        assert_eq!(snap.status, "certified");
        assert_eq!(certificate(&table.log), "n=1033;1033:5:[2,3,43]");
        assert_eq!(trace(&table.log)[2], "Root 1033 [2,3,43]");
    }

    #[test]
    fn two_level_tree_is_factored_analyzed_and_rooted() {
        let mut table = two_level_table();
        let mut d = driver(N1, &[], config());
        assert_eq!(table.step(&mut d), format!("Analyze {N1}"));
        let snap = d.snapshot();
        assert_eq!(snap.status, "running");
        assert_eq!(snap.message, "1 prime in the tree");
        assert_eq!(snap.primes[0].state, "factoring");
        assert_eq!(snap.primes[0].open.len(), 1);
        assert_eq!(snap.primes[0].open[0].stage, "analyzing");
        assert_eq!(snap.primes[0].open[0].value, N1_MINUS_1);
        assert!(snap.level.is_none());
        assert_eq!(table.step(&mut d), format!("Analyze {N1_MINUS_1}"));
        let snap = d.snapshot();
        assert_eq!(snap.primes[0].factors, ["2"]);
        assert_eq!(snap.open_composites, 1);
        let open = &snap.primes[0].open[0];
        assert_eq!((open.value.as_str(), open.stage.as_str()), (C1, "rho"));
        assert_eq!((open.done, open.total), (0, 1));
        let level = snap.level.expect("a level");
        assert_eq!(level.name, "Pollard rho (c = 1)");
        assert_eq!((level.done, level.total), (0, 1));
        assert_eq!(level.unit, "tasks");
        assert_eq!(table.step(&mut d), format!("Rho {C1} c=1"));
        assert_eq!(
            d.snapshot().level.expect("a level").name,
            "Pollard rho (c = 2)"
        );
        assert_eq!(table.step(&mut d), format!("Rho {C1} c=2"));
        let snap = d.snapshot();
        assert_eq!(snap.open_composites, 0);
        let analyzing: Vec<&str> = snap.primes[0]
            .open
            .iter()
            .map(|c| c.value.as_str())
            .collect();
        assert_eq!(analyzing, ["1009", "1013"]);
        let snap = table.run(&mut d);
        assert_eq!(snap.status, "certified");
        assert_eq!(certificate(&table.log), N1_CERT);
        assert_eq!(
            trace(&table.log),
            [
                format!("Analyze {N1}"),
                format!("Analyze {N1_MINUS_1}"),
                format!("Rho {C1} c=1"),
                format!("Rho {C1} c=2"),
                "Analyze 1009".to_string(),
                "Analyze 1013".to_string(),
                "Analyze 1008".to_string(),
                "Analyze 1012".to_string(),
                // `N1 - 1` is fully factored once 1009 and 1013 are known prime, before their
                // own `q - 1` are, so the input's root comes first.
                format!("Root {N1} [2,1009,1013]"),
                "Root 1009 [2,3,7]".to_string(),
                "Root 1013 [2,11,23]".to_string(),
                format!("Verify {N1_CERT}"),
            ]
        );
        let values: Vec<&str> = snap.primes.iter().map(|p| p.value.as_str()).collect();
        assert_eq!(values, [N1, "1013", "1009"]);
        assert!(snap.primes.iter().all(|p| p.state == "done"));
        assert_eq!(snap.primes[0].factors, ["2", "1009", "1013"]);
    }

    #[test]
    fn a_hint_splits_a_part_before_it_is_analyzed() {
        let mut table = two_level_table();
        table.add("Analyze", "33193984", analyzed(&[(2, 15)], prime("1013")));
        let mut d = driver(N1, &["999983", "1009"], config());
        let snap = table.run(&mut d);
        assert_eq!(snap.status, "certified");
        assert_eq!(certificate(&table.log), N1_CERT);
        assert_eq!(snap.hints_used, ["1009"]);
        assert_eq!(snap.hints_unused, ["999983"]);
        let log = trace(&table.log);
        assert!(
            !log.iter().any(|t| t.contains(N1_MINUS_1) || t.contains(C1)),
            "{log:?}"
        );
        assert_eq!(log[1], "Analyze 1009");
        assert_eq!(log[2], "Analyze 33193984");
        // A hint is divided out to its maximal power, so `2^16` yields one analysis of 2.
        let mut table = Table::new();
        table
            .add("Analyze", "65537", analyzed(&[], prime("65537")))
            .add("Analyze", "2", analyzed(&[(2, 1)], Rest::One))
            .add("Root", "65537", root(3));
        let snap = table.run(&mut driver("65537", &["2"], Config::default()));
        assert_eq!(snap.status, "certified");
        assert_eq!(
            trace(&table.log),
            [
                "Analyze 65537",
                "Analyze 2",
                "Root 65537 [2]",
                "Verify n=65537;65537:3:[2]"
            ]
        );
        assert_eq!(snap.hints_used, ["2"]);
    }

    #[test]
    fn a_root_hint_rides_on_the_root_task_of_its_prime() {
        // The previous test's run with the root hint 11 for 1009, which only the `Root` task of
        // 1009 carries.
        let mut table = two_level_table();
        table.add("Analyze", "33193984", analyzed(&[(2, 15)], prime("1013")));
        let mut d = driver(N1, &["1009:11", "999983:2"], config());
        assert_eq!(
            d.root_hints,
            BTreeMap::from([(big("1009"), big("11")), (big("999983"), big("2"))])
        );
        let snap = table.run(&mut d);
        assert_eq!(snap.status, "certified");
        assert_eq!(certificate(&table.log), N1_CERT);
        assert_eq!(snap.hints_used, ["1009"]);
        assert_eq!(snap.hints_unused, ["999983"]);
        let roots: Vec<String> = trace(&table.log)
            .into_iter()
            .filter(|t| t.starts_with("Root"))
            .collect();
        assert_eq!(
            roots,
            [
                format!("Root {N1} [2,1009,1013]"),
                "Root 1009 [2,3,7] hint=11".to_string(),
                "Root 1013 [2,11,23]".to_string(),
            ]
        );
        let hinted = table
            .log
            .iter()
            .find(|t| matches!(t, Task::Root { q, .. } if *q == big("1009")))
            .expect("the Root task of 1009");
        assert!(matches!(hinted, Task::Root { hint: Some(a), .. } if *a == big("11")));
    }

    #[test]
    fn a_hint_equal_to_a_part_counts_as_used() {
        // The complete factorization of `N1 - 1` as hints. Dividing the smaller hints out leaves
        // 1013 as a whole part, so it never splits anything and is analyzed as it is.
        let mut table = two_level_table();
        table
            .add("Analyze", "2", analyzed(&[(2, 1)], Rest::One))
            .add("Analyze", "2", analyzed(&[(2, 1)], Rest::One))
            .add("Analyze", "63", analyzed(&[(3, 2), (7, 1)], Rest::One))
            .add("Analyze", "253", analyzed(&[(11, 1), (23, 1)], Rest::One));
        let mut d = driver(N1, &["2", "1009", "1013"], config());
        let snap = table.run(&mut d);
        assert_eq!(snap.status, "certified");
        assert_eq!(certificate(&table.log), N1_CERT);
        assert_eq!(snap.hints_used, ["2", "1009", "1013"]);
        assert!(snap.hints_unused.is_empty());
        assert_eq!(
            trace(&table.log),
            [
                format!("Analyze {N1}"),
                "Analyze 2".to_string(),
                "Analyze 1009".to_string(),
                "Analyze 1013".to_string(),
                "Analyze 2".to_string(),
                "Analyze 63".to_string(),
                "Analyze 253".to_string(),
                format!("Root {N1} [2,1009,1013]"),
                "Root 1009 [2,3,7]".to_string(),
                "Root 1013 [2,11,23]".to_string(),
                format!("Verify {N1_CERT}"),
            ]
        );
    }

    #[test]
    fn every_hint_dividing_a_part_counts_as_used() {
        // 8 divides 65536 but shares its prime with 4, which splits 65536 and takes the 8 along.
        let mut table = Table::new();
        table
            .add("Analyze", "65537", analyzed(&[], prime("65537")))
            .add("Analyze", "4", analyzed(&[(2, 2)], Rest::One))
            .add("Root", "65537", root(3));
        let snap = table.run(&mut driver("65537", &["4", "8"], Config::default()));
        assert_eq!(snap.status, "certified");
        assert_eq!(snap.hints_used, ["4", "8"]);
        assert!(snap.hints_unused.is_empty());
        assert_eq!(
            trace(&table.log),
            [
                "Analyze 65537",
                "Analyze 4",
                "Root 65537 [2]",
                "Verify n=65537;65537:3:[2]"
            ]
        );
    }

    #[test]
    fn an_invalid_divisor_fails_the_run() {
        for bad in ["7", C1, "1"] {
            let mut table = Table::new();
            table
                .add("Analyze", N1, analyzed(&[], prime(N1)))
                .add("Analyze", N1_MINUS_1, analyzed(&[(2, 15)], composite(C1)))
                .add("Rho", C1, divisor(bad));
            let mut d = driver(N1, &[], config());
            let snap = table.run(&mut d);
            assert!(d.is_finished());
            assert_eq!(snap.status, "failed", "{bad}");
            assert!(
                snap.message.starts_with("internal error"),
                "{}",
                snap.message
            );
            assert!(snap.message.contains(bad), "{}", snap.message);
            assert_eq!(table.log.len(), 3);
            assert!(snap.outputs.is_empty());
        }
    }

    /// `N2 - 1 = 2 · P1 · 1019 · 1031 · 1087` and `P1 - 1 = 2 · 1009 · 1013 · 1093`, with the
    /// composites `C1 = P1 · C3`, `C3 = 1019 · C4`, `C4 = 1031 · 1087`, `C5 = 1009 · C6` and
    /// `C6 = 1013 · 1093` on the way.
    const N2: &str = "5103206689629752819";
    const N2_MINUS_1: &str = "5103206689629752818";
    const C1_2: &str = "2551603344814876409";
    const P1: &str = "2234347763";
    const P1_MINUS_1: &str = "2234347762";
    const C3: &str = "1141990243";
    const C4: &str = "1120697";
    const C5: &str = "1117173881";
    const C6: &str = "1107209";
    const N2_CERT: &str = "n=5103206689629752819;\
        5103206689629752819:2:[2,1019,1031,1087,2234347763];\
        2234347763:2:[2,1009,1013,1093];1093:5:[2,3,7,13];1087:3:[2,3,181];\
        1031:14:[2,5,103];1019:2:[2,509];1013:3:[2,11,23];1009:11:[2,3,7]";

    /// `C5` and `C3` survive rho, p-1 and the 15-digit level; `C5` splits on its first 20-digit
    /// task into 1009 and the new composite `C6`, which splits on its own first 20-digit task;
    /// then `C3` splits on its first 20-digit task into 1019 and `C4`, which rho splits at once.
    fn schedule_table() -> Table {
        let mut t = Table::new();
        t.add("Analyze", N2, analyzed(&[], prime(N2)))
            .add("Analyze", N2_MINUS_1, analyzed(&[(2, 1)], composite(C1_2)))
            .add("Rho", C1_2, no_factor())
            .add("Rho", C1_2, divisor(P1))
            .add("Analyze", P1, analyzed(&[], prime(P1)))
            .add("Analyze", C3, analyzed(&[], composite(C3)))
            .add("Analyze", P1_MINUS_1, analyzed(&[(2, 1)], composite(C5)));
        for _ in 0..5 {
            t.add("Ecm", C5, no_factor());
        }
        t.add("Ecm", C5, divisor("1009"))
            .add("Analyze", "1009", analyzed(&[], prime("1009")))
            .add("Analyze", C6, analyzed(&[], composite(C6)))
            .add(
                "Analyze",
                "1008",
                analyzed(&[(2, 4), (3, 2), (7, 1)], Rest::One),
            );
        for _ in 0..5 {
            t.add("Ecm", C6, no_factor());
        }
        t.add("Ecm", C6, divisor("1013"))
            .add("Analyze", "1013", analyzed(&[], prime("1013")))
            .add("Analyze", "1093", analyzed(&[], prime("1093")))
            .add(
                "Analyze",
                "1012",
                analyzed(&[(2, 2), (11, 1), (23, 1)], Rest::One),
            )
            .add(
                "Analyze",
                "1092",
                analyzed(&[(2, 2), (3, 1), (7, 1), (13, 1)], Rest::One),
            );
        for _ in 0..5 {
            t.add("Ecm", C3, no_factor());
        }
        t.add("Ecm", C3, divisor("1019"))
            .add("Analyze", "1019", analyzed(&[], prime("1019")))
            .add("Analyze", C4, analyzed(&[], composite(C4)))
            .add("Analyze", "1018", analyzed(&[(2, 1), (509, 1)], Rest::One))
            .add("Rho", C4, divisor("1031"))
            .add("Analyze", "1031", analyzed(&[], prime("1031")))
            .add("Analyze", "1087", analyzed(&[], prime("1087")))
            .add(
                "Analyze",
                "1030",
                analyzed(&[(2, 1), (5, 1), (103, 1)], Rest::One),
            )
            .add(
                "Analyze",
                "1086",
                analyzed(&[(2, 1), (3, 1), (181, 1)], Rest::One),
            )
            .add("Root", N2, root(2))
            .add("Root", P1, root(2))
            .add("Root", "1019", root(2))
            .add("Root", "1031", root(14))
            .add("Root", "1087", root(3))
            .add("Root", "1009", root(11))
            .add("Root", "1013", root(3))
            .add("Root", "1093", root(5));
        t
    }

    fn ecm15(m: &str, sigma: u64) -> String {
        format!("Ecm {m} b1=2000 sigma={sigma} curves=5")
    }

    fn ecm20(m: &str, sigma: u64) -> String {
        format!("Ecm {m} b1=11000 sigma={sigma} curves=3")
    }

    #[test]
    fn stages_run_in_order_and_level_synchronously() {
        let mut table = schedule_table();
        let mut d = driver(N2, &[], config());
        for _ in 0..7 {
            table.step(&mut d);
        }
        assert_eq!(d.snapshot().open_composites, 2);
        assert_eq!(d.snapshot().message, "2 primes in the tree");
        // Both composites at stage 0: rho before p-1 before ECM, the lower stage first.
        let mut expected = vec![
            format!("Rho {C5} c=1"),
            format!("Rho {C3} c=1"),
            format!("Rho {C5} c=2"),
            format!("Rho {C3} c=2"),
            format!("Pm1 {C5}"),
            format!("Pm1 {C3}"),
        ];
        expected.extend([6, 11, 16, 21, 26].map(|sigma| ecm15(C5, sigma)));
        expected.extend([6, 11, 16, 21, 26].map(|sigma| ecm15(C3, sigma)));
        let mut seen = Vec::new();
        for (i, want) in expected.iter().enumerate() {
            if i == 5 {
                let snap = d.snapshot();
                let level = snap.level.expect("a level");
                assert_eq!(level.name, "Pollard p-1 (B1 = 100000)");
                assert_eq!((level.done, level.total), (0, 1));
                assert_eq!(snap.searched_digits, 0);
            }
            if i == 11 {
                // `C5` has finished the 15-digit level, `C3` has not started it.
                let snap = d.snapshot();
                let level = snap.level.expect("a level");
                assert_eq!(level.name, "ECM for factors up to 15 digits (B1 = 2000)");
                assert_eq!((level.done, level.total), (0, 25));
                assert_eq!(snap.searched_digits, 0);
            }
            seen.push(table.step(&mut d));
            assert_eq!(&seen[i], want, "step {i}: {seen:?}");
        }
        let snap = d.snapshot();
        let level = snap.level.expect("a level");
        assert_eq!(level.name, "ECM for factors up to 20 digits (B1 = 11000)");
        assert_eq!((level.done, level.total), (0, 180));
        assert_eq!(level.unit, "curves");
        assert!(serde_json::to_string(&level)
            .unwrap()
            .contains(r#""unit":"curves""#));
        assert_eq!(snap.searched_digits, 15);
        let views: Vec<(String, String)> = snap
            .primes
            .iter()
            .flat_map(|p| p.open.iter().map(|c| (p.value.clone(), c.stage.clone())))
            .collect();
        let ecm20_stage = "ecm 20 digits (B1 = 11000)".to_string();
        assert_eq!(
            views,
            [
                (N2.to_string(), ecm20_stage.clone()),
                (P1.to_string(), ecm20_stage)
            ]
        );
        // `C5` splits; the new `C6` starts at stage 0 while `C3` waits at the 20-digit level.
        assert_eq!(table.step(&mut d), ecm20(C5, 31));
        // `C3` is the only open composite until `C6` is analyzed.
        assert_eq!(d.snapshot().searched_digits, 15);
        assert_eq!(table.step(&mut d), "Analyze 1009");
        assert_eq!(table.step(&mut d), format!("Analyze {C6}"));
        let snap = d.snapshot();
        assert_eq!(snap.open_composites, 2);
        assert_eq!(snap.searched_digits, 0);
        assert_eq!(snap.level.expect("a level").name, "Pollard rho (c = 1)");
        let snap = table.run(&mut d);
        assert_eq!(snap.status, "certified");
        assert_eq!(certificate(&table.log), N2_CERT);
        let factoring: Vec<String> = trace(&table.log[24..])
            .into_iter()
            .filter(|t| {
                !t.starts_with("Analyze") && !t.starts_with("Root") && !t.starts_with("Verify")
            })
            .collect();
        let mut expected = vec![
            format!("Rho {C6} c=1"),
            format!("Rho {C6} c=2"),
            format!("Pm1 {C6}"),
        ];
        expected.extend([6, 11, 16, 21, 26].map(|sigma| ecm15(C6, sigma)));
        expected.push(ecm20(C6, 31));
        expected.push(ecm20(C3, 31));
        expected.push(format!("Rho {C4} c=1"));
        assert_eq!(factoring, expected);
        let values: Vec<&str> = snap.primes.iter().map(|p| p.value.as_str()).collect();
        assert_eq!(
            values,
            [N2, P1, "1093", "1087", "1031", "1019", "1013", "1009"]
        );
        assert_eq!(snap.primes[1].factors, ["2", "1009", "1013", "1093"]);
    }

    #[test]
    fn parallel_tasks_come_from_one_stage_and_stale_results_are_discarded() {
        let mut table = schedule_table();
        let mut d = driver(N2, &[], config());
        for _ in 0..13 {
            table.step(&mut d);
        }
        // Both composites at the 15-digit level: all ten tasks at once, then nothing more.
        let tasks = d.take_tasks(100);
        assert_eq!(tasks.len(), 10);
        assert!(tasks
            .iter()
            .all(|t| matches!(t, Task::Ecm { b1: 2000, .. })));
        assert!(d.take_tasks(1).is_empty());
        assert_eq!(d.snapshot().tasks_in_flight, 10);
        let level = d.snapshot().level.expect("a level");
        assert_eq!((level.done, level.total), (0, 50));
        // Progress reports move the counts, capped at the task's curves.
        d.report_progress(tasks[0].id(), 3);
        d.report_progress(tasks[1].id(), 99);
        d.report_progress(4_000_000, 7);
        let snap = d.snapshot();
        assert_eq!(snap.level.expect("a level").done, 8);
        assert_eq!(snap.primes[1].open[0].done, 8);
        assert_eq!(snap.primes[1].open[0].stage, "ecm 15 digits (B1 = 2000)");
        for task in &tasks {
            d.submit(TaskResult {
                id: task.id(),
                outcome: no_factor(),
            });
        }
        assert_eq!(d.snapshot().searched_digits, 15);
        // Three 20-digit tasks of `C5`. The first splits it and returns the others as stale, and
        // their results, should they arrive, are discarded (an `Error` included).
        let tasks = d.take_tasks(3);
        assert_eq!(trace(&tasks), [ecm20(C5, 31), ecm20(C5, 34), ecm20(C5, 37)]);
        let stale = d.submit(TaskResult {
            id: tasks[0].id(),
            outcome: divisor("1009"),
        });
        assert_eq!(stale, [tasks[1].id(), tasks[2].id()]);
        assert_eq!(d.snapshot().tasks_in_flight, 0);
        d.submit(TaskResult {
            id: tasks[1].id(),
            outcome: Outcome::Error {
                message: "a crashed worker".to_string(),
            },
        });
        let snap = d.snapshot();
        assert_eq!((snap.status.as_str(), snap.tasks_in_flight), ("running", 0));
        assert_eq!(snap.open_composites, 1);
        let snap = table.run(&mut d);
        assert_eq!(snap.status, "certified");
        assert_eq!(certificate(&table.log), N2_CERT);
    }

    #[test]
    fn a_missing_root_requeues_the_prime_as_a_composite() {
        let mut table = two_level_table();
        table.answers.remove(&("Root", big("1009")));
        table.add("Root", "1009", Outcome::Root { root: None });
        let config = Config {
            max_ecm_levels: Some(0),
            ..config()
        };
        let mut d = driver(N1, &[], config);
        for _ in 0..8 {
            table.step(&mut d);
        }
        assert_eq!(table.step(&mut d), format!("Root {N1} [2,1009,1013]"));
        assert_eq!(table.step(&mut d), "Root 1009 [2,3,7]");
        let snap = d.snapshot();
        assert_eq!(snap.status, "running");
        let values: Vec<&str> = snap.primes.iter().map(|p| p.value.as_str()).collect();
        assert_eq!(values, [N1, "1013"]);
        let input = &snap.primes[0];
        assert_eq!((input.state.as_str(), input.root), ("factoring", None));
        assert_eq!(input.factors, ["2", "1013"]);
        assert_eq!(input.open.len(), 1);
        assert_eq!(
            (input.open[0].value.as_str(), input.open[0].stage.as_str()),
            ("1009", "rho")
        );
        assert_eq!(table.step(&mut d), "Root 1013 [2,11,23]");
        assert_eq!(table.step(&mut d), "Rho 1009 c=1");
        assert_eq!(table.step(&mut d), "Rho 1009 c=2");
        assert_eq!(table.step(&mut d), "Pm1 1009");
        let snap = d.snapshot();
        assert_eq!(snap.status, "failed");
        assert_eq!(
            snap.message,
            "no factor found by Pollard rho and p-1 (no ECM level enabled)"
        );
        // The factor 2 is below the bound, and 1009 left the tree with its missing root.
        assert_eq!(snap.found_factors, "1013:3\n");
        assert_eq!(table.log.iter().filter(|t| t.id() == 0).count(), 0);
        assert_eq!(
            trace(&table.log)
                .iter()
                .filter(|t| t.starts_with(&format!("Root {N1}")))
                .count(),
            1
        );
    }

    #[test]
    fn composite_inputs_are_reported() {
        for n in ["0", "1"] {
            let d = driver(n, &[], Config::default());
            assert!(d.is_finished());
            let snap = d.snapshot();
            assert_eq!(snap.status, "composite");
            assert_eq!(snap.message, format!("{n} is not prime"));
        }
        let mut table = Table::new();
        table.add("Analyze", C1, analyzed(&[(1009, 1), (1013, 1)], Rest::One));
        let snap = table.run(&mut driver(C1, &[], Config::default()));
        assert_eq!(snap.status, "composite");
        assert_eq!(snap.message, "1022117 = 1009 × 1013");
        let mut table = Table::new();
        table.add("Analyze", "1024", analyzed(&[(2, 10)], Rest::One));
        assert_eq!(
            table
                .run(&mut driver("1024", &[], Config::default()))
                .message,
            "1024 = 2 × 512"
        );
        let mut table = Table::new();
        table.add("Analyze", "1022117", analyzed(&[(1009, 1)], prime("1013")));
        assert_eq!(
            table
                .run(&mut driver("1022117", &[], Config::default()))
                .message,
            "1022117 = 1009 × 1013"
        );
        let big_composite = "1000000000100000000002379";
        let mut table = Table::new();
        table.add(
            "Analyze",
            big_composite,
            analyzed(
                &[],
                Rest::Composite {
                    value: big(big_composite),
                    witness: Some(2),
                },
            ),
        );
        let snap = table.run(&mut driver(big_composite, &[], Config::default()));
        assert_eq!(snap.status, "composite");
        assert_eq!(
            snap.message,
            format!("Miller–Rabin base 2 shows {big_composite} is composite")
        );
        let mut table = Table::new();
        table.add(
            "Analyze",
            "1000006000009",
            analyzed(
                &[],
                Rest::Power {
                    base: big("1000003"),
                    exp: 2,
                },
            ),
        );
        let snap = table.run(&mut driver("1000006000009", &[], Config::default()));
        assert_eq!(snap.status, "composite");
        assert_eq!(snap.message, "1000006000009 = 1000003^2");
        // A hint dividing the input settles it without a task.
        let mut d = driver(C1, &["1013"], Config::default());
        assert!(d.is_finished());
        assert!(d.take_tasks(5).is_empty());
        let snap = d.snapshot();
        assert_eq!(snap.status, "composite");
        assert_eq!(snap.message, "1022117 = 1009 × 1013");
        assert_eq!(snap.hints_used, ["1013"]);
        assert!(snap.outputs.is_empty());
    }

    #[test]
    fn exhausting_the_schedule_fails_and_keeps_the_factors() {
        for (levels, message) in [
            (
                0,
                "no factor found by Pollard rho and p-1 (no ECM level enabled)",
            ),
            (1, "no factor found up to ECM level 15 digits"),
        ] {
            let mut table = Table::new();
            table.add("Analyze", N1, analyzed(&[], prime(N1))).add(
                "Analyze",
                N1_MINUS_1,
                analyzed(&[(2, 15)], composite(C1)),
            );
            let config = Config {
                max_ecm_levels: Some(levels),
                ..config()
            };
            let mut d = driver(N1, &[], config);
            let snap = table.run(&mut d);
            assert!(d.is_finished());
            assert_eq!(snap.status, "failed");
            assert_eq!(snap.message, message);
            assert!(snap.outputs.is_empty());
            assert_eq!(table.log.len(), 5 + 5 * levels);
            assert_eq!(snap.primes[0].factors, ["2"]);
            assert_eq!(snap.open_composites, 1);
            assert_eq!(snap.primes[0].open[0].value, C1);
            assert!(d.take_tasks(3).is_empty());
        }
    }

    #[test]
    fn the_same_results_give_the_same_tasks() {
        let mut first = schedule_table();
        let mut second = schedule_table();
        let one = first.run(&mut driver(N2, &[], config()));
        let two = second.run(&mut driver(N2, &[], config()));
        assert_eq!(first.log, second.log);
        assert_eq!(first.log.len(), 58);
        assert_eq!(one.outputs, two.outputs);
        assert!(!one.outputs.is_empty());
        assert_eq!(
            serde_json::to_string(&one).unwrap(),
            serde_json::to_string(&two).unwrap()
        );
    }

    #[test]
    fn take_tasks_is_never_empty_while_idle_and_unfinished() {
        let mut table = schedule_table();
        let mut d = driver(N2, &[], config());
        let mut steps = 0;
        while !d.is_finished() {
            assert_eq!(d.snapshot().tasks_in_flight, 0);
            let tasks = d.take_tasks(1);
            assert_eq!(tasks.len(), 1, "idle after {steps} steps");
            let result = table.exec(&tasks[0]);
            d.submit(result);
            steps += 1;
        }
        assert_eq!(steps, 58);
        assert!(d.take_tasks(1).is_empty());
        assert!(d.take_tasks(0).is_empty());
    }

    /// The table of a run on 65537 up to its root.
    fn table_65537() -> Table {
        let mut table = Table::new();
        table
            .add("Analyze", "65537", analyzed(&[], prime("65537")))
            .add("Analyze", "65536", analyzed(&[(2, 16)], Rest::One))
            .add("Root", "65537", root(3));
        table
    }

    #[test]
    fn the_certificate_is_checked_by_a_verify_task() {
        let mut table = table_65537();
        let mut d = driver("65537", &[], Config::default());
        for _ in 0..3 {
            table.step(&mut d);
        }
        // The tree is complete and the root is in: the check is queued, not yet handed out.
        let snap = d.snapshot();
        assert_eq!(snap.status, "running");
        assert_eq!(snap.message, "verifying the certificate");
        assert_eq!(snap.tasks_in_flight, 0);
        assert_eq!(snap.primes[0].state, "done");
        assert!(snap.outputs.is_empty());
        let tasks = d.take_tasks(5);
        assert_eq!(trace(&tasks), ["Verify n=65537;65537:3:[2]"]);
        assert_eq!(tasks[0].id(), 4);
        assert!(matches!(
            tasks[0],
            Task::Verify {
                witness_bound: 1024,
                ..
            }
        ));
        let snap = d.snapshot();
        assert_eq!(snap.message, "verifying the certificate");
        assert_eq!(snap.tasks_in_flight, 1);
        assert!(d.take_tasks(5).is_empty());
        let Task::Verify { cert, .. } = &tasks[0] else {
            unreachable!("checked above");
        };
        // Results of unknown ids and of the finished `Root` task are discarded.
        d.submit(TaskResult {
            id: 99,
            outcome: verified(cert),
        });
        d.submit(TaskResult {
            id: 3,
            outcome: verified(cert),
        });
        assert_eq!(d.snapshot().status, "running");
        assert_eq!(d.snapshot().tasks_in_flight, 1);
        d.submit(TaskResult {
            id: 4,
            outcome: verified(cert),
        });
        assert!(d.is_finished());
        let snap = d.snapshot();
        assert_eq!(snap.status, "certified");
        assert_eq!(snap.message, "65537 is prime (1 witness entry)");
        assert_eq!(snap.tasks_in_flight, 0);
        assert_eq!(
            mathlib_code(&snap),
            Some(
                "import Mathlib.Tactic.Primality\n\nexample : Nat.Prime 65537 := by\n  \
                 primality (cert := .witnesses [\n    .lucas { root := 3, primeFactors := [2] }])\n"
            )
        );
        // A duplicate result changes nothing.
        d.submit(TaskResult {
            id: 4,
            outcome: Outcome::VerifyFailed {
                message: "late".to_string(),
            },
        });
        assert_eq!(d.snapshot().status, "certified");
        assert!(d.take_tasks(5).is_empty());
    }

    #[test]
    fn a_rejected_certificate_fails_the_run() {
        let mut table = table_65537();
        table.add(
            "Verify",
            "65537",
            Outcome::VerifyFailed {
                message: "fake rejection".to_string(),
            },
        );
        let mut d = driver("65537", &[], Config::default());
        let snap = table.run(&mut d);
        assert!(d.is_finished());
        assert_eq!(snap.status, "failed");
        assert_eq!(
            snap.message,
            "internal error: the certificate did not verify: fake rejection"
        );
        assert!(snap.outputs.is_empty());
        assert_eq!(table.log.len(), 4);
        assert!(d.take_tasks(5).is_empty());
        // A `Verify` task answered with an outcome of another kind is an internal error too.
        let mut table = table_65537();
        table.add("Verify", "65537", root(3));
        let snap = table.run(&mut driver("65537", &[], Config::default()));
        assert_eq!(snap.status, "failed");
        assert!(
            snap.message
                .starts_with("internal error: task 4 returned an outcome of the wrong kind"),
            "{}",
            snap.message
        );
    }

    #[test]
    fn task_errors_and_inconsistent_analyses_fail_the_run() {
        let mut d = driver("65537", &[], Config::default());
        let task = d.take_tasks(1).pop().expect("a task");
        d.submit(TaskResult {
            id: task.id(),
            outcome: Outcome::Error {
                message: "boom".to_string(),
            },
        });
        let snap = d.snapshot();
        assert_eq!(snap.status, "failed");
        assert_eq!(snap.message, "internal error: task 1 failed: boom");
        let mut d = driver("65537", &[], Config::default());
        let task = d.take_tasks(1).pop().expect("a task");
        // Unknown ids and late results are ignored.
        d.submit(TaskResult {
            id: 99,
            outcome: root(3),
        });
        d.submit(TaskResult {
            id: task.id(),
            outcome: analyzed(&[(3, 1)], prime("65537")),
        });
        assert!(d.snapshot().message.starts_with("internal error"));
        d.submit(TaskResult {
            id: task.id(),
            outcome: analyzed(&[], prime("65537")),
        });
        assert_eq!(d.snapshot().status, "failed");
    }

    #[test]
    fn new_rejects_bad_inputs() {
        let none = Hints::default;
        assert!(Driver::new("", none(), Config::default()).is_err());
        assert!(Driver::new("   ", none(), Config::default()).is_err());
        assert!(Driver::new("12a", none(), Config::default()).is_err());
        assert!(Driver::new("-7", none(), Config::default()).is_err());
        assert!(Driver::new("2^12 7", none(), Config::default()).is_err());
        // Digits split by whitespace alone are one numeral (a wrapped paste).
        assert_eq!(
            Driver::new("1 2", none(), Config::default())
                .unwrap()
                .snapshot()
                .input,
            "12"
        );
        assert!(Driver::new(&"9".repeat(1001), none(), Config::default()).is_err());
        assert!(Driver::new(&"9".repeat(1000), none(), Config::default()).is_ok());
        let small = Config {
            max_digits: 3,
            ..Config::default()
        };
        assert!(Driver::new("1234", none(), small.clone()).is_err());
        assert!(Driver::new(" 123 ", none(), small).is_ok());
        // Factor hints built by hand are filtered and sorted as the parser would.
        let hints = Hints {
            factors: vec![big("7"), big("1"), big("0"), big("7"), big("5")],
            roots: BTreeMap::new(),
        };
        let d = Driver::new("65537", hints, Config::default()).unwrap();
        assert_eq!(d.hints, [big("5"), big("7")]);
    }

    #[test]
    fn plural_adds_an_s_except_for_one() {
        assert_eq!(plural(0, "prime"), "0 primes");
        assert_eq!(plural(1, "task"), "1 task");
        assert_eq!(plural(2, "open composite"), "2 open composites");
    }

    #[test]
    fn new_rejects_a_witness_bound_above_2_10() {
        let at_ceiling = Config {
            witness_bound: 1024,
            ..Config::default()
        };
        assert!(Driver::new("65537", Hints::default(), at_ceiling).is_ok());
        let above = Config {
            witness_bound: 1025,
            ..Config::default()
        };
        let Err(error) = Driver::new("65537", Hints::default(), above) else {
            panic!("a witness_bound above 1024 was accepted");
        };
        assert!(error.contains("1025") && error.contains("1024"), "{error}");
    }

    /// `66720956417 - 1 = 2^16 · 1009²`, so its analysis leaves a power, whose base is a part.
    #[test]
    fn the_base_of_a_power_left_by_an_analysis_is_a_part() {
        let mut t = Table::new();
        let power = Rest::Power {
            base: big("1009"),
            exp: 2,
        };
        t.add(
            "Analyze",
            "66720956417",
            analyzed(&[], prime("66720956417")),
        )
        .add("Analyze", "66720956416", analyzed(&[(2, 16)], power))
        .add("Analyze", "1009", analyzed(&[], prime("1009")))
        .add(
            "Analyze",
            "1008",
            analyzed(&[(2, 4), (3, 2), (7, 1)], Rest::One),
        )
        .add("Root", "1009", root(11))
        .add("Root", "66720956417", root(3));
        let snap = t.run(&mut driver("66720956417", &[], config()));
        assert_eq!(snap.status, "certified", "{}", snap.message);
        assert_eq!(
            certificate(&t.log),
            "n=66720956417;66720956417:3:[2,1009];1009:11:[2,3,7]"
        );
    }

    /// `3275633 - 1 = 2^4 · 101 · 2027` and `2027 - 1 = 2 · 1013`. A missing root takes 2027 out
    /// of the tree with 1013, which only 2027 holds, and the late analysis of `1013 - 1` is
    /// discarded.
    #[test]
    fn a_prime_without_a_root_leaves_the_tree_with_its_subtree() {
        let mut t = Table::new();
        t.add("Analyze", "3275633", analyzed(&[], prime("3275633")))
            .add(
                "Analyze",
                "3275632",
                analyzed(&[(2, 4)], composite("204727")),
            )
            .add("Rho", "204727", divisor("2027"))
            .add("Analyze", "2027", analyzed(&[], prime("2027")))
            .add("Analyze", "101", analyzed(&[], prime("101")))
            .add("Analyze", "2026", analyzed(&[(2, 1)], prime("1013")))
            .add(
                "Analyze",
                "1012",
                analyzed(&[(2, 2), (11, 1), (23, 1)], Rest::One),
            )
            .add("Root", "3275633", root(3))
            .add("Root", "2027", Outcome::Root { root: None });
        let config = Config {
            max_ecm_levels: Some(0),
            ..config()
        };
        let mut d = driver("3275633", &[], config);
        let batch = loop {
            let tasks = d.take_tasks(4);
            if trace(&tasks)
                .iter()
                .any(|task| task.starts_with("Root 2027"))
            {
                break tasks;
            }
            for task in &tasks {
                let result = t.exec(task);
                d.submit(result);
            }
        };
        assert_eq!(trace(&batch), ["Analyze 1012", "Root 2027 [2,1013]"]);
        for task in batch.iter().rev() {
            let result = t.exec(task);
            d.submit(result);
        }
        let snap = d.snapshot();
        let values: Vec<&str> = snap.primes.iter().map(|p| p.value.as_str()).collect();
        assert_eq!(values, ["3275633"]);
        let open: Vec<&str> = snap.primes[0]
            .open
            .iter()
            .map(|c| c.value.as_str())
            .collect();
        assert_eq!(open, ["2027"]);
        let snap = t.run(&mut d);
        assert_eq!(snap.status, "failed");
        assert_eq!(snap.found_factors, "");
        assert!(!trace(&t.log)
            .iter()
            .any(|task| task.starts_with("Root 1013")));
    }
}
