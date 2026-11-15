//! Command-line front end. It runs the driver with worker threads, prints progress to stderr and
//! the certificate (or the composite report, or the failure) to stdout.

use std::any::Any;
use std::collections::HashMap;
use std::io::{self, Write};
use std::panic::{self, AssertUnwindSafe};
use std::process::{self, ExitCode};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};
use std::thread;
use std::time::{Duration, Instant};

use primality_producer::driver::{plural, Config, Driver, Snapshot};
use primality_producer::hints::parse_hints;
use primality_producer::targets::{self, Target, TARGETS};
use primality_producer::task::{run_task, Outcome, TaskResult};

fn usage() -> String {
    format!(
        "usage: primality-cert <N> [--hints \"<text>\"] [--threads k] [--max-ecm-levels L] \
         [--target {}] [--quiet] [--json]",
        target_names().join("|")
    )
}

fn target_names() -> Vec<&'static str> {
    TARGETS.iter().map(|target| target.name).collect()
}

struct Args {
    /// A numeral or an expression (`input::parse_input`).
    n: String,
    hints: String,
    /// The number of worker threads (by default the available parallelism).
    threads: usize,
    max_ecm_levels: Option<usize>,
    /// The target whose Lean text goes to stdout (by default the first of `TARGETS`).
    target: &'static Target,
    /// Silences the progress and the hint usage on stderr.
    quiet: bool,
    /// Prints the final snapshot as JSON on stdout instead of the verdict text.
    json: bool,
}

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.iter().any(|a| a == "--help" || a == "-h") {
        println!("{}", usage());
        return ExitCode::SUCCESS;
    }
    let args = match parse_args(&argv) {
        Ok(args) => args,
        Err(message) => {
            eprintln!("{message}\n{}", usage());
            return ExitCode::from(1);
        }
    };
    let mut config = Config::default();
    if let Some(levels) = args.max_ecm_levels {
        config.ecm_levels.truncate(levels);
    }
    let driver = match Driver::new(&args.n, parse_hints(&args.hints), config) {
        Ok(driver) => driver,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::from(1);
        }
    };
    let snapshot = run(driver, &args);
    ExitCode::from(report(&snapshot, &args))
}

/// Parses the arguments after the program name.
fn parse_args(argv: &[String]) -> Result<Args, String> {
    let mut n = None;
    let mut hints = String::new();
    let mut threads = None;
    let mut max_ecm_levels = None;
    let mut target = &TARGETS[0];
    let mut quiet = false;
    let mut json = false;
    let mut rest = argv.iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--hints" => hints = option_value(&mut rest, "--hints")?.clone(),
            "--threads" => {
                let text = option_value(&mut rest, "--threads")?;
                threads = Some(parse_count(text, "--threads")?);
            }
            "--max-ecm-levels" => {
                let text = option_value(&mut rest, "--max-ecm-levels")?;
                max_ecm_levels = Some(parse_count(text, "--max-ecm-levels")?);
            }
            "--target" => {
                let name = option_value(&mut rest, "--target")?;
                target = targets::find(name).ok_or_else(|| {
                    format!(
                        "--target needs one of {}, found {name:?}",
                        target_names().join(", ")
                    )
                })?;
            }
            "--quiet" => quiet = true,
            "--json" => json = true,
            _ if arg.starts_with("--") => return Err(format!("unknown option {arg}")),
            _ if n.is_none() => n = Some(arg.clone()),
            _ => return Err(format!("unexpected argument {arg}")),
        }
    }
    let n = n.ok_or_else(|| "missing <N>".to_string())?;
    let threads = match threads {
        Some(0) => return Err("--threads must be at least 1".to_string()),
        Some(k) => k,
        None => thread::available_parallelism().map_or(1, |k| k.get()),
    };
    Ok(Args {
        n,
        hints,
        threads,
        max_ecm_levels,
        target,
        quiet,
        json,
    })
}

fn option_value<'a>(
    rest: &mut impl Iterator<Item = &'a String>,
    option: &str,
) -> Result<&'a String, String> {
    rest.next().ok_or_else(|| format!("{option} needs a value"))
}

fn parse_count(text: &str, option: &str) -> Result<usize, String> {
    text.parse()
        .map_err(|_| format!("{option} needs a non-negative integer, found {text:?}"))
}

/// Runs the driver on `args.threads` worker threads, with progress on stderr about once per
/// second and at the end (unless `args.quiet`). A finished run is reported and exits the process
/// from inside the loop, as does a panic inside the driver, so this returns only when every worker
/// stopped before the run finished.
fn run(driver: Driver, args: &Args) -> Snapshot {
    let driver = Mutex::new(driver);
    let running = Mutex::new(HashMap::new());
    let live_workers = AtomicUsize::new(args.threads);
    let start = Instant::now();
    thread::scope(|scope| {
        for _ in 0..args.threads {
            scope.spawn(|| {
                let _live = LiveWorker(&live_workers);
                worker_loop(&driver, &running);
            });
        }
        let mut last_report: Option<Instant> = None;
        loop {
            // A panic inside the driver leaves its state unknown and may lose the result the run
            // waits for.
            if driver.is_poisoned() {
                exit_driver_panicked();
            }
            let step = panic::catch_unwind(AssertUnwindSafe(|| {
                let guard = lock(&driver);
                let finished = guard.is_finished();
                let due = !args.quiet
                    && last_report.is_none_or(|t| t.elapsed() >= Duration::from_secs(1));
                (finished, (finished || due).then(|| guard.snapshot()))
            }));
            let Ok((finished, snapshot)) = step else {
                exit_driver_panicked();
            };
            if let Some(snapshot) = snapshot {
                // Printed after the lock is released, so that a slow stderr does not stall the
                // workers.
                if !args.quiet {
                    eprint!("{}", progress_text(&snapshot, start.elapsed()));
                    last_report = Some(Instant::now());
                }
                if finished {
                    // Leaving the scope would wait for the workers, and a worker returns only
                    // when its task does (minutes for a large input). Exiting here prints the
                    // verdict at once.
                    let code = report(&snapshot, args);
                    let _ = io::stdout().flush();
                    let _ = io::stderr().flush();
                    process::exit(i32::from(code));
                }
            }
            if live_workers.load(Ordering::SeqCst) == 0 {
                break;
            }
            thread::sleep(Duration::from_millis(50));
        }
    });
    let driver = driver
        .into_inner()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    driver.snapshot()
}

/// Ends the process with exit code 3. The panic message is already on stderr.
fn exit_driver_panicked() -> ! {
    eprintln!("internal error: the driver panicked");
    let _ = io::stdout().flush();
    let _ = io::stderr().flush();
    process::exit(3);
}

/// Decrements the live-worker count when dropped, so a panicking worker is counted out too.
struct LiveWorker<'a>(&'a AtomicUsize);

impl Drop for LiveWorker<'_> {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::SeqCst);
    }
}

/// Takes tasks one at a time until the run is finished. A panic in a task becomes an `Error`
/// outcome, so the run never waits for a result that cannot arrive. `running` holds the stop flag
/// of every task on a thread, by id, and a flag is set when `submit` returns its task as stale.
fn worker_loop(driver: &Mutex<Driver>, running: &Mutex<HashMap<u32, Arc<AtomicBool>>>) {
    loop {
        let task = {
            let mut guard = lock(driver);
            if guard.is_finished() {
                return;
            }
            // Registered under the driver's lock, so a task is in `running` before any `submit`
            // can return it as stale.
            guard.take_tasks(1).pop().map(|task| {
                let stop = Arc::new(AtomicBool::new(false));
                lock(running).insert(task.id(), Arc::clone(&stop));
                (task, stop)
            })
        };
        match task {
            Some((task, stop)) => {
                let id = task.id();
                let result = panic::catch_unwind(AssertUnwindSafe(|| {
                    run_task(
                        &task,
                        &mut |done| lock(driver).report_progress(id, done),
                        &|| stop.load(Ordering::Relaxed),
                    )
                }))
                .unwrap_or_else(|payload| TaskResult {
                    id,
                    outcome: Outcome::Error {
                        message: format!("task {id} panicked: {}", panic_message(&*payload)),
                    },
                });
                let stale = lock(driver).submit(result);
                let mut running = lock(running);
                running.remove(&id);
                for stale_id in stale {
                    if let Some(stop) = running.get(&stale_id) {
                        stop.store(true, Ordering::Relaxed);
                    }
                }
            }
            // Results of other threads are awaited.
            None => thread::sleep(Duration::from_millis(10)),
        }
    }
}

fn panic_message(payload: &(dyn Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

/// Locks `mutex`, ignoring poisoning, which the main loop checks for on the driver's lock.
fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// The progress report, a status line followed by one line per prime of the tree.
fn progress_text(snapshot: &Snapshot, elapsed: Duration) -> String {
    let mut text = format!(
        "[{:.1}s] {}: {}",
        elapsed.as_secs_f64(),
        snapshot.status,
        snapshot.message
    );
    if let Some(stage) = &snapshot.stage {
        text.push_str(&format!(
            " | {} {}/{} {}",
            stage.name, stage.done, stage.total, stage.unit
        ));
    }
    if snapshot.searched_digits > 0 {
        text.push_str(&format!(
            " | searched for factors up to {} digits",
            snapshot.searched_digits
        ));
    }
    text.push_str(&format!(
        " | {}, {} in flight\n",
        plural(snapshot.open_composites, "open composite"),
        plural(snapshot.tasks_in_flight, "task")
    ));
    for prime in &snapshot.primes {
        text.push_str(&format!(
            "  {} ({} digits) {}",
            abbreviate(&prime.value),
            prime.digits,
            prime.state
        ));
        if let Some(root) = prime.root {
            text.push_str(&format!(" root {root}"));
        }
        if !prime.factors.is_empty() {
            let factors: Vec<String> = prime.factors.iter().map(|f| abbreviate(f)).collect();
            text.push_str(&format!(" factors {}", factors.join(" ")));
        }
        for part in &prime.open {
            // A part under analysis is not known composite yet.
            if part.stage == "analyzing" {
                text.push_str(&format!(
                    " | analyzing {} ({} digits)",
                    abbreviate(&part.value),
                    part.digits
                ));
            } else {
                text.push_str(&format!(
                    " | open {} ({} digits) {} {}/{}",
                    abbreviate(&part.value),
                    part.digits,
                    part.stage,
                    part.done,
                    part.total
                ));
            }
        }
        text.push('\n');
    }
    text
}

/// A number of more than 40 digits shortened to its first and last 18 digits.
fn abbreviate(value: &str) -> String {
    if value.len() > 40 && value.is_ascii() {
        format!("{}...{}", &value[..18], &value[value.len() - 18..])
    } else {
        value.to_string()
    }
}

/// Prints the final result to stdout (the snapshot as JSON with `args.json`) and the hint usage
/// to stderr (unless `args.quiet`). Returns the exit code, 0 when certified, 2 for a composite and
/// 3 on failure.
fn report(snapshot: &Snapshot, args: &Args) -> u8 {
    let file = snapshot
        .outputs
        .iter()
        .find(|output| output.target == args.target.name)
        .map(|output| output.code.as_str());
    let code = match snapshot.status.as_str() {
        "certified" if file.is_some() => 0,
        "certified" => {
            eprintln!("internal error: status certified without the target's output");
            3
        }
        "composite" => 2,
        _ => 3,
    };
    if args.json {
        let json = serde_json::to_string(snapshot)
            .expect("JSON serialization of our own types cannot fail");
        println!("{json}");
    } else {
        print!("{}", verdict_text(snapshot, file));
    }
    if !args.quiet {
        if !snapshot.hints_used.is_empty() {
            eprintln!("hints used: {}", snapshot.hints_used.join(", "));
        }
        if !snapshot.hints_unused.is_empty() {
            eprintln!(
                "hints dividing nothing: {}",
                snapshot.hints_unused.join(", ")
            );
        }
    }
    code
}

/// The verdict as text: the Lean file `file` of the chosen target when certified, the composite
/// line, or the failure message with the factors found so far.
fn verdict_text(snapshot: &Snapshot, file: Option<&str>) -> String {
    match (snapshot.status.as_str(), file) {
        ("certified", Some(file)) => file.to_string(),
        ("certified", None) => String::new(),
        ("composite", _) => format!("{}\n", snapshot.message),
        _ if snapshot.found_factors.is_empty() => format!("{}\n", snapshot.message),
        _ => format!(
            "{}\nFactors found so far (paste as hints):\n{}",
            snapshot.message, snapshot.found_factors
        ),
    }
}
