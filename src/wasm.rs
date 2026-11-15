//! wasm-bindgen bindings for the page. Tasks, results, snapshots and targets cross the boundary
//! as JSON strings.

use std::cell::RefCell;

use js_sys::Function;
use wasm_bindgen::prelude::*;

use crate::driver::{Config, Driver};
use crate::hints::parse_hints;
use crate::task::{self, Task, TaskResult};

thread_local! {
    /// The message of the last panic, stored by the hook `start` installs.
    static PANIC_MESSAGE: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Runs when the module is instantiated. A panic reaches JavaScript as a bare "unreachable" trap,
/// so the hook installed here keeps the panic message for `take_panic_message`.
#[wasm_bindgen(start)]
fn start() {
    std::panic::set_hook(Box::new(|info| {
        let payload = info.payload();
        let text = payload
            .downcast_ref::<&str>()
            .copied()
            .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
            .unwrap_or("(no message)");
        let message = match info.location() {
            Some(location) => format!("panicked at {location}: {text}"),
            None => format!("panicked: {text}"),
        };
        PANIC_MESSAGE.with(|slot| *slot.borrow_mut() = Some(message));
    }));
}

/// The message of the last panic in this instance, cleared by the call (`undefined` when none).
#[wasm_bindgen]
pub fn take_panic_message() -> Option<String> {
    PANIC_MESSAGE.with(|slot| slot.borrow_mut().take())
}

/// A `Driver` owned by the page.
#[wasm_bindgen]
pub struct WasmDriver {
    inner: Driver,
}

#[wasm_bindgen]
impl WasmDriver {
    /// A driver with the default configuration for the input `n`, a numeral or an expression
    /// (`input::parse_input`), with the hints parsed from `hints_text`.
    #[wasm_bindgen(constructor)]
    pub fn new(n: &str, hints_text: &str) -> Result<WasmDriver, JsError> {
        let hints = parse_hints(hints_text);
        let inner = Driver::new(n, hints, Config::default()).map_err(|e| JsError::new(&e))?;
        Ok(WasmDriver { inner })
    }

    /// Up to `max` new tasks, as a JSON array of `Task`. They count as in flight from then on.
    pub fn take_tasks(&mut self, max: usize) -> String {
        to_json(&self.inner.take_tasks(max))
    }

    /// Submits a JSON `TaskResult` and returns the ids of the factoring tasks it left stale.
    pub fn submit(&mut self, result_json: &str) -> Result<Vec<u32>, JsError> {
        let result: TaskResult = serde_json::from_str(result_json)
            .map_err(|e| JsError::new(&format!("invalid task result: {e}")))?;
        Ok(self.inner.submit(result))
    }

    /// Updates the curve count of the in-flight task `id`.
    pub fn report_progress(&mut self, id: u32, done: u32) {
        self.inner.report_progress(id, done);
    }

    /// The current `Snapshot` as JSON.
    pub fn snapshot(&self) -> String {
        to_json(&self.inner.snapshot())
    }

    /// Whether the run is over.
    pub fn is_finished(&self) -> bool {
        self.inner.is_finished()
    }
}

/// `targets::TARGETS` as a JSON array of `Target`s without their renderers.
#[wasm_bindgen]
pub fn targets() -> String {
    to_json(&crate::targets::TARGETS)
}

/// Runs the JSON `Task` in `task_json` and returns its `TaskResult` as JSON. `progress(done)` is
/// called after each ECM curve. Unparsable input throws.
#[wasm_bindgen]
pub fn run_task(task_json: &str, progress: &Function) -> Result<String, JsError> {
    let task: Task =
        serde_json::from_str(task_json).map_err(|e| JsError::new(&format!("invalid task: {e}")))?;
    // A worker cannot read a stop signal during a task, so the page replaces a worker instead of
    // stopping its task.
    let result = task::run_task(
        &task,
        &mut |done| {
            // A throwing callback must not abort the task.
            let _ = progress.call1(&JsValue::NULL, &JsValue::from(done));
        },
        &|| false,
    );
    Ok(to_json(&result))
}

fn to_json<T: serde::Serialize>(value: &T) -> String {
    serde_json::to_string(value).expect("JSON serialization of our own types cannot fail")
}
