// A module worker with its own wasm instance. It runs one task at a time for the coordinator in
// main.js.

import init, { run_task, take_panic_message } from './pkg/primality_producer.js?v=dev';

// Handles `{type: 'task', id, task}` messages. Any exception, a wasm panic included, becomes an
// `Error` outcome, so the coordinator never waits for a result that cannot arrive. A panic arrives
// as a bare "unreachable" trap, so the message the panic hook stored is appended.
self.onmessage = (event) => {
  const { type, id, task } = event.data;
  if (type !== 'task') {
    return;
  }
  let result;
  try {
    result = run_task(task, (done) => postMessage({ type: 'progress', id, done }));
  } catch (e) {
    const panic = panicMessage();
    const message = panic ? `${e} (${panic})` : String(e);
    result = JSON.stringify({ id, outcome: { kind: 'Error', message } });
  }
  postMessage({ type: 'result', id, result });
};

// The stored panic message, or undefined. The instance has just trapped, so even this read is
// guarded.
function panicMessage() {
  try {
    return take_panic_message();
  } catch (e) {
    return undefined;
  }
}

await init({ module_or_path: new URL('./pkg/primality_producer_bg.wasm?v=dev', import.meta.url) });
postMessage({ type: 'ready' });
