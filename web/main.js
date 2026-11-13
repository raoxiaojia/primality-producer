// The coordinator and UI of the page. It owns a WasmDriver (the run's state machine, compiled to
// wasm), hands the driver's tasks to module workers and renders the driver's snapshots.
//
// Every URL of the page's own files ends in `?v=dev`, which scripts/build-web.sh replaces by the
// build's version in dist/, so that a browser never mixes cached files of two deploys.

import init, { WasmDriver, take_panic_message, targets } from './pkg/primality_producer.js?v=dev';

const MAX_WORKERS = 64;
// One worker per logical processor (4 when the browser does not say).
const DEFAULT_WORKERS = Math.min(MAX_WORKERS, Math.max(1, navigator.hardwareConcurrency || 4));
// Renders happen at most this often.
const RENDER_INTERVAL_MS = 200;
// A number with more digits than this is followed by its digit count.
const COUNT_DIGITS_ABOVE = 30;
// The states the status line is coloured by, through a `status-<state>` class.
const STATUS_STATES = ['starting', 'running', 'certified', 'composite', 'failed', 'stopped'];
// The output targets by name, in button order, from the wasm module's `targets()`. Each has a
// button `label`, the `tool` its text proves primality with, the `release` the text was checked
// against (null for a development head) and a `playground` editor (or null), which reads the code
// from the URL fragment `#code=…`.
const TARGETS = new Map();

const ui = elementsById([
  'tools', 'form', 'n', 'hints', 'workers', 'generate', 'stop', 'inputError', 'announcer', 'run',
  'status', 'elapsed', 'levelBox', 'progress', 'levelText', 'searched', 'stoppedHeading',
  'outputBox', 'targets', 'requires', 'copyOutput', 'playground', 'output', 'reason',
  'factorsBox', 'factors', 'copyFactors', 'treeBox', 'tree', 'hintsBox', 'hintsList',
  'galleryNote', 'galleryList', 'galleryInfo',
]);

// The page's state. It is 'idle' before the first run, then 'starting' while the workers load,
// 'running', and finally 'certified', 'composite', 'failed' or 'stopped'.
let state = 'idle';
// The current run (see `beginRun`), or null before the first one.
let run = null;
// The last snapshot rendered, as an object.
let latestSnapshot = null;
// The gallery's buttons in the side menu, filled by `loadGallery`.
const galleryButtons = [];
// The selected output target, a key of TARGETS. It outlives runs; `?target=…` sets it at load,
// and the first target is the default.
let selectedTarget = null;
// Runs need the main thread's wasm instance. A Rust panic traps it, after which no call into it is
// safe, so the page then asks for a reload instead of starting another run.
let wasmLoaded = false;
let wasmTrapped = false;

// The main thread's wasm instance. The driver's calls are bookkeeping and stay fast.
ui.generate.disabled = true;
init({
  module_or_path: new URL('./pkg/primality_producer_bg.wasm?v=dev', import.meta.url),
})
  .then(() => {
    for (const target of JSON.parse(targets())) {
      TARGETS.set(target.name, target);
    }
    if (!TARGETS.has(selectedTarget)) {
      selectedTarget = TARGETS.keys().next().value;
    }
    renderTools();
    wasmLoaded = true;
    setStartEnabled(canStart());
  })
  .catch((e) => showInputError(`The WebAssembly module failed to load: ${errorMessage(e)}`));
loadGallery();

ui.form.addEventListener('submit', (event) => {
  event.preventDefault();
  startRun();
});
ui.stop.addEventListener('click', stopRun);
ui.copyOutput.addEventListener('click', copyHandler(ui.copyOutput, ui.output));
ui.copyFactors.addEventListener('click', copyHandler(ui.copyFactors, ui.factors));
// Hints a gallery entry filled in are cleared when the number is edited, so that they do not
// carry over to a number of the user's own.
let galleryHints = null;
ui.n.addEventListener('input', () => {
  if (galleryHints !== null && ui.hints.value === galleryHints) {
    ui.hints.value = '';
  }
  galleryHints = null;
});

ui.workers.value = DEFAULT_WORKERS;
applyUrlParams();

// --- Setup ---------------------------------------------------------------------------------

function elementsById(ids) {
  return Object.fromEntries(ids.map((id) => [id, document.getElementById(id)]));
}

// Prefills the form from `?n=…&hints=…&workers=…` and selects the target of `?target=…` (an
// unknown name gives way to the default once the targets are loaded).
function applyUrlParams() {
  const params = new URLSearchParams(location.search);
  if (params.has('target')) {
    selectedTarget = params.get('target');
  }
  if (params.has('n')) {
    ui.n.value = params.get('n');
  }
  if (params.has('hints')) {
    ui.hints.value = params.get('hints');
  }
  if (params.has('workers')) {
    ui.workers.value = clampWorkers(params.get('workers'));
  }
}

// Fills the intro with the targets' tools as "A", "A or B" or "A, B or C".
function renderTools() {
  const tools = [...TARGETS.values()].map((target) => codeText(target.tool));
  ui.tools.replaceChildren(
    ...tools.flatMap((nodes, i) => {
      if (i === 0) {
        return nodes;
      }
      return [i === tools.length - 1 ? ' or ' : ', ', ...nodes];
    }),
  );
}

// The nodes of `text` with its backticked parts as `<code>` elements.
function codeText(text) {
  return text.split('`').map((part, i) => {
    if (i % 2 === 0) {
      return part;
    }
    const code = document.createElement('code');
    code.textContent = part;
    return code;
  });
}

// The worker count as an integer in 1…MAX_WORKERS (the default when `value` is blank or not a
// number).
function clampWorkers(value) {
  const count = Math.floor(Number(value));
  if (String(value).trim() === '' || !Number.isFinite(count)) {
    return DEFAULT_WORKERS;
  }
  return Math.min(MAX_WORKERS, Math.max(1, count));
}

// --- The run -------------------------------------------------------------------------------

// Starts a run from the form. A driver error is shown under the number box. `galleryEntry` is the
// entry the form was filled from (null for none), which the info line names.
function startRun(galleryEntry = null) {
  if (!canStart()) {
    return;
  }
  clearInputError();
  renderGalleryInfo(galleryEntry);
  // A pasted number may be wrapped or grouped by spaces. The driver reads it as one numeral, and
  // the box shows it joined.
  let n = ui.n.value;
  if (/^[\d\s]+$/.test(n)) {
    n = n.replace(/\s+/g, '');
    ui.n.value = n;
  }
  const hintsText = ui.hints.value;
  const workerCount = clampWorkers(ui.workers.value);
  ui.workers.value = workerCount;

  let driver;
  try {
    driver = new WasmDriver(n, hintsText);
  } catch (e) {
    // A trap is a bug, which the reason line reports. Any other exception is an invalid input.
    let message = null;
    if (e instanceof WebAssembly.RuntimeError) {
      message = failureText(e);
    } else {
      showInputError(e);
    }
    beginRun(null, workerCount);
    failRun(message);
    return;
  }
  beginRun(driver, workerCount);
  guarded(() => {
    // An input the driver settles at once (n < 2) needs no worker.
    if (driver.is_finished()) {
      finishRun();
      return;
    }
    for (let i = 0; i < workerCount; i++) {
      run.workers.push(spawnWorker(run));
    }
    render();
  });
}

// Replaces the previous run (freeing its driver) by a fresh one around `driver`.
function beginRun(driver, workerCount) {
  disposeRun();
  // `render` replaces the previous run's snapshot only when the snapshot JSON changes, and a run
  // whose driver could not be constructed has no snapshot, so the previous one is dropped here.
  latestSnapshot = null;
  run = {
    driver,
    workerCount,
    workers: [],
    started: performance.now(),
    finished: null,
    done: false,
    // A page-level failure message, which overrides the snapshot's message in the reason line.
    error: null,
    lastJson: null,
    // The tree, the outcome and the hints are rebuilt only when the snapshot JSON or the state
    // differs from these.
    renderedJson: null,
    renderedState: null,
    // The tree item of each prime and the JSON of its view, by value.
    treeItems: new Map(),
    lastRender: 0,
    renderTimer: null,
    ticker: null,
  };
  setState('starting');
  ui.run.hidden = false;
  // The pressed button is about to be disabled, which would drop the keyboard focus.
  const refocus = document.activeElement === ui.generate
    || galleryButtons.includes(document.activeElement);
  setStartEnabled(false);
  ui.stop.disabled = false;
  if (refocus) {
    ui.stop.focus();
  }
  // On a narrow screen the gallery is above the form, and the run would start out of view.
  ui.status.scrollIntoView({ block: 'nearest' });
}

function disposeRun() {
  if (!run) {
    return;
  }
  terminateWorkers(run);
  const { driver } = run;
  run = null;
  // No call into a trapped instance is safe, so its drivers are leaked.
  if (!wasmTrapped) {
    driver?.free();
  }
}

// The worker's messages count only while `owner` is the current run.
function spawnWorker(owner) {
  const worker = new Worker(new URL('./worker.js?v=dev', import.meta.url), { type: 'module' });
  const slot = { worker, ready: false, idle: false, taskId: null };
  worker.onmessage = (event) => {
    if (owner === currentRun()) {
      guarded(() => onWorkerMessage(slot, event.data));
    }
  };
  worker.onerror = (event) => {
    if (owner === currentRun()) {
      failRun(`a worker failed: ${event.message || 'unknown error'}`);
    }
  };
  return slot;
}

// The run whose workers may still report, or null once it is over.
function currentRun() {
  return run && !run.done ? run : null;
}

// Runs `action`, turning an exception (a driver call that throws) into a failed run.
function guarded(action) {
  try {
    action();
  } catch (e) {
    failRun(failureText(e));
  }
}

// The text a run ends with when a driver call throws `e`. A panic arrives as a bare "unreachable"
// trap, so the message the panic hook stored is appended, and the trapped instance asks for a
// reload.
function failureText(e) {
  const panic = panicMessage();
  const text = panic ? `${errorMessage(e)} (${panic})` : errorMessage(e);
  if (!(e instanceof WebAssembly.RuntimeError)) {
    return text;
  }
  wasmTrapped = true;
  return `${text}. Reload the page to start another run.`;
}

// The stored panic message, or undefined. The instance has just trapped, so even this read is
// guarded.
function panicMessage() {
  try {
    return take_panic_message();
  } catch (e) {
    return undefined;
  }
}

// Dispatching starts once every worker is ready. A replacement worker joins the running dispatch
// loop when it is ready.
function onWorkerMessage(slot, data) {
  switch (data.type) {
    case 'ready':
      slot.ready = true;
      slot.idle = true;
      if (state !== 'starting') {
        pump();
      } else if (run.workers.every((other) => other.ready)) {
        setState('running');
        run.ticker = setInterval(requestRender, RENDER_INTERVAL_MS);
        pump();
      } else {
        requestRender();
      }
      break;
    case 'progress':
      run.driver.report_progress(data.id, data.done);
      requestRender();
      break;
    case 'result': {
      const stale = run.driver.submit(data.result);
      slot.taskId = null;
      // An `Error` outcome is how worker.js reports an exception, which for a Rust panic leaves
      // the wasm instance trapped mid-task, so that instance never gets another task.
      if (JSON.parse(data.result).outcome.kind === 'Error') {
        replaceWorker(slot);
      } else {
        slot.idle = true;
      }
      replaceStaleWorkers(stale);
      pump();
      break;
    }
    default:
      break;
  }
}

function replaceWorker(slot) {
  terminateWorker(slot);
  run.workers[run.workers.indexOf(slot)] = spawnWorker(run);
}

// A worker cannot be interrupted in the middle of a task, so the workers running the tasks
// `stale` (ids the driver no longer needs) are replaced.
function replaceStaleWorkers(stale) {
  for (const slot of run.workers.filter((other) => stale.includes(other.taskId))) {
    replaceWorker(slot);
  }
}

// One step of the dispatch loop.
function pump() {
  if (run.driver.is_finished()) {
    finishRun();
    return;
  }
  dispatch();
  requestRender();
}

// A driver that issues nothing while nothing is in flight would hang the page, so that is reported
// as a failure.
function dispatch() {
  const idle = run.workers.filter((slot) => slot.idle);
  if (idle.length === 0) {
    return;
  }
  const tasks = JSON.parse(run.driver.take_tasks(idle.length));
  if (tasks.length > idle.length) {
    throw new Error(`the driver issued ${tasks.length} tasks for ${idle.length} idle workers`);
  }
  for (const task of tasks) {
    const slot = idle.shift();
    slot.idle = false;
    slot.taskId = task.id;
    slot.worker.postMessage({ type: 'task', id: task.id, task: JSON.stringify(task) });
  }
  if (run.workers.every((slot) => slot.idle)) {
    throw new Error('internal error: the driver issued no task while none is in flight');
  }
}

function finishRun() {
  endRun();
  const snapshot = readSnapshot();
  setState(snapshot ? snapshot.status : 'failed');
  render();
}

// Ends the run as a page-level failure with `message` (null for an invalid input, which the
// error under the number box reports).
function failRun(message) {
  if (!run) {
    return;
  }
  run.error = message;
  endRun();
  setState('failed');
  render();
}

// Stops the run and leaves its last snapshot shown under the heading "Stopped".
function stopRun() {
  if (!run || run.done) {
    return;
  }
  endRun();
  setState('stopped');
  render();
}

// Marks the run over, which stops its worker messages, renders and ticks.
function endRun() {
  run.done = true;
  run.finished = performance.now();
  terminateWorkers(run);
  clearInterval(run.ticker);
  clearTimeout(run.renderTimer);
  run.ticker = null;
  run.renderTimer = null;
  const refocus = document.activeElement === ui.stop;
  setStartEnabled(canStart());
  ui.stop.disabled = true;
  if (refocus && !ui.generate.disabled) {
    ui.generate.focus();
  }
}

// Whether a new run can start now.
function canStart() {
  return wasmLoaded && !wasmTrapped && currentRun() === null;
}

// Enables or disables Generate and the gallery's buttons.
function setStartEnabled(enabled) {
  ui.generate.disabled = !enabled;
  for (const button of galleryButtons) {
    button.disabled = !enabled;
  }
}

function terminateWorkers(target) {
  for (const slot of target.workers) {
    terminateWorker(slot);
  }
}

function terminateWorker(slot) {
  slot.worker.onmessage = null;
  slot.worker.onerror = null;
  slot.worker.terminate();
}

// Sets the page's state and announces it to screen readers. The status line itself is not a
// live region, since its counts change several times a second.
function setState(next) {
  state = next;
  ui.announcer.textContent = capitalize(next);
}

// --- The gallery ---------------------------------------------------------------------------

// Fills the side menu from gallery.json, or leaves a note when it cannot be loaded.
async function loadGallery() {
  let gallery;
  try {
    const response = await fetch(new URL('./gallery.json?v=dev', import.meta.url));
    if (!response.ok) {
      throw new Error(`HTTP ${response.status}`);
    }
    gallery = await response.json();
  } catch (e) {
    ui.galleryNote.hidden = false;
    ui.galleryNote.textContent = 'No gallery available (gallery.json could not be loaded).';
    return;
  }
  renderGallery(gallery);
}

function renderGallery(gallery) {
  const groups = (gallery.groups ?? []).map((group, index) => {
    const list = document.createElement('ul');
    for (const entry of group.entries) {
      const button = document.createElement('button');
      button.type = 'button';
      button.className = 'gallery-entry';
      button.disabled = !canStart();
      button.append(entry.name, ' ', metaSpan(`${entry.digits} digits`));
      button.addEventListener('click', () => selectGalleryEntry(entry));
      galleryButtons.push(button);
      const item = document.createElement('li');
      item.append(button);
      list.append(item);
    }
    return detailsElement(group.name, list, index === 0);
  });
  ui.galleryList.replaceChildren(...groups);
}

function detailsElement(title, content, open) {
  const details = document.createElement('details');
  details.open = open;
  const summary = document.createElement('summary');
  summary.textContent = title;
  details.append(summary, content);
  return details;
}

function metaSpan(text) {
  const span = document.createElement('span');
  span.className = 'meta';
  span.textContent = text;
  return span;
}

// Fills the form from the gallery entry `entry` and starts a run (changing nothing while no run
// can start).
function selectGalleryEntry(entry) {
  if (!canStart()) {
    return;
  }
  ui.n.value = entry.input === 'expr' ? entry.expr : entry.value;
  ui.hints.value = entry.hints ?? '';
  galleryHints = ui.hints.value;
  startRun(entry);
}

// The info line above the status, naming the gallery entry the run started from.
function renderGalleryInfo(entry) {
  ui.galleryInfo.hidden = entry === null;
  if (entry === null) {
    ui.galleryInfo.textContent = '';
    return;
  }
  const ref = entry.ref ? ` (${entry.ref})` : '';
  const note = entry.note ? ` ${entry.note}.` : '';
  ui.galleryInfo.textContent =
    `Gallery: ${entry.name}${ref}, ${entry.expr}, ${entry.digits} digits. Source: ${entry.source}.${note}`;
}

// --- Rendering -----------------------------------------------------------------------------

// Renders now when the last render is old enough, else once at the end of the interval.
function requestRender() {
  if (!run || run.done) {
    return;
  }
  const due = run.lastRender + RENDER_INTERVAL_MS - performance.now();
  if (due <= 0) {
    render();
  } else if (run.renderTimer === null) {
    run.renderTimer = setTimeout(render, due);
  }
}

function render() {
  if (!run) {
    return;
  }
  run.lastRender = performance.now();
  clearTimeout(run.renderTimer);
  run.renderTimer = null;
  ui.elapsed.textContent = `Elapsed: ${formatSeconds((run.finished ?? performance.now()) - run.started)}`;
  const json = snapshotJson();
  if (json !== run.lastJson) {
    run.lastJson = json;
    latestSnapshot = json === null ? null : JSON.parse(json);
  }
  renderStatus(latestSnapshot);
  renderLevel(latestSnapshot);
  if (json !== run.renderedJson || state !== run.renderedState) {
    run.renderedJson = json;
    run.renderedState = state;
    renderTree(latestSnapshot);
    renderOutcome(latestSnapshot);
    renderHints(latestSnapshot);
  }
}

// The driver's snapshot as JSON, or the last one when the driver cannot answer any more.
function snapshotJson() {
  if (!run.driver) {
    return null;
  }
  try {
    return run.driver.snapshot();
  } catch (e) {
    return run.lastJson;
  }
}

function readSnapshot() {
  const json = snapshotJson();
  return json === null ? null : JSON.parse(json);
}

// A composite or failed run shows its message in the reason line instead of the status line.
function renderStatus(snapshot) {
  const ready = run.workers.filter((slot) => slot.ready).length;
  const message = snapshot ? snapshot.message : '';
  let text;
  switch (state) {
    case 'starting':
      text = `Starting ${counted(run.workerCount, 'worker')} (${ready} ready)`;
      break;
    case 'running': {
      const counts = snapshot
        ? `, ${counted(snapshot.open_composites, 'open composite')}, ${counted(snapshot.tasks_in_flight, 'task')} in flight`
        : '';
      text = `Running: ${message}${counts}, ${counted(run.workerCount, 'worker')}`;
      break;
    }
    case 'certified':
      text = `Certified: ${message}`;
      break;
    case 'stopped':
      text = 'Stopped by the user';
      break;
    default:
      text = capitalize(state);
  }
  setStatusText(text);
  for (const name of STATUS_STATES) {
    ui.status.classList.toggle(`status-${name}`, state === name);
  }
}

function setStatusText(text) {
  ui.run.hidden = false;
  ui.status.textContent = text;
}

// The progress bar of the current level and the "searched up to" line.
function renderLevel(snapshot) {
  const level = snapshot ? snapshot.level : null;
  ui.levelBox.hidden = level === null;
  if (level !== null) {
    ui.progress.max = Math.max(1, level.total);
    ui.progress.value = Math.min(level.done, level.total);
    ui.levelText.textContent = `${level.name}: ${level.done}/${level.total} ${level.unit ?? 'curves'}`;
  }
  const searched = snapshot ? snapshot.searched_digits : 0;
  ui.searched.hidden = !(searched > 0);
  ui.searched.textContent = `Searched for factors up to ${searched} digits`;
}

// An item is rebuilt only when its prime's view changed, so a progress tick on one composite does
// not rebuild the items of the other primes.
function renderTree(snapshot) {
  const primes = snapshot ? snapshot.primes : [];
  ui.treeBox.hidden = primes.length === 0;
  const items = primes.map((prime) => {
    const json = JSON.stringify(prime);
    const cached = run.treeItems.get(prime.value);
    if (cached !== undefined && cached.json === json) {
      return cached.item;
    }
    const item = primeItem(prime);
    run.treeItems.set(prime.value, { json, item });
    return item;
  });
  ui.tree.replaceChildren(...items);
}

function primeItem(prime) {
  const item = document.createElement('li');
  item.append(numberSpan(prime.value), ' ', badge(prime.state));
  if (prime.root !== null && prime.root !== undefined) {
    item.append(` root ${prime.root}`);
  }
  if (prime.factors.length > 0) {
    const factors = document.createElement('div');
    factors.className = 'meta';
    factors.append('factors: ');
    prime.factors.forEach((factor, index) => {
      factors.append(index > 0 ? ', ' : '', numberSpan(factor));
    });
    item.append(factors);
  }
  if (prime.open.length > 0) {
    const open = document.createElement('ul');
    open.className = 'open';
    open.append(...prime.open.map(compositeItem));
    item.append(open);
  }
  return item;
}

// The digit count is added here when `numberSpan` does not add it. A part still under analysis is
// not known to be composite and has no progress to show.
function compositeItem(composite) {
  const item = document.createElement('li');
  const digits = composite.value.length > COUNT_DIGITS_ABOVE ? '' : ` (${composite.digits} digits)`;
  if (composite.stage === 'analyzing') {
    item.append(badge('analyzing'), ' ', numberSpan(composite.value), digits);
  } else {
    item.append(
      badge('composite'),
      ' ',
      numberSpan(composite.value),
      `${digits}: ${composite.stage} ${composite.done}/${composite.total}`,
    );
  }
  return item;
}

// A span showing every digit of `value`, followed by the digit count for a long number.
function numberSpan(value) {
  const span = document.createElement('span');
  span.className = 'num';
  span.textContent = value;
  if (value.length > COUNT_DIGITS_ABOVE) {
    span.append(` (${value.length} digits)`);
  }
  return span;
}

// The badge of a state in the tree; its `state-<name>` class picks the colour.
function badge(name) {
  const span = document.createElement('span');
  span.className = `state state-${name}`;
  span.textContent = name;
  return span;
}

// Shows the Lean texts when certified, the reason when composite or failed, and the found factors
// after Stop or a failure.
function renderOutcome(snapshot) {
  const outputs = state === 'certified' && snapshot !== null ? snapshot.outputs : [];
  ui.outputBox.hidden = outputs.length === 0;
  renderOutputs(outputs);

  const reason = state === 'composite' || state === 'failed'
    ? run.error ?? (snapshot ? snapshot.message : '')
    : '';
  ui.reason.hidden = reason === '';
  ui.reason.textContent = reason;

  ui.stoppedHeading.hidden = state !== 'stopped';
  const offerFactors = (state === 'stopped' || state === 'failed') && snapshot !== null;
  ui.factorsBox.hidden = !offerFactors;
  if (offerFactors) {
    ui.factors.textContent = snapshot.found_factors || '(none yet)';
    ui.copyFactors.disabled = snapshot.found_factors === '';
  }
}

// The output box for `outputs` (empty unless certified). A click on a target button re-renders
// this box alone.
function renderOutputs(outputs) {
  const shown = outputs.find((output) => output.target === selectedTarget);
  ui.targets.hidden = outputs.length < 2;
  ui.targets.replaceChildren(
    ...outputs.map((output) => {
      const button = document.createElement('button');
      button.type = 'button';
      button.textContent = TARGETS.get(output.target).label;
      button.setAttribute('aria-pressed', String(output === shown));
      button.addEventListener('click', () => {
        selectedTarget = output.target;
        renderOutputs(outputs);
      });
      return button;
    }),
  );
  const target = shown ? TARGETS.get(shown.target) : undefined;
  const code = shown ? shown.code : '';
  ui.requires.hidden = !target?.release;
  ui.requires.textContent = target?.release ? `Requires ${target.release}` : '';
  ui.playground.hidden = !target?.playground;
  if (target?.playground) {
    ui.playground.href = `${target.playground}#code=${encodeURIComponent(code)}`;
  }
  ui.output.textContent = code;
}

// The hint usage, shown once the run is over.
function renderHints(snapshot) {
  const over = state !== 'starting' && state !== 'running';
  const used = snapshot ? snapshot.hints_used : [];
  const unused = snapshot ? snapshot.hints_unused : [];
  const show = over && used.length + unused.length > 0;
  ui.hintsBox.hidden = !show;
  if (show) {
    ui.hintsList.replaceChildren(
      ...used.map((hint) => hintItem(hint, 'used', 'hint-used')),
      ...unused.map((hint) => hintItem(hint, 'divides nothing', 'hint-unused')),
    );
  }
}

function hintItem(hint, verdict, className) {
  const item = document.createElement('li');
  item.className = className;
  item.append(numberSpan(hint), `: ${verdict}`);
  return item;
}

// --- Small helpers -------------------------------------------------------------------------

function showInputError(error) {
  ui.inputError.hidden = false;
  ui.inputError.textContent = errorMessage(error);
}

function clearInputError() {
  ui.inputError.hidden = true;
  ui.inputError.textContent = '';
}

// The text of an exception, including wasm runtime errors, which have no useful `message`.
function errorMessage(error) {
  if (error instanceof Error && error.message && !(error instanceof WebAssembly.RuntimeError)) {
    return error.message;
  }
  return String(error);
}

function capitalize(word) {
  return word.charAt(0).toUpperCase() + word.slice(1);
}

// `count` followed by `noun` in the matching number ("1 task", "2 tasks").
function counted(count, noun) {
  return `${count} ${noun}${count === 1 ? '' : 's'}`;
}

// Seconds with one decimal, with the minutes split off beyond a minute.
function formatSeconds(ms) {
  const seconds = ms / 1000;
  if (seconds < 60) {
    return `${seconds.toFixed(1)} s`;
  }
  const minutes = Math.floor(seconds / 60);
  return `${minutes} min ${(seconds - 60 * minutes).toFixed(1)} s`;
}

// Copies the text of `source` and reports on `button` for a moment. It falls back to a selection
// copy where the clipboard API is unavailable.
function copyHandler(button, source) {
  const label = button.textContent;
  let timer = null;
  return async () => {
    const text = source.textContent;
    let copied = false;
    try {
      await navigator.clipboard.writeText(text);
      copied = true;
    } catch (e) {
      copied = copyBySelection(text);
    }
    button.textContent = copied ? 'Copied' : 'Copy failed';
    clearTimeout(timer);
    timer = setTimeout(() => {
      button.textContent = label;
    }, 1500);
  };
}

function copyBySelection(text) {
  const area = document.createElement('textarea');
  area.value = text;
  area.setAttribute('readonly', '');
  area.style.position = 'fixed';
  area.style.opacity = '0';
  document.body.append(area);
  area.select();
  let copied = false;
  try {
    copied = document.execCommand('copy');
  } catch (e) {
    copied = false;
  }
  area.remove();
  return copied;
}
