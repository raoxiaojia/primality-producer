#!/usr/bin/env node
// Node check of web/main.js (dev only). It runs the page script with a small DOM shim and an
// in-thread Worker shim over the wasm in web/pkg, and checks what the browser check cannot pin
// down, such as the status line's plurals, the focus between Generate and Stop, worker
// replacement after a trap and for a stale task, the gallery, the target buttons and the reuse
// of tree items. Needs web/pkg (see scripts/build-web.sh) and Node 22 or later, and exits 0 when
// every check holds.
//
// usage: node scripts/web-check.mjs

import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';

const WEB = new URL('../web/', import.meta.url);
// A prime whose `n - 1` is `2 * 1000003 * 1000121`: trial division leaves the composite product,
// which Pollard rho splits at once, so the run shows a level and parts under analysis.
const N = '2000248000727';
// Analyze and rho tasks are held this long so that a render falls into them and the page shows
// the level and the part under analysis.
const SLOW_MS = 300;
// Root tasks are held longer in run 1 (by more than the render interval), so that a render falls
// between a child's result and its parent's root, where the parent's tree item is kept and the
// child's is rebuilt.
const ROOT_MS = 700;
const FINAL = new Set(['certified', 'composite', 'failed', 'stopped']);

// --- fetch shim: the wasm from its file: URL, gallery.json from this stub -----------------------

// Two entries with short runs. The first fills the number box with its expression, the second
// with its decimal value.
const STUB_GALLERY = JSON.stringify({
  version: 1,
  built: '2026-11-03',
  groups: [
    {
      name: 'Stub group',
      entries: [
        {
          id: 'm61',
          name: 'Mersenne prime 2^61 - 1',
          ref: 'OEIS A000043',
          expr: '2^61 - 1',
          value: '2305843009213693951',
          input: 'expr',
          digits: 19,
          entries: 2,
          hints: '1321:13',
          source: 'web-check stub',
        },
        {
          id: 'f4',
          name: 'Fermat prime F4',
          ref: 'OEIS A019434',
          expr: '(2^17 + 2)/2',
          value: '65537',
          input: 'value',
          digits: 5,
          entries: 1,
          hints: '65537:3',
          source: 'web-check stub',
        },
      ],
    },
  ],
});

const realFetch = globalThis.fetch;
globalThis.fetch = async (input, init) => {
  const url = input instanceof URL ? input : new URL(String(input));
  if (url.pathname.endsWith('/gallery.json')) {
    return new Response(STUB_GALLERY, {
      status: 200,
      headers: { 'Content-Type': 'application/json' },
    });
  }
  if (url.protocol !== 'file:') {
    return realFetch(input, init);
  }
  const bytes = readFileSync(fileURLToPath(url));
  return new Response(bytes, { status: 200, headers: { 'Content-Type': 'application/wasm' } });
};
WebAssembly.instantiateStreaming = async (response, imports) =>
  WebAssembly.instantiate(await (await response).arrayBuffer(), imports);

// --- DOM shim: what main.js touches on its elements -------------------------------------------

class Element {
  constructor(tag) {
    this.tagName = tag;
    this.hidden = false;
    this.disabled = false;
    this.value = '';
    this.className = '';
    this.style = {};
    this.children = [];
    this.handlers = {};
    this.attributes = {};
    const classes = new Set();
    this.classList = {
      toggle: (name, force) => {
        const on = force === undefined ? !classes.has(name) : Boolean(force);
        if (on) {
          classes.add(name);
        } else {
          classes.delete(name);
        }
        return on;
      },
      contains: (name) => classes.has(name),
    };
  }
  get textContent() {
    return this.children
      .map((child) => (typeof child === 'string' ? child : child.textContent))
      .join('');
  }
  set textContent(text) {
    this.children = [String(text)];
  }
  addEventListener(type, handler) {
    this.handlers[type] = handler;
  }
  append(...nodes) {
    this.children.push(...nodes);
  }
  replaceChildren(...nodes) {
    this.children = nodes;
  }
  setAttribute(name, value) {
    this.attributes[name] = String(value);
  }
  select() {}
  remove() {}
  focus() {
    document.activeElement = this;
  }
  scrollIntoView() {}
}

const elements = new Map();
function byId(id) {
  if (!elements.has(id)) {
    elements.set(id, new Element('div'));
  }
  return elements.get(id);
}
globalThis.document = {
  getElementById: byId,
  createElement: (tag) => new Element(tag),
  body: new Element('body'),
  execCommand: () => false,
};
globalThis.window = globalThis;

// --- Worker shim: runs the tasks in this thread with the real `run_task` -----------------------

// The page's module URL, so that the page's own `init()` returns at once after this one.
const pkg = await import(new URL('pkg/primality_producer.js?v=dev', WEB).href);
await pkg.default();
const TARGET_LIST = JSON.parse(pkg.targets());
const FIRST = TARGET_LIST[0];
const LAST = TARGET_LIST.at(-1);
// The URL prefills the form for the first run, with the number wrapped and indented as a paste
// may be, selects the last target and installs the test hook.
globalThis.location = {
  search: `?n=${N.slice(0, 7)}%0A%20${N.slice(7)}&workers=2&target=${LAST.name}&test=1`,
};
// One record per Worker constructed, with the kinds of its tasks, whether it was terminated, and
// the kinds of the tasks it was terminated in the middle of.
const workers = [];
// How the shim serves a task (`{ delay, trap, outcome }`), set per run. A trap throws the
// exception a Rust panic produces in the browser instead of running the task, and an outcome is
// returned without running it.
let behaviour = () => ({ delay: 0, trap: false });

globalThis.Worker = class FakeWorker {
  constructor() {
    this.record = { tasks: [], terminated: false, cut: [] };
    workers.push(this.record);
    this.onmessage = null;
    this.onerror = null;
    setTimeout(() => this.deliver({ type: 'ready' }), 0);
  }
  postMessage(message) {
    if (message.type !== 'task') {
      return;
    }
    const task = JSON.parse(message.task);
    this.record.tasks.push(task.kind);
    const { delay, trap, outcome } = behaviour(task);
    setTimeout(() => {
      if (this.record.terminated) {
        this.record.cut.push(task.kind);
        return;
      }
      let result;
      try {
        if (trap) {
          throw new WebAssembly.RuntimeError('unreachable');
        }
        result = outcome
          ? JSON.stringify({ id: message.id, outcome })
          : pkg.run_task(message.task, (done) =>
            this.deliver({ type: 'progress', id: message.id, done }),
          );
      } catch (e) {
        result = JSON.stringify({ id: message.id, outcome: { kind: 'Error', message: String(e) } });
      }
      this.deliver({ type: 'result', id: message.id, result });
    }, delay);
  }
  deliver(data) {
    if (!this.record.terminated && this.onmessage) {
      this.onmessage({ data });
    }
  }
  terminate() {
    this.record.terminated = true;
  }
};

// The render ticker is set once per run; a replacement worker must not set a second one.
let intervals = 0;
const realSetInterval = globalThis.setInterval;
globalThis.setInterval = (...args) => {
  intervals++;
  return realSetInterval(...args);
};

// --- The page script, its form prefilled by the URL ---------------------------------------------

await import(new URL('main.js?v=dev', WEB).href);
const ui = Object.fromEntries(
  [
    'form', 'n', 'hints', 'workers', 'status', 'reason', 'output', 'levelBox', 'levelText', 'tree',
    'galleryNote', 'galleryList', 'galleryInfo', 'targets', 'requires', 'playground', 'announcer',
  ].map((id) => [id, byId(id)]),
);

const failures = [];
function check(condition, description) {
  if (!condition) {
    failures.push(description);
  }
  console.log(`${condition ? 'ok  ' : 'FAIL'} ${description}`);
}

const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

// The Lean file of the target `target` in the last snapshot.
const codeOf = (target) =>
  window.__pp.snapshot().outputs.find((output) => output.target === target.name).code;

// The texts of the open parts under the primes of the tree.
function openParts() {
  const parts = [];
  for (const prime of ui.tree.children) {
    for (const child of prime.children) {
      if (typeof child !== 'string' && child.className === 'open') {
        parts.push(...child.children.map((part) => part.textContent));
      }
    }
  }
  return parts;
}

// Waits for the run to end and returns its final status, the texts shown while it ran, and the
// tree's reuse counts between polls. On a new snapshot, the item of a prime already shown counts
// as `kept` or `rebuilt` when that matches whether its view changed, and as `wrong` otherwise.
async function observeRun(timeoutMs) {
  const seen = { status: new Set(), level: new Set(), parts: new Set() };
  const reuse = { rebuiltUnchanged: 0, kept: 0, rebuilt: 0, wrong: 0 };
  let previous = null;
  const deadline = Date.now() + timeoutMs;
  while (Date.now() < deadline) {
    const status = window.__pp.status();
    if (FINAL.has(status)) {
      return { status, seen, reuse };
    }
    if (status === 'running') {
      // Renders are throttled, so the status text may still be the starting line for a moment.
      if (ui.status.textContent.startsWith('Running:')) {
        seen.status.add(ui.status.textContent);
      }
      if (!ui.levelBox.hidden) {
        seen.level.add(ui.levelText.textContent);
      }
      for (const part of openParts()) {
        seen.parts.add(part);
      }
      const snapshot = window.__pp.snapshot();
      // The shim's `replaceChildren` stores a new array, so the array's identity says whether
      // the tree was rendered.
      const children = ui.tree.children;
      const items = new Map(
        (snapshot ? snapshot.primes : []).map((prime, index) => [
          prime.value,
          { json: JSON.stringify(prime), item: children[index] },
        ]),
      );
      if (previous !== null) {
        if (snapshot === previous.snapshot) {
          reuse.rebuiltUnchanged += children === previous.children ? 0 : 1;
        } else {
          for (const [value, { json, item }] of items) {
            const before = previous.items.get(value);
            if (before === undefined) {
              continue;
            }
            const same = before.json === json;
            const kept = before.item === item;
            if (same === kept) {
              reuse[same ? 'kept' : 'rebuilt']++;
            } else {
              reuse.wrong++;
            }
          }
        }
      }
      previous = { snapshot, children, items };
    }
    await sleep(2);
  }
  throw new Error('the run did not finish in time');
}

// With `exercised`, a kept and a rebuilt item must both have been observed.
function checkReuse(reuse, exercised) {
  const counts = JSON.stringify(reuse);
  check(reuse.wrong === 0, `every tree item is kept or rebuilt with its prime's view (${counts})`);
  check(reuse.rebuiltUnchanged === 0, `the tree is left alone while the snapshot is unchanged (${counts})`);
  if (exercised) {
    check(reuse.kept > 0 && reuse.rebuilt > 0, `both a kept and a rebuilt tree item were observed (${counts})`);
  }
}

// Submits the form with `n` and waits until the page has left its previous state (`startRun`
// awaits the wasm module before it changes the state).
async function submitForm(n) {
  const before = window.__pp.status();
  ui.n.value = n;
  ui.hints.value = '';
  ui.workers.value = '2';
  ui.form.handlers.submit({ preventDefault() {} });
  const started = Date.now();
  while (window.__pp.status() === before && Date.now() - started < 2000) {
    await sleep(5);
  }
}

// Whether `count` and the plural suffix `s` agree ("1 task", "2 tasks").
const agree = (count, s) => (Number(count) === 1) === (s === '');

// --- Run 1: the number from the URL, wrapped; status line, level and tree -----------------------

console.log(`\n--- run 1: n = ${N} from the URL, wrapped ---`);
behaviour = (task) => ({
  delay: ['Analyze', 'Rho'].includes(task.kind) ? SLOW_MS : task.kind === 'Root' ? ROOT_MS : 0,
  trap: false,
});
await sleep(50);
check(
  window.__pp.status() === 'idle' && workers.length === 0,
  `the URL starts no run (${window.__pp.status()}, ${workers.length} workers)`,
);
let workersBefore = 0;
let intervalsBefore = 0;
ui.form.handlers.submit({ preventDefault() {} });
let run = await observeRun(120_000);
console.log(`status lines: ${JSON.stringify([...run.seen.status], null, 2)}`);
console.log(`level texts: ${JSON.stringify([...run.seen.level])}`);
console.log(`open parts: ${JSON.stringify([...run.seen.parts])}`);
const tools = TARGET_LIST.map((target) => target.tool.replaceAll('`', ''));
const toolList = tools.length === 1 ? tools[0] : `${tools.slice(0, -1).join(', ')} or ${tools.at(-1)}`;
check(
  byId('tools').textContent === toolList,
  `the intro names every target's tool (${JSON.stringify(byId('tools').textContent)})`,
);
check(ui.n.value === N, `the number field holds the stripped number (${JSON.stringify(ui.n.value)})`);
check(run.status === 'certified', `the run is certified (${run.status})`);
check(
  ui.output.textContent === codeOf(LAST) && ui.output.textContent.includes(N),
  `the code is the ${LAST.label} one (?target=${LAST.name}) for the stripped number`,
);
check(ui.announcer.textContent === 'Certified', `the outcome is announced (${ui.announcer.textContent})`);
check(run.seen.status.size > 0, 'a running status line was observed');
for (const text of run.seen.status) {
  const m = /^Running: .+, (\d+) open composite(s?), (\d+) task(s?) in flight, (\d+) worker(s?)$/.exec(
    text,
  );
  check(m !== null, `the status line carries each count once: ${JSON.stringify(text)}`);
  if (m !== null) {
    check(
      agree(m[1], m[2]) && agree(m[3], m[4]) && agree(m[5], m[6]),
      `the plurals of the status line agree: ${JSON.stringify(text)}`,
    );
  }
}
check(run.seen.level.size > 0, 'a level text was observed');
for (const text of run.seen.level) {
  check(/^.+: \d+\/\d+ (curves|tasks)$/.test(text), `the level text ends with its unit: ${text}`);
}
check(
  [...run.seen.parts].some((part) => /^analyzing \d+ \(\d+ digits\)$/.test(part)),
  'a part under analysis is labelled "analyzing"',
);
check(
  ![...run.seen.parts].some((part) => part.startsWith('composite ') && part.includes('analyzing')),
  'no part is labelled "composite" while under analysis',
);
check(workers.length - workersBefore === 2, 'two workers were constructed');
check(intervals - intervalsBefore === 1, 'one render ticker was set');
checkReuse(run.reuse, true);

// --- Run 2: a trap in the Root task; the worker is replaced and the run fails ------------------

console.log('\n--- run 2: n = 65537, the Root task traps ---');
let trapped = false;
behaviour = (task) => {
  if (task.kind === 'Root' && !trapped) {
    trapped = true;
    return { delay: 0, trap: true };
  }
  return { delay: 0, trap: false };
};
workersBefore = workers.length;
intervalsBefore = intervals;
await submitForm('65537');
run = await observeRun(60_000);
console.log(`status: ${ui.status.textContent}`);
console.log(`reason: ${ui.reason.textContent}`);
const records = workers.slice(workersBefore);
check(run.status === 'failed', `the run fails (${run.status})`);
check(
  /^internal error: task \d+ failed: RuntimeError: unreachable$/.test(ui.reason.textContent),
  'the reason names the trap',
);
check(records.length === 3, `a replacement worker was spawned (${records.length} constructed)`);
const trappedRecord = records.find((record) => record.tasks.includes('Root'));
check(
  trappedRecord !== undefined && trappedRecord.terminated && trappedRecord.tasks.at(-1) === 'Root',
  'the trapped worker was terminated and got no further task',
);
check(records.every((record) => record.terminated), 'every worker was terminated at the end');
check(intervals - intervalsBefore === 1, 'one render ticker was set');
checkReuse(run.reuse, false);

// --- Run 3: the page recovers ------------------------------------------------------------------

console.log('\n--- run 3: n = 65537 again ---');
behaviour = () => ({ delay: 0, trap: false });
workersBefore = workers.length;
intervalsBefore = intervals;
// Generate has the focus, as after a press of Enter on it.
byId('generate').focus();
await submitForm(' 65537\n');
check(document.activeElement === byId('stop'), 'Generate hands the focus to Stop as it disables itself');
run = await observeRun(60_000);
console.log(`status: ${ui.status.textContent}`);
check(run.status === 'certified', `the run is certified (${run.status})`);
check(document.activeElement === byId('generate'), 'Stop hands the focus back to Generate at the end');
check(ui.n.value === '65537', 'the number field holds the stripped number');
check(ui.reason.hidden, 'the previous failure is no longer shown');
check(workers.length - workersBefore === 2, 'two workers were constructed');
check(intervals - intervalsBefore === 1, 'one render ticker was set');
// The target buttons, with the last target still selected from run 1.
const targetState = () => ({
  labels: ui.targets.children.map((button) => button.textContent),
  pressed: ui.targets.children.map((button) => button.attributes['aria-pressed']),
  requires: ui.requires.hidden ? null : ui.requires.textContent,
  code: ui.output.textContent,
});
// The release line of `target`, or null when it names no release (the line is hidden).
const requiresLine = (target) => (target.release ? `Requires ${target.release}` : null);
// Whether the playground link is shown exactly when `target` has an editor, carrying the code.
const playgroundMatches = (target) => {
  if (!target.playground) {
    return ui.playground.hidden;
  }
  const prefix = `${target.playground}#code=`;
  return !ui.playground.hidden
    && ui.playground.href.startsWith(prefix)
    && decodeURIComponent(ui.playground.href.slice(prefix.length)) === ui.output.textContent;
};
check(
  ui.targets.hidden === (TARGET_LIST.length < 2),
  `the target buttons are shown only for more than one target (${TARGET_LIST.length})`,
);
let targets = targetState();
check(
  JSON.stringify(targets.labels) === JSON.stringify(TARGET_LIST.map((target) => target.label))
    && JSON.stringify(targets.pressed)
      === JSON.stringify(TARGET_LIST.map((target) => String(target === LAST))),
  `the target buttons show ${LAST.label} selected (${JSON.stringify(targets)})`,
);
check(
  targets.requires === requiresLine(LAST) && targets.code === codeOf(LAST),
  `the ${LAST.label} release line and code are shown (${JSON.stringify(targets)})`,
);
check(playgroundMatches(LAST), `the ${LAST.label} playground link (${ui.playground.href})`);
ui.targets.children[0].handlers.click();
targets = targetState();
check(
  JSON.stringify(targets.pressed)
    === JSON.stringify(TARGET_LIST.map((target) => String(target === FIRST)))
    && targets.requires === requiresLine(FIRST)
    && targets.code === codeOf(FIRST)
    && window.__pp.target() === FIRST.name,
  `a click on ${FIRST.label} selects it (${JSON.stringify(targets)})`,
);
check(playgroundMatches(FIRST), `the ${FIRST.label} playground link (${ui.playground.href})`);

// --- Run 4: the gallery entry m61 from the stub gallery.json ------------------------------------

console.log('\n--- run 4: the gallery entry m61 from the stub gallery.json ---');
const M61 = '2305843009213693951';
// The analysis is held so that the run is observably in progress right after the selection.
behaviour = (task) => ({ delay: task.kind === 'Analyze' ? SLOW_MS : 0, trap: false });
workersBefore = workers.length;
// The note's text is set only when the gallery cannot be loaded (its `hidden` attribute is not
// modelled by the shim).
check(ui.galleryNote.textContent === '', `the gallery loaded without a note (${JSON.stringify(ui.galleryNote.textContent)})`);
check(
  ui.galleryList.children.length === 1,
  `the menu holds the stub's one group (${ui.galleryList.children.length} details)`,
);
check(
  JSON.stringify(window.__pp.galleryIds()) === '["m61","f4"]',
  `the stub's ids are loaded (${JSON.stringify(window.__pp.galleryIds())})`,
);
let unknownRejected = false;
try {
  await window.__pp.gallery('no-such-entry');
} catch (e) {
  unknownRejected = true;
}
check(unknownRejected, 'an unknown gallery id is rejected');
const selected = await window.__pp.gallery('m61');
check(selected === true, `the entry was selected (${selected})`);
check(ui.n.value === '2^61 - 1', `the number box holds the expression (${JSON.stringify(ui.n.value)})`);
check(ui.hints.value === '1321:13', `the hints box holds the root hints (${JSON.stringify(ui.hints.value)})`);
// The run has started once its workers exist (spawned right after the run is set up).
let waited = Date.now();
while (workers.length === workersBefore && Date.now() - waited < 2000) {
  await sleep(5);
}
check(workers.length - workersBefore === 2, 'a run started: two workers were constructed');
// The entry's button: details > [summary, list] > li > button.
const entryButton = ui.galleryList.children[0].children[1].children[0].children[0];
check(entryButton.disabled === true, 'the gallery button is disabled during the run');
check(
  !ui.galleryInfo.hidden
    && ui.galleryInfo.textContent
      === 'Gallery: Mersenne prime 2^61 - 1 (OEIS A000043), 2^61 - 1, 19 digits. Source: web-check stub.',
  `the info line names the entry (${JSON.stringify(ui.galleryInfo.textContent)})`,
);
run = await observeRun(60_000);
console.log(`status: ${ui.status.textContent}`);
check(run.status === 'certified', `the run is certified (${run.status})`);
check(
  ui.output.textContent.startsWith(
    'import Mathlib.Tactic.Primality\nimport Mathlib.Tactic.NormNum.Pow\n\n'
      + 'example : Nat.Prime (2 ^ 61 - 1) := by\n',
  ),
  `a power adds norm_num's power extension to the imports, and the text states the expression (${JSON.stringify(ui.output.textContent.split('\n').slice(0, 4))})`,
);
check(playgroundMatches(FIRST), 'the playground link carries the code');
check(ui.status.textContent.includes(M61), `the status line shows the value (${ui.status.textContent})`);
check(entryButton.disabled === false, 'the gallery button is enabled again after the run');
check(ui.status.classList.contains('status-certified'), 'the status line carries its state class');
checkReuse(run.reuse, false);

// An entry whose expression the number box does not take fills in its decimal value.
behaviour = () => ({ delay: 0, trap: false });
check(await window.__pp.gallery('f4') === true, 'the second entry was selected');
check(ui.n.value === '65537', `the number box holds the decimal value (${JSON.stringify(ui.n.value)})`);
run = await observeRun(60_000);
check(run.status === 'certified', `the second entry's run is certified (${run.status})`);
check(
  ui.output.textContent.startsWith(
    'import Mathlib.Tactic.Primality\n\nexample : Nat.Prime 65537 := by\n',
  ),
  'the code imports the tactic alone and states the numeral',
);

// A run from the form afterwards clears the info line.
behaviour = () => ({ delay: 0, trap: false });
await submitForm('65537');
run = await observeRun(60_000);
check(run.status === 'certified', `the following form run is certified (${run.status})`);
check(ui.galleryInfo.hidden, 'a run from the form clears the gallery info line');

// --- Run 5: the worker of a stale ECM task is replaced ------------------------------------------

console.log(`\n--- run 5: n = ${N}, the product reaches ECM ---`);
// Rho and p-1 report no factor without running, so the product reaches the first ECM level with
// a task on each worker. The first task to split it leaves the other stale.
behaviour = (task) => ({
  delay: task.kind === 'Ecm' ? 50 : 0,
  trap: false,
  outcome: ['Rho', 'Pm1'].includes(task.kind) ? { kind: 'NoFactor' } : undefined,
});
workersBefore = workers.length;
await submitForm(N);
run = await observeRun(60_000);
check(run.status === 'certified', `the run is certified (${run.status})`);
check(
  workers.length - workersBefore === 3,
  `two workers and one replacement were constructed (${workers.length - workersBefore})`,
);
// The shim records a cut task when its delay ends, which may be after the run.
await sleep(100);
const cut = workers.slice(workersBefore).flatMap((record) => record.cut);
check(
  JSON.stringify(cut) === '["Ecm"]',
  `the worker of the stale ECM task was terminated mid-task (${JSON.stringify(cut)})`,
);

console.log(failures.length === 0 ? '\nOK' : `\n${failures.length} check(s) failed`);
process.exit(failures.length === 0 ? 0 : 1);
