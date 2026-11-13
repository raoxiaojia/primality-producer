#!/usr/bin/env python3
"""Browser check of the page against a local server (dev only).

usage: browser-check.py (--n N | --gallery ID) [--url URL] [--hints TEXT] [--workers K]
                        [--target NAME] [--timeout SECONDS] [--expect-file PATH]
                        [--screenshot PATH] [--stop-after SECONDS]
                        [--expect-status {certified,composite,failed}] [--then-invalid TEXT]

Opens the page with `?test=1` in the installed Microsoft Edge, headless through Playwright
(`pip install playwright`, no browser download), runs N or the gallery entry ID, and prints the
status line, the elapsed time and the code shown. Exits 0 only when every expectation holds.
"""

import argparse
import sys
import time
from urllib.parse import urlencode

from playwright.sync_api import TimeoutError as PlaywrightTimeoutError
from playwright.sync_api import sync_playwright

FINAL_STATES = ("certified", "composite", "failed", "stopped")
POLL_SECONDS = 0.25


def parse_args():
    parser = argparse.ArgumentParser(description="Browser check of the page.")
    parser.add_argument("--url", default="http://localhost:8000/", help="the page's URL")
    parser.add_argument("--n", help="the decimal input")
    parser.add_argument("--gallery", metavar="ID", help="select this gallery entry instead of filling n")
    parser.add_argument("--hints", help="the hints text")
    parser.add_argument("--workers", type=int, help="the worker count")
    parser.add_argument("--target", metavar="NAME", help="the output target to select and expect")
    parser.add_argument("--timeout", type=float, default=600, help="seconds to wait for the run")
    parser.add_argument(
        "--expect-file",
        help="a file the code shown must equal, up to line endings and a trailing newline",
    )
    parser.add_argument("--screenshot", help="where to save a full-page screenshot")
    parser.add_argument(
        "--stop-after",
        type=float,
        help="click Stop after this many seconds and expect the Stopped heading and found factors",
    )
    parser.add_argument(
        "--expect-status",
        choices=("certified", "composite", "failed"),
        help="the final status to expect",
    )
    parser.add_argument(
        "--then-invalid",
        metavar="TEXT",
        help="after the run, submit this input, which the driver must reject (such as 12a), and"
        " expect an input error with nothing of the run left on the page",
    )
    args = parser.parse_args()
    if (args.n is None) == (args.gallery is None):
        parser.error("exactly one of --n and --gallery is needed")
    return args


def page_url(args):
    """The page's URL with the test hook, and with the form prefilled unless for a gallery run."""
    params = {"test": "1"} if args.gallery is not None else {"n": args.n, "test": "1"}
    if args.hints is not None:
        params["hints"] = args.hints
    if args.workers is not None:
        params["workers"] = str(args.workers)
    if args.target is not None:
        params["target"] = args.target
    return f"{args.url}?{urlencode(params)}"


def select_gallery(page, entry_id, timeout):
    """Selects the gallery entry, which starts its run, and returns the failures."""
    try:
        page.wait_for_function("() => window.__pp !== undefined", timeout=timeout * 1000)
    except PlaywrightTimeoutError:
        return ["the page script did not load"]
    try:
        started = page.evaluate("(id) => window.__pp.gallery(id)", entry_id)
    except Exception as error:  # noqa: BLE001 (an unknown id is reported by the page as an error)
        return [f"the gallery entry {entry_id!r} could not be selected: {error}"]
    if started is not True:
        return [f"the gallery entry {entry_id!r} did not start a run"]
    print(f"Gallery entry {entry_id!r} selected")
    return []


def status(page):
    """The page's state as `window.__pp.status()` reports it."""
    return page.evaluate("() => (window.__pp ? window.__pp.status() : 'loading')")


def wait_until_over(page, timeout):
    """Polls the status until the run is over; returns the final status or None on timeout."""
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        current = status(page)
        if current in FINAL_STATES:
            return current
        time.sleep(POLL_SECONDS)
    return None


def stop_run(page, after, timeout):
    """Clicks Stop after `after` seconds and returns the failures of the Stop expectations."""
    deadline = time.monotonic() + after
    while time.monotonic() < deadline and status(page) not in FINAL_STATES:
        time.sleep(POLL_SECONDS)
    if status(page) in FINAL_STATES:
        return [f"the run was already over ({status(page)}) before Stop could be clicked"]
    page.click("#stop")
    try:
        page.wait_for_function(
            "() => window.__pp.status() === 'stopped'", timeout=timeout * 1000
        )
    except PlaywrightTimeoutError:
        return ["the page did not report 'stopped' after Stop was clicked"]
    failures = []
    if not page.is_visible("#stoppedHeading") or page.inner_text("#stoppedHeading") != "Stopped":
        failures.append("the heading 'Stopped' is not shown")
    if not page.is_visible("#factors"):
        failures.append("the found-factors text is not shown")
    else:
        print("Found factors:")
        print(page.inner_text("#factors"))
    return failures


def submit_invalid(page, text, timeout):
    """Submits the invalid input `text` after a run and returns the failures of the expectation
    that nothing of the previous run is left on the page."""
    page.fill("#n", text)
    page.click("#generate")
    try:
        page.wait_for_function(
            "() => window.__pp.status() === 'failed'"
            " && !document.getElementById('inputError').hidden",
            timeout=timeout * 1000,
        )
    except PlaywrightTimeoutError:
        return [f"the page did not report a failed run with an input error for {text!r}"]
    print(f"After submitting {text!r}: {page.inner_text('#status')}")
    print(f"Input error: {page.inner_text('#inputError')}")
    failures = []
    if page.evaluate("() => window.__pp.snapshot()") is not None:
        failures.append("window.__pp.snapshot() still returns the previous run's snapshot")
    for selector, shown in (
        ("#treeBox", "tree"),
        ("#factorsBox", "found-factors box"),
        ("#hintsBox", "hints box"),
        ("#outputBox", "Lean text"),
    ):
        if page.is_visible(selector):
            failures.append(f"the previous run's {shown} is still shown after the invalid input")
    return failures


def output_text(page):
    """The code the page shows (the text Copy copies), or None when it shows none."""
    return page.evaluate(
        "() => document.getElementById('outputBox').hidden"
        " ? null : document.getElementById('output').textContent"
    )


def report(page, final):
    """Prints the status line, the worker count, the elapsed time and the output text."""
    print(f"Final state: {final}")
    if page.is_visible("#galleryInfo"):
        print(page.inner_text("#galleryInfo"))
    print(f"Status line: {page.inner_text('#status')}")
    print(f"Workers ready: {page.evaluate('() => window.__pp.workers()')}")
    print(page.inner_text("#elapsed"))
    print(f"Target: {page.evaluate('() => window.__pp.target()')}")
    if page.is_visible("#inputError"):
        print(f"Input error: {page.inner_text('#inputError')}")
    output = output_text(page)
    if output is not None:
        print("Output:")
        print(output, end="" if output.endswith("\n") else "\n")
    elif page.is_visible("#reason"):
        print(f"Reason: {page.inner_text('#reason')}")
    return output


def normalized(text):
    """`text` without a byte-order mark, with LF line endings and no trailing newline."""
    return text.lstrip(chr(0xFEFF)).replace("\r\n", "\n").rstrip("\n")


def check_expectations(args, final, output, target):
    """The failed expectations, as messages. `target` is the page's selected target."""
    failures = []
    if final is None:
        failures.append(f"the run did not finish within {args.timeout:g} s")
    if args.expect_status is not None and final != args.expect_status:
        failures.append(f"expected status {args.expect_status}, got {final}")
    if args.target is not None and target != args.target:
        failures.append(f"expected the target {args.target}, got {target}")
    if args.expect_file is not None:
        with open(args.expect_file, encoding="utf-8") as file:
            expected = file.read()
        if output is None:
            failures.append("no code was produced")
        elif normalized(expected) != normalized(output):
            failures.append(f"the code differs from {args.expect_file}")
    return failures


def log_console(message):
    """Prints a console error or warning of the page."""
    if message.type in ("error", "warning"):
        print(f"[console {message.type}] {message.text}")


def main():
    args = parse_args()
    failures = []
    with sync_playwright() as playwright:
        browser = playwright.chromium.launch(channel="msedge", headless=True)
        page = browser.new_page()
        page.on("console", log_console)
        page.on("pageerror", lambda error: print(f"[page error] {error}"))
        page.goto(page_url(args))
        if args.gallery is not None:
            failures += select_gallery(page, args.gallery, args.timeout)
        else:
            page.click("#generate")
        if args.stop_after is not None:
            failures += stop_run(page, args.stop_after, args.timeout)
        final = wait_until_over(page, args.timeout)
        output = report(page, final)
        target = page.evaluate("() => window.__pp.target()")
        failures += check_expectations(args, final, output, target)
        # The Generate button stays disabled while a run is in progress, so the second submission
        # needs the first run to be over.
        if args.then_invalid is not None and final is not None:
            failures += submit_invalid(page, args.then_invalid, args.timeout)
        if args.screenshot:
            page.screenshot(path=args.screenshot, full_page=True)
            print(f"Screenshot: {args.screenshot}")
        browser.close()
    for failure in failures:
        print(f"FAIL: {failure}")
    print("OK" if not failures else f"{len(failures)} expectation(s) failed")
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
