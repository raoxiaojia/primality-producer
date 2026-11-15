#!/usr/bin/env python3
"""Builds web/gallery.json, the page's gallery, from scripts/gallery/entries.json.

usage: build_gallery.py [--producer PATH] [--out PATH] [--only ID [ID ...]] [--threads K]
                        [--max-ecm-levels L]

Runs each entry with its hints file through the command-line tool and records the roots of its
tree as the entry's hints. Exits with an error when an entry does not certify.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import expr_eval  # noqa: E402

GALLERY_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.dirname(os.path.dirname(GALLERY_DIR))
ENTRIES_PATH = os.path.join(GALLERY_DIR, "entries.json")
HINTS_DIR = os.path.join(GALLERY_DIR, "hints")
DEFAULT_OUT = os.path.join(PROJECT_ROOT, "web", "gallery.json")
DEFAULT_PRODUCER = os.path.join(
    PROJECT_ROOT, "target", "release", "primality-cert.exe" if os.name == "nt" else "primality-cert"
)
# The lines of the producer's stderr shown when an entry fails.
STDERR_TAIL = 20
# The characters of the producer's input expressions (src/input.rs).
INPUT_CHARS = re.compile(r"[0-9\s+\-*^()]+")


class GalleryError(Exception):
    """An entry that cannot go into the gallery, with the reason."""


def parse_args():
    parser = argparse.ArgumentParser(description="Builds web/gallery.json.")
    parser.add_argument(
        "--producer",
        default=DEFAULT_PRODUCER,
        help="the primality-cert executable (default %(default)s)",
    )
    parser.add_argument("--out", help=f"where to write the gallery (default {DEFAULT_OUT})")
    parser.add_argument("--only", nargs="+", metavar="ID", help="build only these entries (needs --out)")
    parser.add_argument("--threads", type=int, default=8, help="the producer's thread count")
    parser.add_argument("--max-ecm-levels", type=int, default=1, help="the producer's ECM level cap")
    args = parser.parse_args()
    if args.only and args.out is None:
        parser.error("--only builds a partial gallery and needs an explicit --out")
    if args.out is None:
        args.out = DEFAULT_OUT
    return args


def load_entries(path):
    """The entries of `path`, checked for the required keys and unique ids."""
    with open(path, encoding="utf-8") as file:
        data = json.load(file)
    entries = data["entries"]
    seen = set()
    for entry in entries:
        missing = [key for key in ("id", "group", "name", "ref", "expr", "source") if key not in entry]
        if missing:
            raise GalleryError(f"entry {entry.get('id', '?')!r} lacks {', '.join(missing)}")
        if entry["id"] in seen:
            raise GalleryError(f"duplicate entry id {entry['id']!r}")
        seen.add(entry["id"])
    return entries


def hints_text(entry_id):
    """The contents of the entry's hints file, or None when there is none."""
    path = os.path.join(HINTS_DIR, f"{entry_id}.txt")
    if not os.path.exists(path):
        return None
    with open(path, encoding="utf-8") as file:
        return file.read().strip()


def number_text(expr, value):
    """The text for the number box, `expr` when it uses only the producer's input characters and
    the decimal `value` otherwise."""
    return expr if INPUT_CHARS.fullmatch(expr) else str(value)


def producer_command(producer, number, hints, threads, max_ecm_levels):
    """The producer's command line for the input text `number` with the hints text `hints` (None
    for none)."""
    command = [producer, number]
    if hints is not None:
        command += ["--hints", hints]
    command += ["--json", "--threads", str(threads), "--max-ecm-levels", str(max_ecm_levels)]
    return command


def run_producer(command):
    """Runs the producer and returns its snapshot; raises GalleryError when stdout is not JSON."""
    completed = subprocess.run(command, capture_output=True, text=True, encoding="utf-8", errors="replace")
    try:
        return json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise GalleryError(
            f"the producer exited with code {completed.returncode} and no JSON snapshot ({error})"
            f"\n--- stdout ---\n{completed.stdout.strip()}{stderr_tail(completed.stderr)}"
        ) from None


def stderr_tail(stderr):
    """The last lines of the producer's stderr, formatted for an error message."""
    lines = stderr.strip().splitlines()
    if not lines:
        return ""
    return f"\n--- producer stderr (last {STDERR_TAIL} lines) ---\n" + "\n".join(lines[-STDERR_TAIL:])


def gallery_entry(entry, number, value, snapshot):
    """The gallery record of `entry`, run as the input text `number` of value `value`, from the
    producer's final `snapshot`."""
    status = snapshot.get("status")
    if status != "certified":
        raise GalleryError(f"status {status!r}: {snapshot.get('message', '')}")
    decimal = str(value)
    if "input" in snapshot and snapshot["input"] != decimal:
        raise GalleryError(f"the snapshot is for {snapshot['input']}, not {decimal}")
    tree = []
    for prime in snapshot["primes"]:
        q = int(prime["value"])
        if prime.get("state") != "done" or prime.get("root") is None:
            raise GalleryError(f"tree prime {q} is {prime.get('state')!r} without a root")
        tree.append((q, int(prime["root"])))
    if value not in {q for q, _ in tree}:
        raise GalleryError("the input is missing from the tree")
    if len({q for q, _ in tree}) != len(tree):
        raise GalleryError("a tree prime is listed twice")
    # The input's own token carries its root, which is the costliest one to search.
    hints = " ".join(f"{q}:{root}" for q, root in sorted(tree))
    record = {
        "id": entry["id"],
        "name": entry["name"],
        "ref": entry["ref"],
        "expr": entry["expr"],
        "number": number,
        "digits": len(decimal),
        "hints": hints,
        "source": entry["source"],
    }
    if "note" in entry:
        record["note"] = entry["note"]
    return record


def grouped(records, entries):
    """The gallery groups, in the order the groups first appear in `entries`."""
    groups = {}
    by_id = {record["id"]: record for record in records}
    for entry in entries:
        if entry["id"] in by_id:
            groups.setdefault(entry["group"], []).append(by_id[entry["id"]])
    return [{"name": name, "entries": members} for name, members in groups.items()]


def build(args):
    """Builds the gallery as a dict; raises GalleryError on the first entry that does not certify."""
    entries = load_entries(ENTRIES_PATH)
    if args.only:
        unknown = set(args.only) - {entry["id"] for entry in entries}
        if unknown:
            raise GalleryError(f"unknown entry id(s): {', '.join(sorted(unknown))}")
        entries = [entry for entry in entries if entry["id"] in args.only]
    records = []
    for entry in entries:
        started = time.monotonic()
        value = expr_eval.evaluate(entry["expr"])
        hints = hints_text(entry["id"])
        number = number_text(entry["expr"], value)
        command = producer_command(args.producer, number, hints, args.threads, args.max_ecm_levels)
        try:
            snapshot = run_producer(command)
            record = gallery_entry(entry, number, value, snapshot)
        except GalleryError as error:
            raise GalleryError(f"{entry['id']}: {error}") from None
        records.append(record)
        unused = snapshot.get("hints_unused", [])
        unused_note = f", {len(unused)} hint(s) divide nothing" if unused else ""
        print(
            f"{entry['id']}: {record['digits']} digits, {len(snapshot['primes'])} entries, "
            f"{time.monotonic() - started:.1f} s{unused_note}",
            file=sys.stderr,
            flush=True,
        )
    return {"groups": grouped(records, entries)}


def write_gallery(gallery, path):
    with open(path, "w", encoding="utf-8", newline="\n") as file:
        json.dump(gallery, file, indent=1, ensure_ascii=False)
        file.write("\n")


def main():
    args = parse_args()
    try:
        gallery = build(args)
    except (GalleryError, expr_eval.ExprError, OSError) as error:
        sys.exit(f"gallery build failed: {error}")
    write_gallery(gallery, args.out)
    count = sum(len(group["entries"]) for group in gallery["groups"])
    print(f"wrote {args.out}: {count} entries in {len(gallery['groups'])} groups", file=sys.stderr)


if __name__ == "__main__":
    main()
