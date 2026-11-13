#!/usr/bin/env python3
"""Tests of the gallery scripts (dev only), on expr_tests.json and hand-made snapshots. Exits 0
when every check holds.

usage: python -I scripts/gallery/test_gallery.py
"""

import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import build_gallery  # noqa: E402
import expr_eval  # noqa: E402

failures = []


def check(condition, description):
    if not condition:
        failures.append(description)
    print(f"{'ok  ' if condition else 'FAIL'} {description}")


def abbreviate(text):
    return f"{text[:15]}…{text[-15:]} ({len(text)} digits)" if len(text) > 40 else text


# --- The evaluator ---------------------------------------------------------------------------

with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "expr_tests.json"), encoding="utf-8") as file:
    tests = json.load(file)

for case in tests["cases"]:
    try:
        result = str(expr_eval.evaluate(case["expr"]))
    except expr_eval.ExprError as error:
        result = f"raises: {error}"
    check(result == case["value"], f"{case['expr']!r} = {abbreviate(result)}")

for expr in tests["errors"]:
    try:
        value = expr_eval.evaluate(expr)
    except expr_eval.ExprError as error:
        check(True, f"{expr!r} raises: {error}")
    else:
        check(False, f"{expr!r} raises (got {abbreviate(str(value))})")

# --- The producer's command line -------------------------------------------------------------

command = build_gallery.producer_command("prod.exe", 2**61 - 1, "1321", 8, 1)
check(
    command == ["prod.exe", "2305843009213693951", "--hints", "1321", "--json", "--threads", "8", "--max-ecm-levels", "1"],
    f"the command line with hints: {command}",
)
command = build_gallery.producer_command("prod.exe", 65537, None, 4, 2)
check(
    command == ["prod.exe", "65537", "--json", "--threads", "4", "--max-ecm-levels", "2"],
    f"the command line without hints: {command}",
)

# --- Entry assembly from a hand-made snapshot --------------------------------------------------

M61 = 2**61 - 1
M127 = 2**127 - 1


def prime_view(value, root, factors, state="done"):
    return {
        "value": str(value),
        "digits": len(str(value)),
        "state": state,
        "root": root,
        "factors": [str(f) for f in factors],
        "open": [],
    }


def snapshot(value, primes, status="certified"):
    return {
        "status": status,
        "message": "certified" if status == "certified" else "no factor found",
        "input": str(value),
        "primes": primes,
        "level": None,
        "searched_digits": 0,
        "open_composites": 0,
        "tasks_in_flight": 0,
        "hints_used": [],
        "hints_unused": [],
        "outputs": [
            {
                "target": "mathlib",
                "code": "import Mathlib.Tactic.Primality\n\nexample : Nat.Prime ... := by\n  primality (cert := .witnesses [...])\n",
            },
        ]
        if status == "certified"
        else [],
    }


entry_m61 = {
    "id": "m61",
    "group": "Classical families",
    "name": "Mersenne prime 2^61 - 1",
    "ref": "OEIS A000043",
    "expr": "2^61 - 1",
    "source": "test",
}
snap_m61 = snapshot(
    M61,
    [
        prime_view(M61, 37, [2, 3, 5, 7, 11, 13, 31, 41, 61, 151, 331, 1321]),
        prime_view(1321, 13, [2, 3, 5, 11]),
    ],
)
record = build_gallery.gallery_entry(entry_m61, M61, snap_m61)
check(
    record
    == {
        "id": "m61",
        "name": "Mersenne prime 2^61 - 1",
        "ref": "OEIS A000043",
        "expr": "2^61 - 1",
        "value": "2305843009213693951",
        "input": "expr",
        "digits": 19,
        "entries": 2,
        "hints": "1321:13 2305843009213693951:37",
        "source": "test",
    },
    f"the record of 2^61 - 1: {record}",
)
for expr, expected in [("2^61 - 1", "expr"), ("5*2^5947 + 1", "expr"), ("(2^2617 + 1)/3", "value"), ("427! + 1", "value"), ("fib(569)", "value")]:
    check(build_gallery.input_field(expr) == expected, f"the number box takes the {expected} of {expr}")

# The tree of 2^127 - 1 in the driver's order (input first, then descending). The hints must come
# out ascending, the input included.
tree_m127 = [
    (M127, 43, [2, 3, 7, 19, 43, 73, 127, 337, 5419, 92737, 649657, 77158673929]),
    (77158673929, 11, [2, 3, 7, 73, 699053]),
    (699053, 2, [2, 174763]),
    (649657, 5, [2, 3, 7, 1289]),
    (174763, 17, [2, 3, 7, 19, 73]),
    (92737, 5, [2, 3, 7, 23]),
    (5419, 3, [2, 3, 7, 43]),
    (1289, 6, [2, 7, 23]),
]
entry_m127 = dict(entry_m61, id="m127", name="Mersenne prime 2^127 - 1", expr="2^127 - 1", note="a note")
record = build_gallery.gallery_entry(
    entry_m127, M127, snapshot(M127, [prime_view(q, r, fs) for q, r, fs in tree_m127])
)
check(record["digits"] == 39 and record["entries"] == 8, f"digits and entries of 2^127 - 1: {record['digits']}, {record['entries']}")
check(
    record["hints"]
    == "1289:6 5419:3 92737:5 174763:17 649657:5 699053:2 77158673929:11 "
    "170141183460469231731687303715884105727:43",
    f"the hints of 2^127 - 1 are ascending with the input: {record['hints']}",
)
check(record.get("note") == "a note", "an entry's note is passed through")

# A small input has no tree and no hints.
record = build_gallery.gallery_entry(dict(entry_m61, id="p7", expr="7"), 7, snapshot(7, []))
check(record["entries"] == 0 and record["hints"] == "", "an input below 1024 has no entries")


def rejects(description, entry, value, snap):
    try:
        build_gallery.gallery_entry(entry, value, snap)
    except build_gallery.GalleryError as error:
        check(True, f"{description} is rejected: {error}")
    else:
        check(False, f"{description} is rejected")


rejects("a failed run", entry_m61, M61, snapshot(M61, [], status="failed"))
rejects("a composite verdict", entry_m61, M61, snapshot(M61, [], status="composite"))
rejects(
    "a prime still rooting",
    entry_m61,
    M61,
    snapshot(M61, [prime_view(M61, None, [2, 1321], state="rooting"), prime_view(1321, 13, [2, 3, 5, 11])]),
)
rejects("a tree without the input", entry_m61, M61, snapshot(M61, [prime_view(1321, 13, [2, 3, 5, 11])]))
rejects(
    "a snapshot for another input", entry_m61, M61, snapshot(1321, [prime_view(1321, 13, [2, 3, 5, 11])])
)

# --- Grouping --------------------------------------------------------------------------------

entries = [
    dict(entry_m61, id="a", group="G1"),
    dict(entry_m61, id="b", group="G2"),
    dict(entry_m61, id="c", group="G1"),
]
records = [{"id": "c"}, {"id": "a"}, {"id": "b"}]
groups = build_gallery.grouped(records, entries)
check(
    [(g["name"], [e["id"] for e in g["entries"]]) for g in groups] == [("G1", ["a", "c"]), ("G2", ["b"])],
    f"groups keep the entries file's order: {groups}",
)

# --- The curated entries file ----------------------------------------------------------------

curated = build_gallery.load_entries(build_gallery.ENTRIES_PATH)
check(len(curated) == 16, f"entries.json holds 16 entries ({len(curated)})")
for entry in curated:
    value = expr_eval.evaluate(entry["expr"])
    has_hints = build_gallery.hints_text(entry["id"]) is not None
    check(value > 1, f"{entry['id']}: {len(str(value))} digits, hints file {'present' if has_hints else 'absent'}")

print("\nOK" if not failures else f"\n{len(failures)} check(s) failed")
sys.exit(0 if not failures else 1)
