#!/usr/bin/env python3
"""Runs the command-line tool on every input of inputs.txt and every gallery entry, checks that each
output is a `primality` invocation proving `Nat.Prime` of its number, and writes all of them into
target/certificates.lean, for `lake env lean` in a Mathlib checkout. Exits 0 when every check holds.

usage: python tests/certificates/check.py
"""

import ast
import json
import operator
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
OUT = os.path.join(ROOT, "target", "certificates.lean")
# Below this, the tool proves the input by `primality` alone (its witness bound).
WITNESS_BOUND = 1024
IMPORTS = ["Mathlib.Tactic.Primality", "Mathlib.Tactic.NormNum.Pow"]
EXAMPLE = re.compile(
    r"(?:set_option exponentiation\.threshold \d+ in\n)?"
    r"example : Nat\.Prime (?P<statement>.+) := by(?P<proof>.*)",
    re.DOTALL,
)
ENTRY = r"    \.lucas \{ root := \d+, primeFactors := \[\d+(?:, \d+)*\] \}"
CERTIFICATE = re.compile(rf"\n  primality \(cert := \.witnesses \[\n(?:{ENTRY},\n)*{ENTRY}\]\)\n")
OPERATORS = {
    ast.Add: operator.add,
    ast.Sub: operator.sub,
    ast.Mult: operator.mul,
    ast.Pow: operator.pow,
}


def value_of(text):
    """The value of `text`, a numeral or an expression in `+ - * ^` and parentheses."""

    def walk(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return node.value
        if isinstance(node, ast.BinOp) and type(node.op) in OPERATORS:
            return OPERATORS[type(node.op)](walk(node.left), walk(node.right))
        raise ValueError(f"not a numeral or an expression in + - * ^: {text!r}")

    return walk(ast.parse(text.replace("^", "**"), mode="eval").body)


def cases():
    """The (label, input, hints) of every input to check."""
    with open(os.path.join(HERE, "inputs.txt"), encoding="utf-8") as file:
        for line in file:
            line = line.strip()
            if line and not line.startswith("#"):
                yield line, line, ""
    with open(os.path.join(ROOT, "web", "gallery.json"), encoding="utf-8") as file:
        gallery = json.load(file)
    for group in gallery["groups"]:
        for entry in group["entries"]:
            yield entry["id"], entry["number"], entry["hints"]


def certificate(text, hints):
    """The tool's output for `text` as (imports, example). Raises ValueError naming the problem."""
    value = value_of(text)
    command = ["cargo", "run", "--quiet", "--locked", "--", text, "--quiet", "--target", "mathlib"]
    if hints:
        command += ["--hints", hints]
    run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, encoding="utf-8")
    if run.returncode != 0:
        raise ValueError(f"the tool exited with code {run.returncode}: {run.stdout}{run.stderr}")
    lines = run.stdout.splitlines(keepends=True)
    imports = [line.split()[1] for line in lines if line.startswith("import ")]
    if not imports or set(imports) - set(IMPORTS):
        raise ValueError(f"unexpected imports {imports}")
    example = "".join(lines[len(imports) :]).lstrip("\n")
    match = EXAMPLE.fullmatch(example)
    if match is None:
        raise ValueError(f"not an example proving Nat.Prime:\n{example}")
    if value_of(match["statement"]) != value:
        raise ValueError(f"the statement {match['statement']} is not the input")
    if value < WITNESS_BOUND:
        if match["proof"] != " primality\n":
            raise ValueError(
                f"expected `by primality` below {WITNESS_BOUND}, found{match['proof']}"
            )
    elif CERTIFICATE.fullmatch(match["proof"]) is None:
        raise ValueError(f"expected `primality` with a witness certificate, found{match['proof']}")
    return imports, example


def main():
    imports, examples, failures = set(), [], 0
    for label, text, hints in cases():
        try:
            used, example = certificate(text, hints)
        except ValueError as error:
            print(f"FAIL {label}: {error}")
            failures += 1
            continue
        print(f"ok   {label}")
        imports.update(used)
        examples.append(f"-- {label}\n{example}")
    if failures:
        sys.exit(f"{failures} input(s) failed")
    header = "".join(f"import {name}\n" for name in IMPORTS if name in imports)
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8", newline="\n") as file:
        file.write(header + "\n" + "\n".join(examples))
    print(f"wrote {OUT} ({len(examples)} certificates)")


if __name__ == "__main__":
    main()
