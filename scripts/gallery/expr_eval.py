"""The evaluator of the gallery's integer expressions.

usage (as a script): expr_eval.py EXPR    prints the value

An expression has decimal and `0x` literals, `+ - * / ^` with the usual precedence (`^`
right-associative), unary minus, parentheses, postfix `!` (factorial) and `#` (primorial), and
`fib(n)` with fib(1) = fib(2) = 1. Division must be exact. Anything else is an error.
"""

import re
import sys

# Bounds that keep a typo from hanging the evaluator. The result size is checked before a `^` and
# after every other operation that can grow.
MAX_EXPONENT = 1_000_000
MAX_RESULT_BITS = 1_000_000
MAX_FACTORIAL = 5_000
MAX_PRIMORIAL = 50_000
MAX_FIB = 50_000

# Whitespace (skipped), or a number, a name or an operator, each in its own group.
TOKEN = re.compile(r"\s+|(0[xX][0-9a-fA-F]+|[0-9]+)|([A-Za-z_][A-Za-z_0-9]*)|([-+*/^!#()])")


class ExprError(ValueError):
    """Anything outside the grammar, or an operation the bounds reject."""


def evaluate(text):
    """The value of `text` as an int; raises ExprError for anything outside the grammar."""
    parser = Parser(tokenize(text))
    value = parser.sum()
    rest = parser.peek()
    if rest[0] != "end":
        raise ExprError(f"unexpected {describe(rest)}")
    return value


def tokenize(text):
    """The tokens of `text`, each `(type, value)` with type one of number, name, op, end."""
    tokens = []
    position = 0
    while position < len(text):
        match = TOKEN.match(text, position)
        if match is None:
            raise ExprError(f"unexpected character {text[position]!r}")
        position = match.end()
        number, name, op = match.groups()
        if number is not None:
            tokens.append(("number", int(number, 16) if number[:2] in ("0x", "0X") else int(number)))
        elif name is not None:
            tokens.append(("name", name))
        elif op is not None:
            tokens.append(("op", op))
    tokens.append(("end", ""))
    return tokens


def describe(token):
    kind, value = token
    return "end of expression" if kind == "end" else f"{kind} {value!r}"


class Parser:
    """Recursive descent over the tokens, one method per precedence level."""

    def __init__(self, tokens):
        self.tokens = tokens
        self.position = 0

    def peek(self):
        return self.tokens[self.position]

    def next(self):
        token = self.tokens[self.position]
        self.position += 1
        return token

    def is_op(self, op):
        """Whether the next token is the operator `op`."""
        return self.peek() == ("op", op)

    def expect_op(self, op):
        if not self.is_op(op):
            raise ExprError(f"expected {op!r}, found {describe(self.peek())}")
        self.next()

    def sum(self):
        """sum := product (('+' | '-') product)*"""
        value = self.product()
        while self.is_op("+") or self.is_op("-"):
            op = self.next()[1]
            right = self.product()
            value = value + right if op == "+" else value - right
        return value

    def product(self):
        """product := unary (('*' | '/') unary)*"""
        value = self.unary()
        while self.is_op("*") or self.is_op("/"):
            op = self.next()[1]
            right = self.unary()
            value = sized(value * right, "*") if op == "*" else exact_divide(value, right)
        return value

    def unary(self):
        """unary := '-' unary | power"""
        if self.is_op("-"):
            self.next()
            return -self.unary()
        return self.power()

    def power(self):
        """power := postfix ('^' unary)?   (right-associative through `unary`)"""
        base = self.postfix()
        if self.is_op("^"):
            self.next()
            return power(base, self.unary())
        return base

    def postfix(self):
        """postfix := primary ('!' | '#')*"""
        value = self.primary()
        while True:
            if self.is_op("!"):
                self.next()
                value = factorial(value)
            elif self.is_op("#"):
                self.next()
                value = primorial(value)
            else:
                return value

    def primary(self):
        """primary := number | '(' sum ')' | 'fib' '(' sum ')'"""
        kind, value = self.next()
        if kind == "number":
            return value
        if kind == "op" and value == "(":
            inner = self.sum()
            self.expect_op(")")
            return inner
        if kind == "name":
            if value != "fib":
                raise ExprError(f"unknown function {value!r}")
            self.expect_op("(")
            argument = self.sum()
            self.expect_op(")")
            return fib(argument)
        raise ExprError(f"unexpected {describe((kind, value))}")


def exact_divide(a, b):
    if b == 0:
        raise ExprError("division by zero")
    quotient, remainder = divmod(a, b)
    if remainder != 0:
        raise ExprError(f"inexact division {a} / {b}")
    return quotient


def power(base, exponent):
    if exponent < 0:
        raise ExprError(f"negative exponent {exponent}")
    if exponent > MAX_EXPONENT:
        raise ExprError(f"exponent {exponent} is above {MAX_EXPONENT}")
    if abs(base).bit_length() * exponent > MAX_RESULT_BITS:
        raise ExprError(f"the result of ^ would exceed {MAX_RESULT_BITS} bits")
    return base**exponent


def sized(value, operator):
    """`value`, the result of `operator`, when it fits MAX_RESULT_BITS; the error names the
    operator."""
    if abs(value).bit_length() > MAX_RESULT_BITS:
        raise ExprError(f"the result of {operator} exceeds {MAX_RESULT_BITS} bits")
    return value


def factorial(n):
    count = small_argument(n, MAX_FACTORIAL, "!")
    value = 1
    for i in range(2, count + 1):
        value *= i
    return sized(value, "!")


def primorial(n):
    """The product of the primes up to `n` (1 for `n < 2`), by a sieve."""
    bound = small_argument(n, MAX_PRIMORIAL, "#")
    composite = bytearray(bound + 1)
    value = 1
    for p in range(2, bound + 1):
        if composite[p]:
            continue
        value *= p
        for multiple in range(p * p, bound + 1, p):
            composite[multiple] = 1
    return sized(value, "#")


def fib(n):
    index = small_argument(n, MAX_FIB, "fib")
    a, b = 0, 1
    for _ in range(index):
        a, b = b, a + b
    return sized(a, "fib")


def small_argument(n, bound, operator):
    """`n` when it is in `0 … bound`; the error names the operator otherwise."""
    if n < 0:
        raise ExprError(f"negative argument {n} of {operator}")
    if n > bound:
        raise ExprError(f"argument {n} of {operator} is above {bound}")
    return n


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__.strip())
    try:
        print(evaluate(sys.argv[1]))
    except ExprError as error:
        sys.exit(f"error: {error}")
