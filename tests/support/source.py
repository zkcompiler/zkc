"""The vocabulary these tests use to write a source, an input and an outcome.

A cross-build test states a small program, the values it is invoked with and
what every implementation of it must produce. These constructors keep that
statement readable, and keep the portable encoding in one place: when the
encoding changes, it changes here rather than in each test.
"""

import sys

sys.set_int_max_str_digits(0)

BOOL = ["bool"]
DIGEST = ["digest"]


def scalar(domain):
    return ["scalar", domain]


def table(domain, arity):
    return ["table", domain, arity]


def point(domain):
    return ["point", domain]


def residual(domain, arity):
    return ["residual", domain, arity]


def apply(operation, arguments, rest):
    return ["apply", operation, arguments, rest]


def ret(index):
    return ["return", index]


def stop(reason):
    return ["stop", reason]


def pair(a, b):
    """Cantor-style pairing, as the ordered digest vocabulary defines it."""
    return b * b + a if a < b else a * a + a + b


def mle(cells, coordinates, modulus):
    """The multilinear extension, summed over the Boolean basis.

    Deliberately independent of the native fold: a test that computed the value
    the way the implementation does would agree with a wrong implementation.
    """
    total = 0
    n = len(coordinates)
    for i, cell in enumerate(cells):
        term = cell
        for j, coordinate in enumerate(coordinates):
            term *= coordinate if i >> (n - 1 - j) & 1 else 1 - coordinate
        total += term
    return total % modulus


def bind(type_, body, rest):
    return ["bind", type_, body, rest]


TERMINAL = ["terminal"]


def certificate(body):
    """The admission certificate a body admits to, written from the body itself.

    Admission asks whether a candidate plan matches the source it claims to
    realize. A test states the source, so it can state the certificate too,
    rather than asking the implementation under test what the answer is.
    """
    match body:
        case ["apply", _, _, rest]:
            return ["next", certificate(rest)]
        case ["if", _, yes, no]:
            return ["branch", certificate(yes), certificate(no)]
        case ["bind", _, body, rest]:
            return ["bind", certificate(body), certificate(rest)]
        case ["repeat", _, _, _, body, rest]:
            return ["loop", ["ready"], certificate(body), certificate(rest)]
        case ["return", _] | ["stop", _]:
            return TERMINAL
        case _:
            raise ValueError(body)


def envelope(context, body, profile="finite-source-1"):
    """The record a source is carried in: its profile, context and body.

    This is a carrier format, which at v0 may change freely, so the tests that
    write one should not each know its shape. Both suites build sources, and
    the context differs between them -- a table protocol here, a vector service
    there -- so the context is the caller's and the record around it is not.
    """
    return ["zkc-request", 1, profile, context, [], body]


def trace(declarations, result):
    """The ordinary context: what the source is given, and what it answers."""
    return ["trace", declarations, result, [["table-protocol", "1"]]]


def request(inputs, result, body, profile="finite-source-1"):
    """A complete source: its declarations, its result type and its body."""
    declarations = [
        [name, type_, ["shared"], "capture" if captured else "argument"]
        for name, type_, _, captured in inputs
    ]
    return envelope(trace(declarations, result), body, profile)


def invocation(inputs, state=None):
    """The values a source is invoked with, and the state it starts from."""
    return [
        [[name, type_, value] for name, type_, value, _ in inputs],
        state or EMPTY_STATE,
    ]


EMPTY_STATE = [0, 0, 0, [], []]


def executed(value, state=None, events=None):
    """A complete execution that returned this value."""
    return {
        "status": "executed",
        "outcome": ["returned", value],
        "state": state or EMPTY_STATE,
        "events": events or [],
    }


def stopped(reason, state=None, events=None):
    """A complete execution that stopped for this reason."""
    return {
        "status": "executed",
        "outcome": ["stopped", reason],
        "state": state or EMPTY_STATE,
        "events": events or [],
    }


def refused(code, state=None):
    """Admission refused before execution began."""
    return {
        "status": "start-failed",
        "code": code,
        "state": state or EMPTY_STATE,
        "events": [],
    }
