"""Variants of a callable-expansion source that both implementations judge.

A callable is expanded away before a plan exists, so what a plan is allowed to
be depends on what the calls in the source were. These three edits state the
cases that matter: a second caller of the same callable, two callables that
call each other, and a callable that returns its argument unchanged so that a
plan compiled from a changed body no longer matches the source it claims.

The compiler's own test and the cross-build test both judge these, so they are
built here rather than written out twice and allowed to drift apart.
"""

import copy


def nested(source):
    """A second callable that calls the one the protocol already calls.

    The protocol calls the wrapper instead, so the expansion has two call edges
    to follow and both origins have to survive to the plan.
    """
    value = copy.deepcopy(source)
    wrapper = copy.deepcopy(source[2][2])
    wrapper[1] = wrapper[5][0] = "Nested"
    wrapper[4] = [["apply", "inner", "Linear", [], ["g", "x"], ["r"]], ["return", ["r"]]]
    value[2].append(wrapper)
    value[2].reverse()
    value[3][0][7][0][3] = "Nested"
    return value


def cycle(source):
    """Two callables that call each other, which no expansion can finish."""
    value = copy.deepcopy(source)
    value[2][0][4] = [["apply", "back", "Again", [], ["x"], ["y"]], ["return", ["y"]]]
    again = copy.deepcopy(value[2][0])
    again[1] = again[5][0] = "Again"
    again[4][0][2] = "Twice"
    value[2].append(again)
    return value


def with_identity(source):
    """The same source with a callable that returns its argument unchanged.

    Redirecting a call to it changes what the protocol computes without
    changing anything an unexpanded reading of the source would notice.
    """
    value = copy.deepcopy(source)
    identity = copy.deepcopy(source[2][0])
    identity[1] = identity[5][0] = "Identity"
    identity[4] = [["return", ["x"]]]
    value[2].append(identity)
    return value
