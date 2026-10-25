"""Executable imports retain physical specialization for independent admission."""

import json

import pytest

from harness import load


@pytest.fixture
def renderer():
    return load("executable_binding_render", "lean/bridges/executable/render.py")


def deployment(renderer, physical_arguments):
    program = ["zkc.program/0", [["observe", "transcript.native.indexed.observe.data",
        ["merlin3.bls12-381.fr64be/0", "field:bls12-381.fr"],
        "arkworks/transcript.native.indexed.observe.data", physical_arguments]],
        [["function", "helper", [], [],
          [["op", "site", "observe", [], [], []], ["return", []]], None]],
        [["participant", "validator", "proof", "verifier", [], [],
          [["local", "call", "helper", [], []], ["return", []]], []]],
        [["entry", "proof", [["verifier", "validator"]]]]]
    candidate = json.dumps(program)
    return ["zkc.native-proof/0", None, [None, [None, "proof", None, "verifier"]],
            None, candidate, renderer.lean_render.digest(candidate.encode()), None, None, None]


def test_explicit_layout_is_retained_instead_of_erased(renderer):
    default = renderer.render(deployment(renderer, []), "Example")
    explicit = renderer.render(deployment(renderer, ["field:bls12-381.fr@arkworks.fr/0"]), "Example")
    assert default != explicit
    assert '"arkworks/transcript.native.indexed.observe.data", []⟩' in default
    assert '"arkworks/transcript.native.indexed.observe.data", [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩]⟩' in explicit


def test_unknown_well_formed_layout_reaches_the_lean_vocabulary(renderer):
    rendered = renderer.render(deployment(renderer, ["field:bls12-381.fr@foreign.fr/0"]), "Example")
    assert '"foreign.fr/0"' in rendered


@pytest.mark.parametrize("arguments", [None, {}, "field:bls12-381.fr@arkworks.fr/0",
    ["field:bls12-381.fr"], ["field:bls12-381.fr@"], ["field:bls12-381.fr@@arkworks.fr/0"], [1]])
def test_malformed_physical_arguments_are_refused(renderer, arguments):
    with pytest.raises(renderer.Refused):
        renderer.render(deployment(renderer, arguments), "Example")
