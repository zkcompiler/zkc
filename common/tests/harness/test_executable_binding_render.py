"""Physical specialization survives rendering; the Lean vocabulary admits it."""

import hashlib
import json
import pytest
from harness import load


def renderer():
    return load('executable_binding_render', 'lean/bridges/executable/render.py')


def deployment(arguments):
    binding = ['operation', 'field.add', ['bls12-381.fr'], 'arkworks/field.add', arguments]
    function = ['function', 'helper', [], [],
                [['op', 'site', 'operation', [], [], []], ['ret', []]], None]
    participant = ['participant', 'validator', 'entry', 'V', [], [],
                   [['local', 'site', 'helper', [], []], ['return', []]], []]
    program = json.dumps(['zkc.program/0', [binding], [function], [participant],
                          [['entry', 'entry', [['V', 'validator']]]]])
    return ['zkc.native-proof/0', '', ['', ['', 'entry', 'P', 'V']], '', program,
            hashlib.sha256(program.encode()).hexdigest(), None, None, None]


def test_physical_arguments_are_preserved_as_typed_data():
    render = renderer().render
    empty = render(deployment([]), 'Control')
    physical = render(deployment(['field:bls12-381.fr@arkworks.fr/0']), 'Control')
    assert '"arkworks/field.add", []⟩' in empty
    assert '"arkworks/field.add", [⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩]⟩' in physical
    assert empty != physical
    # Syntactically valid but uninstalled data remains visible for Lean to refuse.
    assert '"other.fr/0"' in render(deployment(['field:bls12-381.fr@other.fr/0']), 'Control')


@pytest.mark.parametrize('arguments', [None, 'field:bls12-381.fr@arkworks.fr/0', [True],
                                      ['field:bls12-381.fr'], ['array<field>@aggregate/layout']])
def test_malformed_or_unsupported_physical_arguments_are_refused(arguments):
    with pytest.raises(ValueError):
        renderer().render(deployment(arguments), 'Control')


def test_old_four_field_binding_is_refused():
    value = deployment([])
    program = json.loads(value[4])
    program[1][0].pop()
    value[4] = json.dumps(program)
    value[5] = hashlib.sha256(value[4].encode()).hexdigest()
    with pytest.raises(ValueError, match='expected array of size 5'):
        renderer().render(value, 'Control')
