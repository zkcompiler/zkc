"""Valid origin families and construction coordinate checks agree independently."""

import json

import pytest

from selector_cases import (authored_helper_source, descriptor, family_source,
                            library_family_source, nonprimitive_owner_source, source)


def lean(journal, argv, reason=None):
    result = journal.attempt(argv)
    if reason:
        assert result.returncode > 0, result.stdout
        assert json.loads(result.stdout) == ['refused', reason], result.stdout
    else:
        assert result.returncode == 0, (result.stdout, result.stderr)


@pytest.mark.parametrize('origins', [('F', 'A'), ('Sampling', 'Sampling'), ('GenericDraw', 'GenericDraw'), ('F', 'F'), ('Different', 'F')])
def test_self_and_shared_origins_remain_admitted(toolchain, journal, origins):
    original = source()
    for function, origin in zip(original[2], origins):
        function[5][0] = origin
    original_path = journal.write('source.json', original)
    journal.run([toolchain.compiler, 'protocol-admit', original_path])
    lean(journal, [toolchain.checker('interactive-protocol'), '--admit', original_path])
    printed = journal.run([toolchain.compiler, 'protocol-format', original_path])
    text = journal.write('source.pir', printed)
    text.write_text(printed)
    assert json.loads(journal.run([toolchain.compiler, 'protocol-source', text])) == original
    candidate = journal.write('physical.json', json.loads(journal.run([
        toolchain.compiler, 'protocol-compile', original_path])))
    lean(journal, [toolchain.checker('interactive-protocol'), '--check', original_path, candidate])
    inputs = journal.write('inputs.json', ['zkc.run/2', 'main', 'selectors', [], [
        ['P', [], [], []], ['V', [['rng', 'coins', '2', 'entry']], [['coins', ['host', 'coins']]], []]], []])
    result = journal.attempt([toolchain.runtime, 'run-protocol', original_path, candidate, inputs,
                              toolchain.checker('interactive-protocol')])
    assert result.returncode == 0, (result.stdout, result.stderr)
    assert json.loads(result.stdout)['outcome'][0] == 'returned'


@pytest.mark.parametrize('offset', [False, True])
@pytest.mark.parametrize('reverse', [False, True])
def test_origin_family_coordinate_agreement(toolchain, journal, offset, reverse):
    original = source(offset=offset)
    original[2][0][5][0] = original[2][1][5][0] = 'F'
    if reverse:
        original[2].reverse()
    path = journal.write('source.json', original)
    # Exact selection preserves the established family semantics regardless
    # of independently allocated site numbers.
    exact = journal.write('exact.json', descriptor('exact', ['F']))
    journal.run([toolchain.compiler, 'protocol-construct', path, exact])
    normalized = journal.write('normalized.json', descriptor('normalized', ['F']))
    native = journal.attempt([toolchain.runtime, 'inspect-artifact-identity', path, normalized])
    reference = [toolchain.checker('artifact-reference'), 'identity', path, normalized]
    if offset:
        reason = 'construction-selector-coordinates'
        journal.run([toolchain.compiler, 'protocol-construct', path, normalized], refuses=reason)
        lean(journal, reference, reason)
        assert native.returncode > 0, native.stdout
        assert json.loads(native.stdout)['code'] == reason, native.stdout
    else:
        journal.run([toolchain.compiler, 'protocol-construct', path, normalized])
        lean(journal, reference)
        assert native.returncode == 0, (native.stdout, native.stderr)
        resolved = json.loads(native.stdout)['resolved_descriptor']
        assert resolved[5][1] == [['F', 'site0']]
        assert json.loads(journal.run(reference))[2] == resolved


@pytest.mark.parametrize('retains_sample', [False, True])
def test_unrelated_draw_cannot_be_selected_by_number(toolchain, journal, retains_sample):
    original = source(offset=False)
    original[2][0][5][0] = original[2][1][5][0] = 'F'
    body = original[2][1][4]
    if retains_sample:
        body[0][4] = ['r1']
        body.insert(0, ['op', 'other', 'draw', [], ['r'], ['ignored', 'r1']])
    else:
        body[0][1] = 'other'
    owners = ['F', 'A'] if retains_sample else ['F']
    path = journal.write('source.json', original)
    journal.run([toolchain.compiler, 'protocol-admit', path])
    lean(journal, [toolchain.checker('interactive-protocol'), '--admit', path])
    exact = journal.write('exact.json', descriptor('exact', owners))
    journal.run([toolchain.compiler, 'protocol-construct', path, exact],
                refuses='construction-unselected-draw')
    normalized = journal.write('normalized.json', descriptor('normalized', owners))
    reason = 'construction-selector-coordinates'
    journal.run([toolchain.compiler, 'protocol-construct', path, normalized], refuses=reason)
    lean(journal, [toolchain.checker('artifact-reference'), 'identity', path, normalized], reason)
    native = journal.attempt([toolchain.runtime, 'inspect-artifact-identity', path, normalized])
    assert native.returncode > 0 and json.loads(native.stdout)['code'] == reason, native.stdout


def coordinate_refusal(toolchain, journal, path, selection):
    reason = 'construction-selector-coordinates'
    journal.run([toolchain.compiler, 'protocol-construct', path, selection], refuses=reason)
    lean(journal, [toolchain.checker('artifact-reference'), 'identity', path, selection], reason)
    native = journal.attempt([toolchain.runtime, 'inspect-artifact-identity', path, selection])
    assert native.returncode > 0 and json.loads(native.stdout)['code'] == reason, native.stdout


@pytest.mark.parametrize('owners', [('F',), ('F', 'A')])
@pytest.mark.parametrize('nested', [False, True])
def test_forward_only_conflict_keeps_per_selector_policy(toolchain, journal, directory, owners, nested):
    # F.sample -> site1; A.sample -> site0 and A has no site1. Thus only
    # the forward check can detect losing A. Adding A would repair the whole
    # union, but deliberately does not repair the individual F selector.
    original = journal.write('source.json', family_source(padding='F', nested=nested))
    journal.run([toolchain.compiler, 'protocol-admit', original])
    lean(journal, [toolchain.checker('interactive-protocol'), '--admit', original])
    exact = journal.write('exact.json', descriptor('exact', owners))
    artifact_replay(toolchain, journal, directory, original, exact)
    selection = journal.write('normalized.json', descriptor('normalized', owners))
    coordinate_refusal(toolchain, journal, original, selection)


def test_nested_member_coordinate_conflict(toolchain, journal):
    original = journal.write('source.json', family_source(padding='A', nested=True))
    journal.run([toolchain.compiler, 'protocol-admit', original])
    lean(journal, [toolchain.checker('interactive-protocol'), '--admit', original])
    exact = journal.write('exact.json', descriptor('exact', ['F']))
    journal.run([toolchain.compiler, 'protocol-construct', original, exact])
    selection = journal.write('normalized.json', descriptor('normalized', ['F']))
    coordinate_refusal(toolchain, journal, original, selection)


@pytest.mark.parametrize('owner', ['D', 'C', 'Alias'])
@pytest.mark.parametrize('padding', [None, 'definition', 'member'])
def test_generic_and_configuration_alias_families(toolchain, journal, directory, owner, padding):
    original = journal.write('source.json', library_family_source(owner=owner, padding=padding))
    journal.run([toolchain.compiler, 'protocol-admit', original])
    lean(journal, [toolchain.checker('interactive-protocol'), '--admit', original])
    # A common member's origin can name a definition, a direct configuration,
    # or a configuration alias. None is an admission collision.
    exact = journal.write('exact.json', descriptor('exact', [owner]))
    journal.run([toolchain.compiler, 'protocol-construct', original, exact])
    selection = journal.write('normalized.json', descriptor('normalized', [owner]))
    if padding is not None:
        coordinate_refusal(toolchain, journal, original, selection)
        artifact_replay(toolchain, journal, directory, original, exact)
    else:
        native = journal.json([toolchain.runtime, 'inspect-artifact-identity', original, selection])
        reference = journal.json([toolchain.checker('artifact-reference'), 'identity', original, selection])
        assert native['admission'] == 'not-checked'
        assert native['resolved_descriptor'][5][1] == [[owner, 'site0']]
        assert reference[1:4] == [native[key] for key in (
            'resolved_source', 'resolved_descriptor', 'normalized_protocol')]
        # Inspection alone is not construction or backend admission. Exercise
        # the successful family through actual native and independent replay.
        artifact_replay(toolchain, journal, directory, original, selection)


@pytest.mark.parametrize(('origin', 'selected'), [
    ('D', 'C'), ('C', 'D'), ('C', 'Alias'), ('Alias', 'C')])
def test_unselected_alias_conflict_does_not_contaminate_selection(
        toolchain, journal, directory, origin, selected):
    value = library_family_source(owner=origin, padding='member')
    value[3][3][0][7][0][3] = 'Alias' if selected == 'Alias' else 'C'
    original = journal.write('source.json', value)
    journal.run([toolchain.compiler, 'protocol-admit', original])
    lean(journal, [toolchain.checker('interactive-protocol'), '--admit', original])
    # C and Alias both derive from D, but their selector aliases do not absorb
    # ordinary carrier members of each other's families or of D's family.
    for identity in ('exact', 'normalized'):
        partial = journal.write(f'{identity}-partial.json', descriptor(identity, [selected]))
        journal.run([toolchain.compiler, 'protocol-construct', original, partial],
                    refuses='construction-unselected-draw')
    selection = journal.write('normalized.json', descriptor('normalized', [selected, 'A']))
    artifact_replay(toolchain, journal, directory, original, selection)


@pytest.mark.parametrize('identity', ['exact', 'normalized'])
def test_authored_helper_copies_remain_usable(toolchain, journal, directory, identity):
    authored = journal.write('helper.pir', '')
    authored.write_text(authored_helper_source())
    lowered = journal.json([toolchain.compiler, 'protocol-source', authored])
    original = journal.write('source.json', lowered)
    journal.run([toolchain.compiler, 'protocol-admit', original])
    lean(journal, [toolchain.checker('interactive-protocol'), '--admit', original])
    family = [f for f in lowered[2] if f[5][0] == 'Draw']
    assert any(f[1] == 'Draw' for f in family)
    bindings = {b[0]: b[1] for b in lowered[1]}
    draws = [(f[1], i[1]) for f in family for i in f[4]
             if i[0] == 'op' and bindings[i[2]] == 'random.draw']
    assert len(draws) >= 2, family
    assert len({site for _, site in draws}) == 1, draws
    # The authored Draw entry is an adapter; raw origin selection reaches the
    # helper leaves. Normalized selection uses each actual body's own site.
    value = descriptor(identity, [])
    value[5][1] = ([['Draw', draws[0][1]]] if identity == 'exact'
                   else [[name, site] for name, site in draws])
    selection = journal.write('descriptor.json', value)
    artifact_replay(toolchain, journal, directory, original, selection)


@pytest.mark.parametrize('identity', ['exact', 'normalized'])
@pytest.mark.parametrize('conflict', [False, True])
def test_owner_coordinate_need_not_be_a_primitive(toolchain, journal, directory, identity, conflict):
    original = journal.write('source.json', nonprimitive_owner_source(conflict=conflict))
    journal.run([toolchain.compiler, 'protocol-admit', original])
    lean(journal, [toolchain.checker('interactive-protocol'), '--admit', original])
    selection = journal.write('descriptor.json', descriptor(identity, ['F', 'Leaf']))
    if identity == 'normalized' and conflict:
        # The apply is still part of F's numbering; its kind cannot bypass
        # either coordinate-direction check for sibling A's primitive.
        coordinate_refusal(toolchain, journal, original, selection)
    else:
        # F.sample is an apply, A.origin=F provides the primitive sample,
        # and Leaf.sample selects the draw reached through F's application.
        # Identity prevalidation must not mistake the coordinate owner for
        # the only possible selected primitive in this admitted family.
        artifact_replay(toolchain, journal, directory, original, selection)


@pytest.mark.parametrize('identity', ['exact', 'normalized'])
def test_coordinate_without_a_matching_primitive_is_not_a_draw(toolchain, journal, identity):
    source = nonprimitive_owner_source()
    source[2][1][5][0] = 'A'
    original = journal.write('source.json', source)
    journal.run([toolchain.compiler, 'protocol-admit', original])
    lean(journal, [toolchain.checker('interactive-protocol'), '--admit', original])
    # F.sample now reaches only a call. Selecting the real Leaf and A draws
    # cannot make the extra selector valid: coordinates alone grant nothing.
    selection = journal.write('descriptor.json', descriptor(identity, ['F', 'Leaf', 'A']))
    journal.run([toolchain.compiler, 'protocol-construct', original, selection],
                refuses='construction-draw-selector')


@pytest.mark.parametrize('identity', ['exact', 'normalized'])
@pytest.mark.parametrize('nested', [False, True])
def test_helper_family_proofs_replay_independently(toolchain, journal, directory, identity, nested):
    # Different full site maps are fine: only the selected coordinate must
    # agree. The extra primitive follows the draw, in just one family member.
    original = journal.write('source.json', family_source(nested=nested, tail=True))
    selection = journal.write('descriptor.json', descriptor(identity, ['F']))
    artifact_replay(toolchain, journal, directory, original, selection)


def artifact_replay(toolchain, journal, directory, original, selection):
    from construction import constructed_plan
    from run_reference import run_reference

    paths = constructed_plan(journal, toolchain.compiler, original, selection, '')
    inputs = journal.write('inputs.json', ['zkc.artifact-inputs/1', '', [], [],
                                          ['zkc.public-configuration/1', [], [], []]])
    proof = directory / 'proof.bin'
    arguments = [*paths, inputs, toolchain.compiler, toolchain.checker('interactive-protocol'), proof, 10000]
    produced = journal.json([toolchain.runtime, 'produce-artifact', *arguments])
    assert produced['status'] == 'produced', produced
    validated = journal.json([toolchain.runtime, 'validate-artifact', *arguments])
    assert validated['status'] == 'accepted', validated
    reference = run_reference(toolchain.checker('artifact-reference'), toolchain.primitive,
                              original, selection, inputs, proof, directory / 'reference')
    assert reference[1][0] == 'accepted', reference
    assert reference[2] == validated['events']
    assert sum(event[0] == 'challenge' for event in validated['events']) == 2
