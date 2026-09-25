#!/usr/bin/env python3
"""Local algorithms through construction, Rust execution and independent Lean.

The reference computes control, origins, framing and arithmetic itself. Its
SHA256/Merlin requests use the public primitive service, not native event replies.
"""
import copy
from pathlib import Path

import pytest
from construction import constructed_plan
from journal import Journal
from toolchain import Toolchain, records

# The sources whose nested draws this constructs, both selected by the draw's
# definition: closed functions, and a generic library whose draw is reached
# directly and through a partial configuration.
FIXTURES = ("local-construction.pir", "generic-construction.pir")


# The two Lean references this drives: one consumes the admitted source and the
# candidate, the other interprets the artifact the runtime produced.
def main(fixture):
    CHECKER = "interactive-protocol"
    REFERENCE = "artifact-reference"

    tools = Toolchain()
    compiler, runtime = tools.compiler, tools.runtime
    checker, reference = tools.checker(CHECKER), tools.checker(REFERENCE)
    primitive = tools.primitive
    root = records(Path(fixture).stem)
    repository = Path(__file__).resolve().parents[2]
    journal = Journal(root)

    source = journal.json([compiler, 'protocol-source', repository / 'tests/fixtures' / fixture])
    source_path = journal.write('source.json', source)
    config = ['zkc.public-configuration/1', [], [], []]
    config_path = journal.write('configuration.json', config)
    inputs = journal.write('inputs.json', ['zkc.artifact-inputs/1', '', [], [], config])
    replies = journal.write('replies.json', ['zkc.primitive-replies/1', []])


    def build(name, source_path, descriptor):
        desc = journal.write(name + '-descriptor.json', descriptor)
        return constructed_plan(journal, compiler, source_path, desc, name + '-')


    def run_reference(paths, proof, budget):
        answers = []
        for _ in range(32):
            journal.write('replies.json', ['zkc.primitive-replies/1', answers])
            result = journal.json([reference, 'reference', *paths[:2], inputs, proof, replies, budget])
            if result[1][0] != 'pending-primitive':
                return result
            request = result[1][2]
            answer = journal.json([primitive, journal.write('request.json', request)])
            assert all(old[0] != request for old in answers)
            answers.append([request, answer])
        raise AssertionError('reference request bound')


    for version in ('exact', 'normalized'):
        descriptor = ['zkc.construction/1', 'main', 'P', 'V', [],
                      ['coins', [['Draw', 'sample']]], '0', 'merlin3.bls12-381.fr64be/1', version]
        paths = build(version, source_path, descriptor)
        proof = root / f'{version}.proof'
        produced = journal.json([runtime, 'produce-artifact', *paths, inputs, compiler, checker, proof, 100])
        assert produced['status'] == 'produced' and produced['runtime']['active_frames'] == 0
        for budget in (100, 0, 1, 2):
            result = journal.json([runtime, 'validate-artifact', *paths, inputs, compiler, checker, proof, budget], refuses=None if budget == 100 else True)
            ref = run_reference(paths, proof, budget)
            assert result['status'] == ('accepted' if budget == 100 else 'refused')
            assert ref[1][0] == ('accepted' if budget == 100 else 'exhausted'), ref[1]
            if budget != 100:
                assert result['code'] == 'exhausted:resource-budget'
            assert result['events'] == ref[2], (version, budget, 'events')
            assert result['proof_bytes'] == int(ref[4])
            assert result['runtime']['active_frames'] == 0
            journal.write(f'{version}-budget{budget}-native.json', result)
            journal.write(f'{version}-budget{budget}-reference.json', ref)
            if budget == 100:
                challenge_origins = [e[1] for e in result['events'] if e[0] == 'challenge']
                assert len(challenge_origins) == 2 and len(set(challenge_origins)) == 2
        if version == 'normalized':
            native = journal.json([runtime, 'inspect-artifact-identity', *paths[:2], config_path])
            independent = journal.json([reference, 'identity', *paths[:2], config_path])
            assert native['normalized_protocol'] == independent[3]
            assert native['resolved_source'] == independent[1]
            assert native['resolved_descriptor'] == independent[2]
            # Labels resolve before expansion, so relabeling nested call/leaf sites
            # keeps the normalized transcript and the already produced proof.
            renamed = copy.deepcopy(source)
            definitions, body_index = (renamed[1], 6) if renamed[0] == 'zkc.library/1' else (renamed[2], 4)
            definitions[0][body_index][0][1] = 'renamed_leaf'
            definitions[1][body_index][0][1] = 'renamed_first'
            definitions[1][body_index][1][1] = 'renamed_second'
            if renamed[0] == 'zkc.library/1':
                # Nested value binders are normalized as well as sites.
                aliases = {'r': 'seed', 'x': 'drawn', 'next': 'next_seed',
                           'a': 'first_value', 'b': 'second_value', 'r1': 'first_seed', 'r2': 'second_seed'}
                def rename_values(value):
                    if isinstance(value, list):
                        return [rename_values(v) for v in value]
                    return aliases.get(value, value) if isinstance(value, str) else value
                for definition in definitions[:2]:
                    definition[4] = rename_values(definition[4])
                    definition[body_index] = rename_values(definition[body_index])
            descriptor[5][1][0][1] = 'renamed_leaf'
            renamed_paths = build('relabeled', journal.write('relabeled-source.json', renamed), descriptor)
            result = journal.json([runtime, 'validate-artifact', *renamed_paths, inputs, compiler, checker, proof, 100])
            assert result['status'] == 'accepted'
            ref = run_reference(renamed_paths, proof, 100)
            assert ref[1][0] == 'accepted' and result['events'] == ref[2]
            # A transitive helper's body contributes to identity.
            changed = copy.deepcopy(source)
            if changed[0] == 'zkc.library/1':
                changed[1][0][6].insert(1, ['op', 'comparison', 'field.equal', ['F'], [], ['x', 'x'], ['same']])
            else:
                changed[2][0][4].insert(1, ['op', 'comparison', 'equal', [], ['x', 'x'], ['same']])
            # The additional primitive is well typed and contributes to identity.
            changed_path = journal.write('changed-helper.json', changed)
            different = journal.json([runtime, 'inspect-artifact-identity', changed_path, paths[1], config_path])
            assert different['normalized_protocol'] != native['normalized_protocol']
            journal.json([compiler, 'protocol-source', changed_path])
            other = journal.json([reference, 'identity', changed_path, paths[1], config_path])
            assert different['normalized_protocol'] == other[3]
            if source[0] == 'zkc.library/1':
                # A partial configuration reached only by a nested apply is in the closure.
                configs = native['normalized_protocol'][6]
                assert any(c[1] == 'SelectedDraw' for c in configs)
                assert {d[1] for d in native['normalized_protocol'][5]} == {'Draw', 'Two', 'Check'}
    print(f'{journal.save()} local composition artifact checks passed')



@pytest.mark.parametrize("fixture", FIXTURES)
def test_local_composition(fixture):
    main(fixture)


if __name__ == "__main__":
    for fixture in FIXTURES:
        main(fixture)
