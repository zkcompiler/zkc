"""Compiler-produced programs execute through the common Runner and Host.

Expected values, resource observations, and malformed input checks are independent
of the optional Lean research package.
"""
from pathlib import Path
import os
import sys

import pytest

from journal import Journal

ROOT = Path(__file__).resolve().parents[2]


NATIVE_CASES = [
    ('mathematical', 'mathematical_native'),
    ('mixed_mathematical', 'mixed_native'),
    ('native_boolean', 'native_boolean'),
    ('language_cli', 'language_native'),
    ('native_services', 'mathematical_services'),
    ('native_joint', 'native_joint'),
    ('native_proofs', 'native_proof'),
    ('native_attempts', 'native_attempts'),
    ('native_entry_completion', 'native_entry_completion'),
    ('native_relation_bindings', 'native_relation_bindings'),
    ('native_domains', 'native_domains'),
    ('native_index_sampling', 'native_index_sampling'),
    ('native_composition', 'native_composition'),
    ('native_setups', 'native_setups'),
    ('native_composed_state', 'native_composed_state'),
    ('native_iterated_proofs', 'native_iterated_proof'),
    ('native_committed_proofs', 'native_committed_proof'),
    ('native_structured_proofs', 'native_structured_proof'),
    ('native_nested_data', 'native_nested_data'),
    ('native_authored_transcripts', 'native_authored_transcripts'),
    ('native_iteration', 'native_iteration'),
    ('resource_origins', 'resource_origins'),
    ('structured_mathematics', 'structured_math'),
    ('relation_composition', 'relation_composition'),
    ('public_coin', 'public_coin'),
]


@pytest.mark.parametrize(('generator', 'example'), NATIVE_CASES)
def test_generated_native_execution(toolchain, directory, monkeypatch, generator, example):
    # Each invocation produces its own carriers, independent of earlier CTest
    # outputs. The generator needs compiler tools only; this test adds execution.
    reports = directory / 'generated'
    monkeypatch.setenv('ZKC_REPORTS_DIR', str(reports))
    monkeypatch.setenv('PYTHONPATH', os.pathsep.join([
        str(ROOT / 'compiler/test/support'), str(ROOT / 'tests/support')]))
    journal = Journal(directory)
    journal.run([sys.executable, ROOT / f'compiler/test/{generator}.py'])
    artifacts = list((reports / 'tests/compiler-test').iterdir())
    assert len(artifacts) == 1, artifacts
    journal.run([toolchain.driver(example), artifacts[0]])
    if example == 'language_native':
        check_source_setup_commands(toolchain, journal, artifacts[0])
    if example == 'native_joint':
        check_bundle_commands(toolchain, journal, artifacts[0])
    if example == 'native_composition':
        check_composition_commands(toolchain, journal, artifacts[0])
    if example in ('native_domains', 'native_setups'):
        check_domain_commands(toolchain, journal, artifacts[0], example == 'native_setups')
    if example == 'native_relation_bindings':
        check_relation_binding_commands(toolchain, journal, artifacts[0])
    if example == 'native_structured_proof':
        check_structured_proof_commands(toolchain, journal, artifacts[0])
    if example == 'native_composed_state':
        check_composed_state_commands(toolchain, journal, artifacts[0])
    if example == 'native_attempts':
        check_native_attempt_commands(toolchain, journal, artifacts[0])
    if example == 'native_committed_proof':
        check_committed_proof_commands(toolchain, journal, artifacts[0])
    if example == 'native_iterated_proof':
        check_iterated_proof_commands(toolchain, journal, artifacts[0])
    if example == 'native_proof':
        check_native_proof_commands(toolchain, journal, artifacts[0])
    if example == 'native_nested_data':
        check_nested_proof_commands(toolchain, journal, artifacts[0])
    if example == 'native_authored_transcripts':
        check_authored_transcript_commands(toolchain, journal, artifacts[0])


def check_authored_transcript_commands(toolchain, journal, directory):
    import hashlib
    import json

    attempt_policy = directory / 'prefix.attempts.json'
    attempt_policy.write_text(json.dumps(['zkc.native-attempt-policy/0', '1', [['2', '2']],
                                          ['3', '1048576'], ['1000000', '100000', '4294967296'],
                                          ['1048576', '16777216']]))
    prefix_summaries = {}
    for case in json.loads((directory / 'manifest.json').read_text()):
        name = case['name']
        deployment = directory / f'{name}.deployment'
        proof = directory / f'{name}.cli.proof'
        args = [deployment, hashlib.sha256(deployment.read_bytes()).hexdigest()]
        options = ['--allow-header-only']
        if case['family'] == 'prefix':
            options.append(f'--attempt-policy={attempt_policy}')
        produced = journal.json([toolchain.runtime, 'prove-bundle', *args,
                                 directory / f'{name}.producer.json', proof, *options])
        assert produced['status'] == 'produced', produced
        assert produced['binding_scope'] == 'header'
        assert produced['external_work_limit'] == 16777216
        if case['family'] == 'prefix':
            attempts = produced['attempts']
            assert attempts
            assert attempts[-1]['external_work'] == 130
            assert all(r['external_work'] == 65 for r in attempts[:-1])
            assert sum(r['external_work'] for r in produced['attempts']) == produced['external_work']
            # Test entropy forced three attempts in the Rust client. The CLI's
            # entropy is independent; compare retained effects across lowering.
            summary = json.loads((directory / f'{name}.summary.json').read_text())
            # Early completion deliberately discards a shorter prefix than the
            # final-return client. Compare each control contract across modes.
            early = case.get('early', False)
            if early not in prefix_summaries:
                prefix_summaries[early] = summary
            else:
                assert summary == prefix_summaries[early]
        checked = journal.json([toolchain.runtime, 'verify-bundle', *args,
                                directory / f'{name}.validator.json', proof, '--allow-header-only'])
        assert checked['status'] == 'accepted', checked
        assert checked['external_work_limit'] == 16777216
        assert proof.read_bytes() == (directory / f'{name}.proof').read_bytes()


def check_nested_proof_commands(toolchain, journal, directory):
    import hashlib
    import json

    for case in json.loads((directory / 'manifest.json').read_text()):
        name = case['name']
        deployment = directory / f'{name}.deployment'
        proof = directory / f'{name}.cli.proof'
        args = [deployment, hashlib.sha256(deployment.read_bytes()).hexdigest()]
        options = [f'--setups={directory / "nested.setups.json"}'] if case['family'] == 'batched-openings' else []
        if case['family'] in ('batched-openings', 'ragged-matrices', 'matrix'):
            options.append('--allow-header-only')
        produced = journal.json([toolchain.runtime, 'prove-bundle', *args,
                                 directory / f'{name}.producer.json', proof, *options])
        assert produced['status'] == 'produced'
        checked = journal.json([toolchain.runtime, 'verify-bundle', *args,
                                directory / f'{name}.validator.json', proof, *options])
        assert checked['status'] == 'accepted'
        assert proof.read_bytes() == (directory / f'{name}.proof').read_bytes()


def check_native_proof_commands(toolchain, journal, directory):
    import hashlib
    import json

    for name in ('schnorr_0', 'dleq_1', 'affine_0', 'reordered_0', 'authored'):
        deployment = directory / f'{name}.deployment'
        pin = hashlib.sha256(deployment.read_bytes()).hexdigest()
        producer = directory / f'{name}.producer.json'
        validator = directory / f'{name}.validator.json'
        proof = directory / f'{name}.cli.proof'
        args = [deployment, pin]
        # This named fixture uses an authored fixed challenge. The others use FS.
        options = ['--allow-header-only'] if name == 'authored' else []
        if name == 'authored':
            proof.write_bytes(b'previous proof')
            for command, request in [('prove-bundle', producer), ('verify-bundle', validator)]:
                refused = journal.json([toolchain.runtime, command, *args, request, proof],
                                       refuses='native-proof-binding-policy')
                assert refused['phase'] == 'admission' and refused['binding_scope'] == 'header'
                assert proof.read_bytes() == b'previous proof'
            missing = directory / 'authored.policy-unpublished'
            journal.json([toolchain.runtime, 'prove-bundle', *args, producer, missing],
                         refuses='native-proof-binding-policy')
            assert not missing.exists()
        report = journal.json([toolchain.runtime, 'prove-bundle', *args, producer, proof, *options])
        assert report['status'] == 'produced'
        assert report['binding_scope'] == ('header' if name == 'authored' else 'transcript')
        report = journal.json([toolchain.runtime, 'verify-bundle', *args, validator, proof, *options])
        assert report['status'] == 'accepted'
        report = journal.json([toolchain.runtime, 'verify-bundle', deployment, '0' * 64,
                               validator, proof], refuses='native-proof-deployment-binding')
        assert report['phase'] == 'admission'
        bad = directory / f'{name}.bad-inputs.json'
        inputs = json.loads(producer.read_text())
        if name == 'affine_0':
            next(row for row in inputs[2] if row[0] == '3')[1][1] = '0'
        else:
            inputs[4][0][1] = '0'
        bad.write_text(json.dumps(inputs))
        before = proof.read_bytes()
        report = journal.json([toolchain.runtime, 'prove-bundle', *args, bad, proof, *options],
                              refuses='exhausted')
        assert report['status'] == 'refused'
        assert proof.read_bytes() == before, 'failed production replaced a complete proof'
        missing = directory / f'{name}.unpublished'
        journal.json([toolchain.runtime, 'prove-bundle', *args, bad, missing, *options], refuses='exhausted')
        assert not missing.exists(), 'failed production published a partial proof'

    deployment = directory / 'schnorr_0.deployment'
    unexpected_authority = directory / 'unexpected.setups.json'
    unexpected_authority.write_text(json.dumps(['zkc.native-setup-authority/0', [['0', '00' * 32]], []]))
    journal.json([toolchain.runtime, 'verify-bundle', deployment,
                  hashlib.sha256(deployment.read_bytes()).hexdigest(),
                  directory / 'schnorr_0.validator.json', directory / 'schnorr_0.cli.proof',
                  f'--setups={unexpected_authority}'], refuses='native-proof-key-authority')
    assert 'EXPECTED_SHA256' in journal.run([toolchain.runtime, 'prove-bundle', '--help'])


def check_iterated_proof_commands(toolchain, journal, directory):
    import hashlib
    import json
    for family in ('sumcheck', 'cubic', 'nested'):
        for suite in range(2):
            name = f'{family}_{suite}'
            deployment = directory / f'{name}.deployment'
            args = [deployment, hashlib.sha256(deployment.read_bytes()).hexdigest()]
            producer = directory / f'{name}.producer.json'
            validator = directory / f'{name}.validator.json'
            proof = directory / f'{name}.cli.proof'
            assert journal.json([toolchain.runtime, 'prove-bundle', *args, producer, proof])['status'] == 'produced'
            assert journal.json([toolchain.runtime, 'verify-bundle', *args, validator, proof])['status'] == 'accepted'
            bad = directory / f'{name}.poor.json'
            inputs = json.loads(producer.read_text())
            inputs[5] = '0'
            bad.write_text(json.dumps(inputs))
            before = proof.read_bytes()
            journal.json([toolchain.runtime, 'prove-bundle', *args, bad, proof], refuses='exhausted')
            assert proof.read_bytes() == before
            absent = directory / f'{name}.absent'
            journal.json([toolchain.runtime, 'prove-bundle', *args, bad, absent], refuses='exhausted')
            assert not absent.exists()


def check_committed_proof_commands(toolchain, journal, directory):
    import hashlib
    import json
    for case in json.loads((directory / 'manifest.json').read_text()):
        name = case['name']
        deployment = directory / f'{name}.deployment'
        args = [deployment, hashlib.sha256(deployment.read_bytes()).hexdigest()]
        producer = directory / f'{name}.producer.json'
        validator = directory / f'{name}.validator.json'
        proof = directory / f'{name}.cli.proof'
        authority = directory / f'{name}.setups.json'
        pin = f'--setups={authority}'
        options = ['--allow-header-only'] if case['family'] in ('authored', 'structured') else []
        journal.json([toolchain.runtime, 'prove-bundle', *args, producer, proof], refuses='native-proof-key-authority')
        assert not proof.exists()
        assert journal.json([toolchain.runtime, 'prove-bundle', *args, producer, proof, pin, *options])['status'] == 'produced'
        assert journal.json([toolchain.runtime, 'verify-bundle', *args, validator, proof, pin, *options])['status'] == 'accepted'
        wrong = json.loads(authority.read_text())
        wrong[1][0][1] = '00' * 32
        wrong_authority = directory / f'{name}.wrong-setups.json'
        wrong_authority.write_text(json.dumps(wrong))
        journal.json([toolchain.runtime, 'verify-bundle', *args, validator, proof, *options,
                      f'--setups={wrong_authority}'], refuses='key-mismatch')
        bad = directory / f'{name}.missing-key.json'
        inputs = json.loads(producer.read_text())
        key = next(r for r in inputs[2] if r[1][0] == 'prover_key_file')
        key[1][1][0] = str(directory / 'missing.pk')
        bad.write_text(json.dumps(inputs))
        before = proof.read_bytes()
        journal.json([toolchain.runtime, 'prove-bundle', *args, bad, proof, pin, *options], refuses='artifact-io')
        assert proof.read_bytes() == before


def check_native_attempt_commands(toolchain, journal, directory):
    import hashlib
    import json

    for family in ('fold', 'service'):
        for suite in (0, 1):
            name = f'{family}_{suite}'
            deployment = directory / f'{name}.deployment'
            pin = hashlib.sha256(deployment.read_bytes()).hexdigest()
            producer = directory / f'{name}.producer.json'
            validator = directory / f'{name}.validator.json'
            proof = directory / f'{name}.cli.proof'
            policy = ['zkc.native-attempt-policy/0', '1', [['2', '2']] if family == 'fold' else [],
                      ['4', '16777216'], ['1000000', '100000', '4294967296'],
                      ['67108864', '268435456']]
            policy_path = directory / f'{name}.attempts'
            policy_path.write_text(json.dumps(policy))
            args = [toolchain.runtime, 'prove-bundle', deployment, pin, producer, proof,
                    f'--attempt-policy={policy_path}']
            report = journal.json(args)
            assert report['status'] == 'produced'
            assert report['proof_bytes'] == proof.stat().st_size
            assert report['attempts'][-1]['decision'] == 'complete'
            assert report['cleanup_errors'] == []
            assert len(report['attempt_policy_sha256']) == 64
            accepted = journal.json([toolchain.runtime, 'verify-bundle', deployment,
                                     pin, validator, proof])
            assert accepted['status'] == 'accepted'
            assert 'proof_bytes' not in accepted
            before = proof.read_bytes()
            # A zero instruction cap stops before protocol work; no published replacement.
            policy[4][0] = '0'
            policy_path.write_text(json.dumps(policy))
            stopped = journal.json(args, refuses='Limit')
            assert stopped['attempts'][0]['decision'] == 'stopped'
            assert stopped['instructions'] == 0
            assert proof.read_bytes() == before
            missing = directory / f'{name}.unpublished'
            args[-2] = missing
            journal.json(args, refuses='Limit')
            assert not missing.exists()
            journal.json([toolchain.runtime, 'verify-bundle', deployment, pin, validator,
                          proof, f'--attempt-policy={policy_path}'], refuses='cli-option')


def check_structured_proof_commands(toolchain, journal, directory):
    import hashlib
    import json

    for case in json.loads((directory / 'manifest.json').read_text()):
        name = case['name']
        deployment = directory / f'{name}.deployment'
        pin = hashlib.sha256(deployment.read_bytes()).hexdigest()
        options = ['--allow-header-only'] if 'standalone' in case else []
        for stem in ([name] if 'standalone' in case else
                     [f'{name}_{tag}_{count}' for tag, count in [(0, 0), (1, 4), (2, 7)]]):
            producer = directory / f'{stem}.producer.json'
            validator = directory / f'{stem}.validator.json'
            proof = directory / f'{stem}.cli.proof'
            assert journal.json([toolchain.runtime, 'prove-bundle', deployment, pin, producer, proof, *options])['status'] == 'produced'
            assert journal.json([toolchain.runtime, 'verify-bundle', deployment, pin, validator, proof, *options])['status'] == 'accepted'


def check_composed_state_commands(toolchain, journal, directory):
    import hashlib
    import json

    for family in ('fold', 'batch'):
        for suite in (0, 1):
            name = f'{family}_{suite}_normal'
            deployment = directory / f'{name}.deployment'
            pin = hashlib.sha256(deployment.read_bytes()).hexdigest()
            proof = directory / f'{name}.cli.proof'
            policy = ['zkc.native-attempt-policy/0', '1', [['4', '2']],
                      ['4', '16777216'], ['1000000', '100000', '4294967296'],
                      ['67108864', '268435456']]
            attempts = directory / f'{name}.attempts'
            attempts.write_text(json.dumps(policy))
            args = [toolchain.runtime, 'prove-bundle', deployment, pin,
                    directory / f'{name}.producer.json', proof, f'--attempt-policy={attempts}']
            result = journal.json(args)
            assert result['status'] == 'produced'
            assert result['attempts'][-1]['decision'] == 'complete'
            assert result['cleanup_errors'] == []
            assert journal.json([toolchain.runtime, 'verify-bundle', deployment,
                                 pin, directory / f'{name}.validator.json', proof])['status'] == 'accepted'
            original = proof.read_bytes()
            policy[4][0] = '0'
            attempts.write_text(json.dumps(policy))
            assert journal.json(args, refuses='Limit')['status'] == 'refused'
            assert proof.read_bytes() == original
            missing = directory / f'{name}.unpublished'
            args[-2] = missing
            journal.json(args, refuses='Limit')
            assert not missing.exists()


def check_relation_binding_commands(toolchain, journal, directory):
    import hashlib
    import json

    for case in json.loads((directory / 'manifest.json').read_text()):
        name = case['name']
        deployment = directory / f'{name}.deployment'
        args = [deployment, hashlib.sha256(deployment.read_bytes()).hexdigest()]
        # Only the explicitly derived fixtures request compiler transcript construction.
        options = [] if name.endswith('_derived') else ['--allow-header-only']
        proof = directory / f'{name}.cli.proof'
        report = journal.json([toolchain.runtime, 'prove-bundle', *args,
                               directory / f'{name}.producer.json', proof, *options])
        assert report['status'] == 'produced', report
        report = journal.json([toolchain.runtime, 'verify-bundle', *args,
                               directory / f'{name}.validator.json', proof, *options])
        assert report['status'] == 'accepted', report
        assert proof.read_bytes() == (directory / f'{name}.proof').read_bytes()
        journal.json([toolchain.runtime, 'verify-bundle', deployment, '0' * 64,
                      directory / f'{name}.validator.json', proof],
                     refuses='native-proof-deployment-binding')


def check_domain_commands(toolchain, journal, directory, setups):
    import hashlib
    import json

    cases = json.loads((directory / 'manifest.json').read_text())
    for case in cases:
        name = case['name']
        deployment = directory / f'{name}.deployment'
        args = [deployment, hashlib.sha256(deployment.read_bytes()).hexdigest()]
        options = [f'--setups={directory / (name + ".setups.json")}'] if setups else []
        # Base setup cases use authored transcripts; derived and early cases use FS.
        if setups and name != 'derived' and not case.get('early'):
            options.append('--allow-header-only')
        proof = directory / f'{name}.cli.proof'
        producer = directory / f'{name}.producer.json'
        validator = directory / f'{name}.validator.json'
        produced = journal.json([toolchain.runtime, 'prove-bundle', *args,
                                 producer, proof, *options])
        assert produced['status'] == 'produced'
        report = journal.json([toolchain.runtime, 'verify-bundle', *args,
                               validator, proof, *options], refuses=case.get('refusal'))
        if case.get('early'):
            assert produced['return_at']['site'] == 'finish_P'
            assert report['return_at']['site'] == 'finish_V'
            assert produced['messages'] == report['messages'] == 4
        else:
            assert produced['return_at'] is None
            assert report['return_at'] is None
        assert report['status'] == ('refused' if 'refusal' in case else 'accepted')
        if setups:
            journal.json([toolchain.runtime, 'verify-bundle', *args,
                          validator, proof], refuses='native-proof-key-authority')
            journal.json([toolchain.runtime, 'verify-bundle', *args,
                          validator, proof, *options, '--key-id=' + '0' * 64],
                         refuses='cli-option')
        # The host still requires an independently authorized deployment pin.
        journal.json([toolchain.runtime, 'verify-bundle', deployment,
                      '0' * 64, validator, proof, *options],
                     refuses='native-proof-deployment-binding')


def check_composition_commands(toolchain, journal, directory):
    import hashlib
    import json

    capacity = ['zkc.native-capacity/0', '65536', '8192', '16777216', '67108864',
                ['1000000', '100000', '4294967296'], ['67108864', '268435456']]
    path = directory / 'capacity.json'
    for name in ['qap-composition', 'air-composition', 'target-accumulation']:
        deployment = directory / f'{name}.deployment'
        args = [deployment, hashlib.sha256(deployment.read_bytes()).hexdigest()]
        options = [] if name == 'air-composition' else ['--allow-header-only']
        proof = directory / f'{name}.cli.proof'
        producer = directory / f'{name}.producer.json'
        validator = directory / f'{name}.validator.json'
        path.write_text(json.dumps(capacity))
        option = f'--capacity={path}'
        result = journal.json([toolchain.runtime, 'prove-bundle', *args,
                               producer, proof, *options, option])
        assert result['status'] == 'produced'
        assert result['capacity'] == capacity
        assert proof.read_bytes() == (directory / f'{name}.proof').read_bytes()
        result = journal.json([toolchain.runtime, 'verify-bundle', *args,
                               validator, proof, *options, option])
        assert result['status'] == 'accepted'
        assert result['capacity'] == capacity
        original = proof.read_bytes()
        limited = json.loads(json.dumps(capacity))
        limited[5][0] = '0'
        path.write_text(json.dumps(limited))
        result = journal.json([toolchain.runtime, 'prove-bundle', *args,
                               producer, proof, *options, option], refuses='Limit')
        assert result['capacity'] == limited
        assert result['stop']['kind'] == 'Limit'
        assert result['stop']['role'] in ('P', 'Prover')
        assert result['stop']['origin'][0] == 'zkc.origin/0'
        attempt = directory / 'excessive-attempt-policy.json'
        attempt.write_text(json.dumps(['zkc.native-attempt-policy/0', '0', [],
                                       ['1', '16777216'], capacity[5], capacity[6]]))
        journal.json([toolchain.runtime, 'prove-bundle', *args, producer,
                      proof, *options, option, f'--attempt-policy={attempt}'], refuses='native-attempt-limits')
        assert proof.read_bytes() == original
        missing = directory / f'{name}.unpublished'
        journal.json([toolchain.runtime, 'prove-bundle', *args,
                      producer, missing, *options, option], refuses='Limit')
        assert not missing.exists()
        limited[2] = '32769'
        path.write_text(json.dumps(limited))
        journal.json([toolchain.runtime, 'prove-bundle', *args,
                      producer, missing, *options, option], refuses='native-capacity-limit')
        path.write_text(json.dumps(capacity))
        journal.json([toolchain.runtime, 'prove-bundle', *args,
                      producer, missing, *options, option, option], refuses='cli-option')
        assert not missing.exists()


def check_bundle_commands(toolchain, journal, directory):
    import hashlib
    import json

    def invoke(name, go=True, options=(), refusal=None, mutate=None, pin=None):
        bundle = directory / f'{name}.bundle'
        candidate = json.loads(json.loads(bundle.read_text())['candidate'])
        roles = []
        for role in candidate[3]:
            data = []
            for i, (_, ty) in enumerate(role[4]):
                if ty == 'bool@native.bool/0':
                    value = go if role[3] == 'Bob' and i == 0 else False
                    wire = '5a4b43560005' + ('01' if value else '00')
                else:
                    assert ty == 'field:bls12-381.fr@arkworks.fr/0'
                    wire = '5a4b43560001' + (3).to_bytes(32, 'little').hex()
                data.append([str(i), ty, ['wire', wire]])
            services = [[str(i), service[1], '4'] for i, service in enumerate(role[7])]
            roles.append([role[3], data, services])
        inputs = ['zkc.bundle-inputs/0', 'installed-host', roles, []]
        if mutate:
            mutate(inputs)
        path = directory / 'bundle.inputs.json'
        path.write_text(json.dumps(inputs))
        command = [toolchain.runtime, 'run-bundle', bundle,
                   pin or hashlib.sha256(bundle.read_bytes()).hexdigest(), path, *options]
        result = journal.json(command, **({'refuses': refusal} if refusal else {}))
        assert result['format'] == 'zkc.bundle-result/0'
        assert all(r['active_frames'] == r['live_resource_units'] == 0
                   for r in result.get('roles', []))
        return result

    result = invoke('single')
    assert result['outcome'] == ['completed']
    assert result['roles'][0]['outputs'][0][2] == '5a4b4356000500'
    assert invoke('empty')['outcome'] == ['completed']
    result = invoke('foreign')
    assert result['outcome'] == ['completed']
    assert result['roles'][0]['outputs'][0] == result['roles'][1]['outputs'][0]
    assert result['roles'][1]['outputs'][1][2] == '5a4b4356000500'
    assert [r['state']['transitions'] for r in result['resources']] == [1, 1]
    result = invoke('foreign', go=False, refusal='participant-stopped')
    assert result['outcome'] == ['participant-stopped', 1]
    assert [r['state']['transitions'] for r in result['resources']] == [1, 0]
    limits = directory / 'bundle.limits.json'
    limits.write_text(json.dumps(['zkc.bundle-limits/0', '0', '4096', '16777216', '16777216']))
    result = invoke('foreign', options=[f'--limits={limits}'], refusal='driver-failed')
    assert result['limits']['execution']['steps'] == 0
    assert [r['state']['transitions'] for r in result['resources']] == [0, 0]
    result = invoke('foreign', refusal='bundle-input-port',
                    mutate=lambda v: v[2][-1][1][0].__setitem__(0, '1'))
    assert result['phase'] == 'inputs' and result['resources'] == []
    invoke('foreign', refusal='bundle-service-port',
           mutate=lambda v: v[2][0][2][0].__setitem__(1, 'random.bn254.fr/0'))
    result = invoke('single', pin='00' * 32, refusal='run-Identity')
    assert result['phase'] == 'admission' and result['resources'] == []
    invoke('single', options=['--unknown=unused'], refusal='cli-option')
    limits.write_text(json.dumps(['zkc.bundle-limits/0', '0', '4096', '16777216', '16777217']))
    invoke('single', options=[f'--limits={limits}'], refusal='bundle-limits')
    capacity = directory / 'bundle.capacity.json'
    capacity.write_text(json.dumps(['zkc.native-capacity/0', '1048577', '0', '0', '0',
                                    ['0', '0', '0'], ['0', '0']]))
    invoke('single', options=[f'--capacity={capacity}'], refusal='native-capacity-limit')
    setups = directory / 'bundle.setups.json'
    setups.write_text(json.dumps(['zkc.bundle-setups/0', [], [['Alice', '0', 'missing']]]))
    invoke('single', options=[f'--setups={setups}'], refusal='bundle-setup-authority')
    # Exact compiler bytes are reusable as the host artifact, without newline repair.
    regenerated = journal.run([toolchain.compiler, 'protocol-bundle', directory / 'foreign.mlir'])
    assert regenerated.encode() == (directory / 'foreign.bundle').read_bytes()


def check_source_setup_commands(toolchain, journal, directory):
    import hashlib
    import json
    package = directory / 'pcs-setup-Prove.entry'
    pin = hashlib.sha256(package.read_bytes()).hexdigest()
    authority = f'--setups={directory / "cli-authority.json"}'
    proof = directory / 'separate-cli-pcs-proof.bin'
    journal.run([toolchain.runtime, 'prove', package, pin, directory / 'cli-producer.json', proof, authority, '--allow-header-only'])
    journal.run([toolchain.runtime, 'verify', package, pin, directory / 'cli-verifier.json', proof, authority, '--allow-header-only'])
    key = directory / 'cli-pk-0.bin'
    unchanged = key.read_bytes()
    for output in ([key], [proof, f'--results={key}']):
        report = json.loads(journal.run([toolchain.runtime, 'prove', package, pin,
            directory / 'cli-producer.json', *output, authority, '--allow-header-only'], refuses='entry-output-path'))
        assert 'execution' not in report and key.read_bytes() == unchanged
    package = directory / 'pcs-setup-Run.entry'
    pin = hashlib.sha256(package.read_bytes()).hexdigest()
    command = [toolchain.runtime, 'run', package, pin, directory / 'cli-run.json', authority]
    journal.run(command)
    report = json.loads(journal.run([*command, f'--results={key}'], refuses='entry-output-path'))
    assert 'execution' not in report and key.read_bytes() == unchanged
