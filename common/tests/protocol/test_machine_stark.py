"""The source machine argument through ordinary compilation and proof commands.

These tests cover the selected three-table, Boolean multiplicity profile, both
interaction reductions and the interactive entry. They provide execution and
adversarial evidence, not a proof of cryptographic soundness or upstream VM
compatibility.
"""

from entry import joint_execution, joint_artifact

from input_files import input_files
import importlib.util
import json
from pathlib import Path

import pytest

from logical_tree import decode_tree
from message_frames import tag
from test_air_stark import (FRI_REALIZATION, alter_octic_frame, check_fri_frames,
                            frames, packet_mutations, packet_rejected)

ROOT = Path(__file__).resolve().parents[3]
EXAMPLE = ROOT / 'common/tests/fixtures/projects/accumulator-machine'
FIXTURES = ROOT / 'compiler/adapters/accumulator-machine/fixtures'
_spec = importlib.util.spec_from_file_location('machine_proof_requests', EXAMPLE / 'prepare.py')
prepare = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(prepare)


def compile_entry(toolchain, journal, directory, entry, *, flags=(), source=None, edits=(), asset=None):
    flags = [FRI_REALIZATION, *flags]
    path = EXAMPLE / 'main.zkc'
    if source is not None:
        path = directory / 'main.zkc'
        path.write_text(source)
    package = directory / f'{entry}.zkpkg'
    if source is None and not edits and asset is None:
        report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                               f'--project={EXAMPLE}/zkc.toml',
                               f'accumulator_machine::{entry}', f'--output={package}', *flags], timeout=600)
        return package, report['package_sha256']
    command = [toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
               f'--module=accumulator_machine={path}',
               f'--asset=machine=relation-bundle-json={asset or FIXTURES / "bundle.json"}',
               f'accumulator_machine::{entry}', f'--output={package}', *flags]
    from source_modules import library_inputs
    modules = library_inputs('arguments/stark/whole_bundle')
    for module, module_path in modules.items():
        replacements = [(old, new) for owner, old, new in edits if owner == module]
        if replacements:
            text = module_path.read_text()
            for old, new in replacements:
                assert text.count(old) == 1, (module, old)
                text = text.replace(old, new)
            module_path = directory / (module + '.zkc')
            module_path.write_text(text)
        command.append(f'--module={module}={module_path}')
    report = journal.json(command, timeout=600)
    return package, report['package_sha256']


def requests(run, **options):
    return prepare.run_inputs(json.loads((FIXTURES / run / 'run.json').read_text()), **options)


def prove_and_verify(toolchain, journal, directory, package, pin, name, pair):
    prover = input_files(journal, name + '-prover', public=pair[0], witness=pair[1])
    verifier = input_files(journal, name + '-verifier', public=pair[0])
    proof = directory / (name + '.proof')
    produced = journal.json([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *prover, f'--output={proof}'])
    checked = journal.json([toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}'])
    assert produced['status'] == 'produced'
    assert checked['status'] == 'accepted'
    return proof, verifier


@pytest.mark.parametrize('entry', ['ProofLogUp', 'ProofProduct'])
def test_machine_proofs_produce_and_verify(toolchain, journal, directory, entry):
    package, pin = compile_entry(toolchain, journal, directory, entry)
    check_transcript_schedule(package)
    for run in ['store-load', 'arithmetic-only', 'store-load-initial-seven']:
        prove_and_verify(toolchain, journal, directory, package, pin, run, requests(run))


def alter_vector(values, position, value=None):
    changed = list(values)
    changed[position] = str((int(values[position]) + 1) % prepare.machine.P if value is None else value)
    return changed


def repack(proof, messages):
    return proof[:40] + b''.join(len(m).to_bytes(8, 'little') + m for m in messages)


def assert_refused(result):
    assert result.returncode > 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'refused', report
    return report


@pytest.mark.parametrize('entry', ['ProofLogUp', 'ProofProduct'])
def test_machine_supports_distinct_heights_and_idle_memory(toolchain, journal, directory, entry):
    package, pin = compile_entry(toolchain, journal, directory, entry)
    document = json.loads((FIXTURES / 'arithmetic-only/run.json').read_text())
    # Execution stops after row 3; the configured program retains four unused
    # instructions, and the optional memory table can be present but idle.
    document[1] += [['add-immediate', '123']] * 4
    for present in [False, True]:
        pair = prepare.run_inputs(document, memory_clocks=16, memory_present=present)
        assert (pair[0]['cpu_height'], pair[0]['program_height'],
                pair[0]['memory_height']) == ('4', '8', '32')
        prove_and_verify(toolchain, journal, directory, package, pin, f'idle-{present}', pair)


@pytest.mark.parametrize('entry,flags', [('ProofLogUp', ['--no-simplify']),
                                        ('ProofProduct', ['--release-storage']),
                                        ('ProofLogUp', ['--no-finite-bulk']),
                                        ('ProofProduct', ['--no-finite-bulk'])])
def test_machine_proof_compiler_policies(toolchain, journal, directory, entry, flags):
    package, pin = compile_entry(toolchain, journal, directory, entry, flags=flags)
    prove_and_verify(toolchain, journal, directory, package, pin, 'policy', requests('store-load'))


def test_machine_interactive_entry_runs_with_multi_megabyte_participants(toolchain, journal, directory):
    # The embedded participant exceeds the old 1 MiB producer ceiling and
    # fits the Program carrier's shared 4 MiB limit. The outer Run bundle
    # has its own separate limit.
    package, pin = compile_entry(toolchain, journal, directory, 'Run')
    bundle = joint_artifact(json.loads(package.read_text()))
    assert bundle['format'] == 'zkc.run/0' and bundle['roles'] == ['role00000000', 'role00000001']
    assert 1024 * 1024 < len(bundle['candidate'].encode()) <= 4 * 1024 * 1024
    pair = requests('store-load')
    public, private = pair[0], pair[1]

    def run(name, secret):
        inputs = input_files(journal, name + '-run.json', session='machine_' + name, package=package, arguments={'inputs': {'P': public | private | secret, 'V': public}})
        outputs = directory / (name + '-outputs.json')
        return [toolchain.runtime, '--json', 'run', f'--package={package}', f'--sha256={pin}', *inputs, f'--results={outputs}'], outputs

    command, outputs = run('honest', {})
    assert journal.json(command)['status'] == 'executed'
    assert json.loads(outputs.read_text())['value']['V'] == {'accepted': True}
    # The verifier's own checks stop the run on a false witness.
    command, outputs = run('false-witness', {'cpu': alter_vector(private['cpu'], 0)})
    report = journal.json(command, refuses='entry-host-run-failed')
    after = {role['role']: role['after'] for role in joint_execution(report)['roles']}
    assert after['role00000001'][0] == 'stopped' and after['role00000001'][1]['cause'][0] == 'explicit'
    assert not outputs.exists()


@pytest.mark.parametrize('entry', ['ProofLogUp', 'ProofProduct'])
def test_machine_rejects_false_relations_and_profiles(toolchain, journal, directory, entry):
    package, pin = compile_entry(toolchain, journal, directory, entry)
    pair = requests('store-load')
    public, private = pair[0], pair[1]
    honest, _ = prove_and_verify(toolchain, journal, directory, package, pin, 'honest', pair)
    foreign = requests('store-load-initial-seven')[1]
    changes = [
        ('cpu-arithmetic', {}, {'cpu': alter_vector(private['cpu'], 0)}),
        ('cpu-short', {}, {'cpu': prepare.vector([])}),
        ('program-multiplicity', {}, {'usage': alter_vector(private['usage'], 0, 2)}),
        ('missing-program-use', {}, {'usage': alter_vector(private['usage'], 0, 0)}),
        ('memory-count', {}, {'cells': alter_vector(private['cells'], 2, 2)}),
        ('foreign-memory', {}, {'cells': foreign['cells']}),
        ('foreign-cpu', {}, {'cpu': foreign['cpu']}),
        ('final', {'final': prepare.scalar(109)}, {}),
        ('initial', {'initial': prepare.scalar(1)}, {}),
        ('program-instruction', {'instructions': alter_vector(public['instructions'], 2)}, {}),
        ('memory-schedule', {'schedule': alter_vector(public['schedule'], 0)}, {}),
        ('memory-absent', {'memory_present': False}, {'cells': prepare.vector([])}),
        ('memory-height', {'memory_height': 8}, {}),
        ('cpu-non-power', {'cpu_height': 12}, {}),
        ('zero-shift', {'shift': prepare.scalar(0)}, {}),
        ('overlapping-domain', {'shift': prepare.scalar(1)}, {}),
        ('wrong-rounds', {'round_count': 4}, {}),
        ('wrong-channels', {'channel_count': 1}, {}),
        ('wrong-queries', {'query_count': 7}, {}),
        ('wrong-attempts', {'attempt_count': 7}, {}),
    ]
    for name, shared, secret in changes:
        prover = input_files(journal, name + '-prover.json', public=public | shared, witness=private | secret)
        verifier = input_files(journal, name + '-verifier.json', public=public | shared, witness={})
        proof = directory / (name + '.proof')
        made = journal.attempt([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *prover, f'--output={proof}'])
        if made.returncode == 0:
            # In particular, cross-table balance is a verifier obligation;
            # producing a transcript does not assert that it will be accepted.
            report = assert_refused(journal.attempt(
                [toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}']))
            assert report['code'].startswith('artifact-stopped'), (name, report)
        else:
            report = assert_refused(made)
            assert report['code'].startswith(('artifact-stopped', 'refused:vector-shape')), (name, report)
            assert not proof.exists()
        if shared:
            assert_refused(journal.attempt(
                [toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={honest}']))


@pytest.mark.parametrize('entry', ['ProofLogUp', 'ProofProduct'])
def test_machine_authenticates_all_commitment_phases(toolchain, journal, directory, entry):
    package, pin = compile_entry(toolchain, journal, directory, entry)
    proof, verifier = prove_and_verify(toolchain, journal, directory, package, pin,
                                      'honest', requests('store-load'))
    original = proof.read_bytes()
    messages = frames(original)
    # Seven original roots/claims, five common FRI roots and its terminal.
    # Each of eight positions has two FRI packets per fold, then the three
    # original table rows and paths. Deterministic requests are reconstructed.
    assert len(messages) == 13 + 16 * 8
    assert [tag(frame) for frame in messages[:7]] == [33, 35, 27, 35, 27, 27, 27]
    fri_end = 13 + 10 * 8
    check_fri_frames(messages[7:fri_end], rounds=5, queries=8, log_size=6)
    for offset in range(fri_end, len(messages), 6):
        assert [tag(frame) for frame in messages[offset:offset + 6]] == [20, 34, 27, 36, 27, 36]
    mutations = [(str(position), position, alter_octic_frame(messages[position]))
                 for position in [*range(13), *range(len(messages) - 6, len(messages))]]
    mutations.extend(packet_mutations(messages, 13, fri_end))
    for name, position, payload in mutations:
        altered = list(messages)
        altered[position] = payload
        candidate = directory / f'message-{name}.proof'
        candidate.write_bytes(repack(original, altered))
        report = assert_refused(journal.attempt(
            [toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={candidate}']))
        if 7 <= position < fri_end:
            assert report['code'] == 'rejected:require', (position, report)
            packet_rejected(report)
        else:
            assert report['code'].startswith('artifact-stopped'), (position, report)
    for name, data, code in [('truncated', original[:-1], 'proof-truncated'),
                             ('trailing', original + b'\x00', 'proof-trailing')]:
        path = directory / (name + '.proof')
        path.write_bytes(data)
        journal.run([toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={path}'], refuses=code)


def check_transcript_schedule(package):
    descriptor = json.loads(json.loads(package.read_text())['artifact'])[2]
    assert descriptor[0] == 'zkc.native-proof-descriptor/0'
    selection = json.loads(descriptor[8])
    assert selection['order'] == 'after-final-draw' and selection['authentication'] == 'atomic-blocks'
    assert {root['scheme'] for root in selection['roots']['entries']} == {
        'rows.merkle-keccak256.koala-bear.ext8-binomial3/0'}
    policy = descriptor[1]
    assert policy[7] == [str(i) for i in [0, 1, 2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 15]]
    events = []
    for kind, encoded, *bound in descriptor[3]:
        template = decode_tree(bytes.fromhex(encoded))
        assert template[0] == 'zkc.native-origin-template/0' and template[3] == []
        loops = tuple(tuple(s) for s in template[2] if s[0] == 'repeat')
        events.append((kind, loops, template[4], bound))
    # Base root; gamma/delta per channel; aux root and claims; alpha; Q root;
    # OOD samples; input/aux/Q claims; rho/eta; FRI; all original openings.
    assert [(kind, len(loops)) for kind, loops, _, _ in events] == [
        ('message', 0), ('query', 1), ('message', 1), ('query', 1), ('message', 1),
        ('message', 0), ('message', 0), ('query', 0), ('message', 0), ('message', 0),
        ('query', 1), ('message', 1), ('message', 0), ('message', 0), ('message', 0),
        ('query', 0), ('message', 0), ('query', 0), ('message', 0),
        ('message', 1), ('query', 1), ('message', 1), ('message', 0),
        ('index', 1), ('message', 1)] + [
        ('reconstructed-message', 2), ('message', 2),
        ('reconstructed-message', 2), ('message', 2),
        ('reconstructed-message', 3), ('message', 3),
        ('reconstructed-message', 3), ('message', 3)] + [('message', 1)] * 6
    draws = [1, 3, 7, 10, 15, 17, 20, 23]
    assert len(policy[8]) == len(draws)
    for (query, delivery), i in zip(policy[8], draws, strict=True):
        assert query.endswith('_' + events[i][2][2])
        assert delivery.endswith('_' + events[i + 1][2][2])
        assert events[i][2][5:7] == ['index' if i == 23 else 'draw', 'role00000001']
    assert events[23][3] == ['64']
    for i, (kind, _, event, bound) in enumerate(events):
        if kind in ('message', 'reconstructed-message'):
            assert event[4:6] == (['role00000001', 'role00000000'] if i - 1 in draws or kind == 'reconstructed-message'
                                  else ['role00000000', 'role00000001'])
            assert bound == []
    assert events[1][1] == events[2][1] == events[3][1] == events[4][1]
    assert len({events[i][1] for i in [1, 10, 19, 23, 25, 27, 29, 31, 33]}) == 9
    for i in (25, 27, 29, 31):
        assert events[i][1] == events[i + 1][1]
        assert events[i][2][2].endswith('_opening_request')
        assert events[i + 1][2][2].endswith('_opening_response')
    assert all(events[i][1][:1] == events[25][1][:1] for i in range(25, 33))
    assert events[29][1][:2] == events[31][1][:2]
    assert all(events[i][1] == events[33][1] for i in range(33, 39))


@pytest.mark.parametrize('profile', ['larger-bound', 'local', 'partial-scope', 'field-balance'])
def test_machine_refuses_other_interaction_profiles(toolchain, journal, directory, profile):
    bundle = json.loads((FIXTURES / 'bundle.json').read_text())
    if profile == 'field-balance':
        for channel in bundle[2]:
            channel[1] = 'field-balance'
        for table in bundle[3]:
            for record in table[8]:
                record[0] = 'field-balance'
                del record[4]
    else:
        record = bundle[3][0][8][0]
        if profile == 'larger-bound':
            record[-1] = 2
        elif profile == 'local':
            record[2] = ['local', 0]
        else:
            record[3] = ['first']
    asset = journal.write('bundle.json', bundle)
    entry = 'ProofProduct' if profile == 'field-balance' else 'ProofLogUp'
    package, pin = compile_entry(toolchain, journal, directory, entry, asset=asset)
    public, witness = requests('store-load')
    producer = input_files(journal, 'prover', public=public, witness=witness)
    proof = directory / 'unsupported.proof'
    report = assert_refused(journal.attempt([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *producer, f'--output={proof}']))
    assert report['code'].startswith('artifact-stopped'), report
    assert not proof.exists()
