"""EIP-4844 KZG through ordinary Entries, against the pinned c-kzg-4844 corpora.

vectors.json holds the upstream vectors; extra.json holds derived malformed,
changed, duplicated and reordered cases whose outcomes the pinned c-kzg-4844
reference computed. Outcomes compare three ways: an accepted proof is true, a
rejected one false, and a stopped participant matches an upstream error.
"""
import hashlib
import json
import subprocess
import sys

import pytest

from test_source_projects import ROOT, build

PROJECT = 'examples/projects/eip4844'
FIXTURES = ROOT / 'common/tests/fixtures/kzg-eip4844'
CORPUS = json.loads((FIXTURES / 'vectors.json').read_text())
EXTRA = json.loads((FIXTURES / 'extra.json').read_text())
SETUP = ROOT / 'libraries/kzg/eip4844/trusted_setup.txt'
R = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001


def cases(function, corpus=CORPUS):
    return [case for case in corpus['cases'] if case['function'] == function]


def named(function, name):
    return next(case for case in cases(function) if case['name'] == name)


def blob(key):
    return bytes.fromhex(CORPUS['blobs'][key])


def hexes(value):
    if isinstance(value, list):
        return [hexes(v) for v in value]
    return value if value is None or isinstance(value, bool) else bytes.fromhex(value)


def shown(value):
    """A JSON-serializable record of a result for the check journal."""
    if isinstance(value, list):
        return [shown(v) for v in value]
    return value.hex() if isinstance(value, bytes) else value


def frame(tag, payload, count=None):
    """A native ZKCV frame with a u32 element count."""
    return b'ZKCV\x00' + bytes([tag]) + (len(payload) if count is None else count).to_bytes(4, 'little') + payload


def setup_words():
    words = SETUP.read_text().split()
    assert words[:2] == ['4096', '65']
    return words


def lagrange():
    """The ceremony's G1 Lagrange points, in file order, as one G1 vector frame."""
    return frame(67, b''.join(bytes.fromhex(word) for word in setup_words()[2:2 + 4096]), 4096)


def g2_monomial(index):
    return bytes.fromhex(setup_words()[2 + 4096 + index])


class Inputs:
    """Input documents whose large values are pinned frame files beside them."""

    def __init__(self, directory, name):
        self.directory = directory / name
        self.directory.mkdir(parents=True, exist_ok=True)
        self.values = {}

    def file(self, name, data):
        (self.directory / name).write_bytes(data)
        return {'file': name, 'sha256': hashlib.sha256(data).hexdigest()}

    def bytes(self, name, data):
        return self.file(f'{name}.zkcv', frame(70, data)) if len(data) > 1024 else list(data)

    def setup(self):
        return self.file('setup.zkcv', lagrange())

    def document(self, name, values):
        path = self.directory / f'{name}.json'
        path.write_text(json.dumps(values))
        return path


class Entries:
    """Compiled example Entries, each built once per test."""

    def __init__(self, toolchain, journal, directory):
        self.toolchain, self.journal, self.directory = toolchain, journal, directory
        self.packages = {}

    def package(self, entry):
        if entry not in self.packages:
            self.packages[entry] = build(self.toolchain, self.journal, self.directory, PROJECT, entry, [])
        return self.packages[entry]

    def run(self, entry, inputs):
        """Returned role outputs, or None after a participant stop."""
        package, pin = self.package(entry)
        document = inputs.document('P', inputs.values)
        output = inputs.directory / 'outputs.json'
        result = self.journal.attempt([self.toolchain.runtime, '--json', 'run', f'--package={package}',
                                       f'--sha256={pin}', '--session=vectors', f'--input=P={document}',
                                       f'--results={output}'])
        report = self.journal.parse(result)
        if report.get('status') == 'executed':
            return json.loads(output.read_text())['roles']['P']
        assert report.get('code') == 'entry-run-incomplete', report
        assert report['execution']['outcome'][0] == 'participant-stopped', report
        return None

    def verify(self, entry, inputs, public, proof):
        """True on acceptance, False on rejection, None when the verifier stops."""
        package, pin = self.package(entry)
        (inputs.directory / 'proof.bin').write_bytes(proof)
        result = self.journal.attempt([self.toolchain.runtime, '--json', 'verify', f'--package={package}',
                                       f'--sha256={pin}', f'--public={inputs.document("public", public)}',
                                       f'--proof={inputs.directory / "proof.bin"}', '--allow-authored'])
        report = self.journal.parse(result)
        if report.get('status') == 'accepted':
            return True
        code = report.get('code', '')
        if code == 'artifact-rejected':
            return False
        # A stopped verifier, or proof bytes too short for the next message.
        assert code.startswith('artifact-stopped') or code == 'refused:bytes-bounds', report
        return None

    def prove(self, entry, inputs, public, witness):
        """The produced proof bytes, or None when the prover stops."""
        package, pin = self.package(entry)
        proof = inputs.directory / 'produced.bin'
        result = self.journal.attempt([self.toolchain.runtime, '--json', 'prove', f'--package={package}',
                                       f'--sha256={pin}', f'--public={inputs.document("public", public)}',
                                       f'--witness={inputs.document("witness", witness)}',
                                       f'--output={proof}', '--allow-authored'])
        report = self.journal.parse(result)
        if report.get('status') == 'produced':
            return proof.read_bytes()
        assert report.get('code', '').startswith('artifact-stopped'), report
        assert not proof.exists()
        return None


@pytest.fixture
def entries(toolchain, journal, directory):
    return Entries(toolchain, journal, directory)


def outcome(entries, directory, case):
    """Evaluate one corpus case through the Entry that implements its function."""
    function, values = case['function'], case['input']
    inputs = Inputs(directory, f'{function}-{case["name"]}')
    if function == 'compute_challenge':
        inputs.values = {'blob': inputs.bytes('blob', blob(values['blob'])),
                         'commitment': inputs.bytes('commitment', hexes(values['commitment']))}
        roles = entries.run('ComputeChallenge', inputs)
        return bytes(roles['challenge']) if roles else None
    if function == 'blob_to_kzg_commitment':
        inputs.values = {'blob': inputs.bytes('blob', blob(values['blob'])), 'setup': inputs.setup()}
        roles = entries.run('BlobToCommitment', inputs)
        return bytes(roles['commitment']) if roles else None
    if function == 'compute_kzg_proof':
        inputs.values = {'blob': inputs.bytes('blob', blob(values['blob'])),
                         'z': list(hexes(values['z'])), 'setup': inputs.setup()}
        roles = entries.run('ComputeKzgProof', inputs)
        return [bytes(roles['proof']), bytes(roles['y'])] if roles else None
    if function == 'compute_blob_kzg_proof':
        public = {'blob': inputs.bytes('blob', blob(values['blob'])),
                  'commitment': list(hexes(values['commitment']))}
        proof = entries.prove('BlobProof', inputs, public, {'setup': inputs.setup()})
        # A produced proof must also verify under the same statement.
        assert proof is None or entries.verify('BlobProof', inputs, public, proof) is True
        return proof
    if function == 'verify_kzg_proof':
        public = {key: list(hexes(values[key])) for key in ('commitment', 'z', 'y')}
        return entries.verify('KzgProof', inputs, public, hexes(values['proof']))
    if function == 'verify_blob_kzg_proof':
        public = {'blob': inputs.bytes('blob', blob(values['blob'])),
                  'commitment': list(hexes(values['commitment']))}
        return entries.verify('BlobProof', inputs, public, hexes(values['proof']))
    if function == 'verify_blob_kzg_proof_batch':
        commitments = hexes(values['commitments'])
        public = {'blobs': inputs.bytes('blobs', b''.join(blob(key) for key in values['blobs'])),
                  'commitments': inputs.bytes('commitments', b''.join(commitments)),
                  'count': str(len(commitments))}
        return entries.verify('BlobBatchProof', inputs, public, b''.join(hexes(values['proofs'])))
    raise AssertionError(function)


def test_corpora_are_the_pinned_upstream_selection():
    assert CORPUS['source']['revision'] == 'e125905e5e01186e6ccb7a0ced4845bf7eddbcfe'
    assert hashlib.sha256(SETUP.read_bytes()).hexdigest() == CORPUS['source']['trusted_setup_sha256']
    counts = {}
    for case in CORPUS['cases']:
        counts[case['function']] = counts.get(case['function'], 0) + 1
    assert counts == {'blob_to_kzg_commitment': 11, 'compute_kzg_proof': 52, 'compute_blob_kzg_proof': 15,
                      'compute_challenge': 9, 'verify_kzg_proof': 122, 'verify_blob_kzg_proof': 29,
                      'verify_blob_kzg_proof_batch': 24}
    for key, value in CORPUS['blobs'].items():
        assert hashlib.sha256(bytes.fromhex(value)).hexdigest() == key
    # Derived cases refer only to upstream blobs.
    for case in EXTRA['cases']:
        for key in [case['input'].get('blob'), *case['input'].get('blobs', [])]:
            assert key is None or key in CORPUS['blobs']


@pytest.mark.parametrize('function', ['compute_challenge', 'verify_kzg_proof', 'verify_blob_kzg_proof',
                                      'verify_blob_kzg_proof_batch', 'blob_to_kzg_commitment',
                                      'compute_kzg_proof', 'compute_blob_kzg_proof'])
def test_upstream_vectors(entries, journal, directory, function):
    for case in cases(function):
        actual = outcome(entries, directory, case)
        journal.check(case['name'], actual == hexes(case['output']), shown(actual))


@pytest.mark.parametrize('function', ['verify_kzg_proof', 'verify_blob_kzg_proof', 'verify_blob_kzg_proof_batch'])
def test_derived_cases_match_the_reference(entries, journal, directory, function):
    selected = cases(function, EXTRA)
    assert selected
    for case in selected:
        actual = outcome(entries, directory, case)
        journal.check(case['name'], actual == case['output'], shown(actual))


def challenge(blob_bytes, commitment):
    """compute_challenge over raw bytes, as specified."""
    data = b'FSBLOBVERIFY_V1_' + (4096).to_bytes(16, 'big') + blob_bytes + commitment
    return (int.from_bytes(hashlib.sha256(data).digest(), 'big') % R).to_bytes(32, 'big')


def test_challenge_entry_takes_typed_inputs(entries, journal, directory):
    """Lengths and the commitment point are checked as by the upstream bindings;
    blob scalars are hashed without being decoded."""
    for case in cases('compute_challenge'):
        values = case['input']
        assert challenge(blob(values['blob']), hexes(values['commitment'])) == hexes(case['output'])
    selected = [case for case in cases('verify_blob_kzg_proof')
                if '_invalid_blob_' in case['name'] or '_invalid_commitment_' in case['name']]
    assert len(selected) == 8
    for case in selected:
        blob_bytes, commitment = blob(case['input']['blob']), hexes(case['input']['commitment'])
        inputs = Inputs(directory, f'challenge-{case["name"]}')
        inputs.values = {'blob': inputs.bytes('blob', blob_bytes), 'commitment': list(commitment)}
        roles = entries.run('ComputeChallenge', inputs)
        actual = bytes(roles['challenge']) if roles else None
        typed = len(blob_bytes) == 131072 and '_invalid_commitment_' not in case['name']
        journal.check(case['name'], actual == (challenge(blob_bytes, commitment) if typed else None), shown(actual))


def versioned(commitment):
    return b'\x01' + hashlib.sha256(commitment).digest()[1:]


def test_point_evaluation_precompile(entries, journal, directory):
    """The 0x0A input form, built from the point vectors."""
    success = (4096).to_bytes(32, 'big') + R.to_bytes(32, 'big')
    for case in cases('verify_kzg_proof'):
        values = {key: hexes(value) for key, value in case['input'].items()}
        data = versioned(values['commitment']) + values['z'] + values['y'] + values['commitment'] + values['proof']
        inputs = Inputs(directory, case['name'])
        inputs.values = {'input': list(data)}
        roles = entries.run('PointEvaluationPrecompile', inputs)
        # A malformed width changes the 192-byte input length; only an
        # accepted opening returns output.
        expected = success if case['output'] is True else None
        journal.check(case['name'], (bytes(roles['output']) if roles else None) == expected, roles)
    values = {key: hexes(value)
              for key, value in named('verify_kzg_proof', 'verify_kzg_proof_case_correct_proof_2_0')['input'].items()}
    valid = versioned(values['commitment']) + values['z'] + values['y'] + values['commitment'] + values['proof']
    for name, data in [('version-byte', b'\x02' + valid[1:]),
                       ('hash-bit', valid[:31] + bytes([valid[31] ^ 1]) + valid[32:]),
                       ('short', valid[:-1]), ('long', valid + b'\x00')]:
        inputs = Inputs(directory, f'precompile-{name}')
        inputs.values = {'input': list(data)}
        journal.check(f'precompile-{name}', entries.run('PointEvaluationPrecompile', inputs) is None)


def test_setup_constants_and_admission(toolchain, journal, directory):
    from entry import Entry
    from source_modules import library_modules

    source = '''module sample;
use zkc::bytes::{Bytes};
use zkc::encoding as encoding;
use zkc::curve as curve;
use zkc::curve::{Groups};
use kzg::eip4844 as eip4844;
protocol Check roles(P)(setup: Groups<eip4844::G1> @P) -> (key: Bytes @P, count: index @P) {
  let admitted = eip4844::admit_setup(setup);
  return (key = encoding::group_compressed(eip4844::verifier_key()), count = curve::length(admitted));
}
run Demo = Check;
'''
    entry = Entry(toolchain, journal, directory, source, library_modules('kzg'))
    pinned = lagrange()

    def run(name, setup):
        (directory / f'{name}.zkcv').write_bytes(setup)
        reference = {'file': f'{name}.zkcv', 'sha256': hashlib.sha256(setup).hexdigest()}
        return entry.run(name, {'setup': reference}, refuses='entry-run-incomplete' if setup != pinned else None)

    # The embedded verifier key is the second G2 monomial point of the asset.
    assert run('pinned', pinned) == {'key': list(g2_monomial(1)), 'count': '4096'}
    # Exchanging two valid points, or omitting one, changes the pinned digest.
    first, second = pinned[10:58], pinned[58:106]
    run('swapped', pinned[:10] + second + first + pinned[106:])
    run('short', frame(67, pinned[10:-48], 4095))


def test_prover_refuses_an_unpinned_setup(entries, directory):
    case = named('compute_blob_kzg_proof', 'compute_blob_kzg_proof_case_valid_blob_2')
    inputs = Inputs(directory, 'unpinned')
    public = {'blob': inputs.bytes('blob', blob(case['input']['blob'])),
              'commitment': list(hexes(case['input']['commitment']))}
    pinned = lagrange()
    changed = pinned[:10] + pinned[58:106] + pinned[10:58] + pinned[106:]
    assert entries.prove('BlobProof', inputs, public, {'setup': inputs.file('changed.zkcv', changed)}) is None
    assert entries.prove('BlobProof', inputs, public, {'setup': inputs.setup()}) == hexes(case['output'])


def test_point_proof_prover_checks_its_statement(entries, journal, directory):
    case = named('verify_kzg_proof', 'verify_kzg_proof_case_correct_proof_2_0')
    statement = named('verify_blob_kzg_proof', 'verify_blob_kzg_proof_case_correct_proof_2')
    values = {key: hexes(value) for key, value in case['input'].items()}
    assert values['commitment'] == hexes(statement['input']['commitment'])
    own = blob(statement['input']['blob'])
    other = blob(named('verify_blob_kzg_proof', 'verify_blob_kzg_proof_case_correct_proof_3')['input']['blob'])
    shifted = ((int.from_bytes(values['y'], 'big') + 1) % R).to_bytes(32, 'big')
    for name, change, blob_bytes, expected in [('statement', {}, own, values['proof']),
                                               ('other-blob', {}, other, None),
                                               ('other-value', {'y': shifted}, own, None)]:
        inputs = Inputs(directory, f'point-{name}')
        public = {key: list(dict(values, **change)[key]) for key in ('commitment', 'z', 'y')}
        witness = {'blob': inputs.bytes('blob', blob_bytes), 'setup': inputs.setup()}
        proof = entries.prove('KzgProof', inputs, public, witness)
        journal.check(name, proof == expected, shown(proof))
        if proof is not None:
            journal.check(f'{name}-verifies', entries.verify('KzgProof', inputs, public, proof) is True)


def test_batch_bound_is_static(toolchain, journal, directory):
    from entry import Entry
    from source_modules import library_modules

    source = '''module sample;
use kzg::eip4844::{BlobBatch, Batch};
proof Demo = BlobBatch<3> {
  prover P;
  verifier V;
  public { blobs, commitments, count };
  accept accepted;
  construction Batch<3>;
}
'''
    entry = Entry(toolchain, journal, directory, source, library_modules('kzg'))
    case = named('verify_blob_kzg_proof_batch', 'verify_blob_kzg_proof_batch_case_4')
    blobs = [blob(key) for key in case['input']['blobs']]
    commitments = hexes(case['input']['commitments'])
    proofs = hexes(case['input']['proofs'])
    for count, expected in [(3, 'accepted'), (4, None)]:
        inputs = Inputs(directory, f'count-{count}')
        public = {'blobs': inputs.bytes('blobs', b''.join(blobs[:count])),
                  'commitments': inputs.bytes('commitments', b''.join(commitments[:count])),
                  'count': str(count)}
        (inputs.directory / 'proof.bin').write_bytes(b''.join(proofs[:count]))
        report = journal.json([toolchain.runtime, '--json', 'verify', f'--package={entry.package}',
                               f'--sha256={entry.pin}', f'--public={inputs.document("public", public)}',
                               f'--proof={inputs.directory / "proof.bin"}', '--allow-authored'],
                              refuses=None if expected else 'loop-count-bound')
        journal.check(f'count-{count}', report['status'] == (expected or 'refused'), report.get('code'))


def test_batch_count_must_match_the_statement(entries, journal, directory):
    case = named('verify_blob_kzg_proof_batch', 'verify_blob_kzg_proof_batch_case_4')
    blobs = b''.join(blob(key) for key in case['input']['blobs'])
    commitments = b''.join(hexes(case['input']['commitments']))
    for name, count, expected in [('equal', 4, True), ('above', 5, None), ('below', 3, None)]:
        inputs = Inputs(directory, f'count-{name}')
        public = {'blobs': inputs.bytes('blobs', blobs), 'commitments': inputs.bytes('commitments', commitments),
                  'count': str(count)}
        actual = entries.verify('BlobBatchProof', inputs, public, b''.join(hexes(case['input']['proofs'])))
        journal.check(name, actual is expected, actual)


def test_example_inputs_prove_and_verify(toolchain, journal, directory):
    output = directory / 'inputs'
    subprocess.run([sys.executable, ROOT / PROJECT / 'prepare.py', f'--output={output}'], check=True)
    project = f'--project={ROOT / PROJECT / "zkc.toml"}'
    common = [toolchain.runtime, '--json']
    for entry in ['BlobToCommitment', 'ComputeKzgProof', 'ComputeChallenge', 'PointEvaluationPrecompile']:
        report = journal.json([*common, 'run', f'example::{entry}', f'--compiler={toolchain.compiler}', project,
                               '--session=example', f'--input=P={output / f"example.{entry}/P.json"}',
                               f'--results={directory / f"{entry}.json"}'])
        assert report['status'] == 'executed', entry
    for entry in ['KzgProof', 'BlobProof', 'BlobBatchProof']:
        documents = output / f'example.{entry}'
        proof = directory / f'{entry}.proof'
        options = [f'--compiler={toolchain.compiler}', project, f'--public={documents / "public.json"}',
                   '--allow-authored']
        journal.run([*common, 'prove', f'example::{entry}', *options, f'--witness={documents / "witness.json"}',
                     f'--output={proof}'])
        assert journal.json([*common, 'verify', f'example::{entry}', *options,
                             f'--proof={proof}'])['status'] == 'accepted'
