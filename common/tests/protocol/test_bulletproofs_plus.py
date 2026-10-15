"""Ordinary source BP+ against proofs from the pinned independent Monero prover."""
import json
import hashlib

import pytest

from test_source_projects import ROOT, build, read

def build_project(toolchain, journal, directory, project):
    package = directory / "Proof.zkpkg"
    report = journal.json([toolchain.runtime, "--json", "compile", f"--compiler={toolchain.compiler}",
                           f"--project={project}/zkc.toml", "example::Proof", f"--output={package}"])
    return package, report["package_sha256"]


FIXTURES = ROOT / 'common/tests/fixtures/bulletproofs-plus'
CASES = json.loads((FIXTURES / 'corpus.json').read_text())['cases']
assert len(CASES[0]['values']) == 1  # Mutation offsets below use six folding rounds.
EXTERNAL = ROOT / 'crates/zkc-test-support/fixtures/external-transcript'
PROJECT = 'examples/projects/bulletproofs-plus'


def verify(toolchain, journal, package, pin, proof, commitments, rounds, *, refuses=None):
    name = f'{proof.stem}-{hashlib.sha256(commitments).hexdigest()[:12]}-{rounds}.public.json'
    public = journal.write(name, {'commitments': list(commitments), 'rounds': str(rounds)})
    return journal.json([toolchain.runtime, '--json', 'verify', f'--package={package}',
                         f'--sha256={pin}', f'--proof={proof}', f'--public={public}',
                         '--allow-authored'], refuses=refuses)


@pytest.mark.parametrize('count', range(1, 17))
def test_exact_upstream_bytes_at_every_aggregation_size(toolchain, journal, directory, count):
    package, pin = build(toolchain, journal, directory, PROJECT, 'Proof', [])
    deployment = directory / 'deployment.json'
    deployment.write_text(json.loads(package.read_text())['artifact'])
    for case in (c for c in CASES if len(c['values']) == count):
        path = journal.write(f'{case["name"]}.json', case)
        proof = directory / f'{case["name"]}.proof'
        produced = journal.json([toolchain.driver('bulletproofs_plus'), deployment, path, proof])
        expected = bytes.fromhex(case['proof'])
        assert produced['bytes'] == len(expected)
        assert proof.read_bytes() == expected, case['name']
        assert verify(toolchain, journal, package, pin, proof,
                      bytes.fromhex(case['commitments']), 6+(count-1).bit_length())['status'] == 'accepted'


@pytest.mark.parametrize('name', ['ordinary-monero-1', 'ordinary-monero-2', 'ordinary-monero-3',
    'ordinary-monero-4', 'ordinary-monero-8', 'ordinary-monero-9', 'ordinary-monero-16',
    'instrumented-monero-consistent-torsion'])
def test_independent_random_coins_and_torsion_before_hash(toolchain, journal, directory, name):
    package, pin = build(toolchain, journal, directory, PROJECT, 'Proof', [])
    transcript = json.loads((EXTERNAL / f'{name}.transcript.json').read_text())
    commitments = bytes.fromhex(''.join(transcript['V']))
    assert verify(toolchain, journal, package, pin, EXTERNAL / f'{name}.proof',
                  commitments, len(transcript['x']))['status'] == 'accepted'


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage'], ['--no-finite-bulk']])
def test_example_uses_managed_randomness_and_checks_witness(toolchain, journal, directory, flags):
    package, pin = build(toolchain, journal, directory, PROJECT, 'Proof', flags)
    public, witness = read(PROJECT, 'public'), read(PROJECT, 'witness')
    public_path = journal.write('public.json', public)
    witness_path = journal.write('witness.json', witness)
    proof = directory / 'proof.bin'
    args = [f'--package={package}', f'--sha256={pin}', f'--public={public_path}', '--allow-authored']
    journal.run([toolchain.runtime, '--json', 'prove', *args, f'--witness={witness_path}', f'--output={proof}'])
    assert journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])['status'] == 'accepted'
    witness['values'][0] = '2'
    witness_path = journal.write('wrong-witness.json', witness)
    journal.run([toolchain.runtime, '--json', 'prove', *args, f'--witness={witness_path}',
                 f'--output={directory / "wrong.proof"}'], refuses='artifact-stopped')


@pytest.mark.parametrize('change', ['trailing', 'truncated', 'left-length', 'right-length',
    'nonminimal-varint', 'scalar-order', 'scalar-bit', 'negative-zero', 'noncanonical-point',
    'off-curve', 'torsion-after-hash', 'commitment-bit', 'no-commitments', 'too-many', 'wrong-rounds'])
def test_malformed_or_unbound_proofs_refuse(toolchain, journal, directory, change):
    package, pin = build(toolchain, journal, directory, PROJECT, 'Proof', [])
    case = CASES[0]
    proof, commitments, rounds = bytearray.fromhex(case['proof']), bytes.fromhex(case['commitments']), 6
    refusal = 'artifact-stopped'
    if change == 'trailing':
        proof += b'\x00'
    elif change == 'truncated':
        proof = proof[:-1]
        refusal = 'bytes-bounds'
    elif change == 'left-length':
        proof[192] = 5
    elif change == 'right-length':
        proof[193+32*rounds] = 5
    elif change == 'nonminimal-varint':
        proof[192:193] = b'\x86\x00'
    elif change == 'scalar-order':
        proof[96:128] = (2**252+27742317777372353535851937790883648493).to_bytes(32, 'little')
    elif change == 'scalar-bit':
        proof[96] ^= 1
        refusal = 'artifact-rejected'
    elif change == 'negative-zero':
        proof[:32] = b'\x01'+b'\x00'*30+b'\x80'
    elif change == 'noncanonical-point':
        proof[:32] = (2**255-19).to_bytes(32, 'little')
    elif change == 'off-curve':
        proof[:32] = b'\x02'+b'\x00'*31
    elif change == 'torsion-after-hash':
        # Add the order-two point: (x,y) -> (-x,-y). Equation points after
        # cofactor clearing are unchanged, but the observed bytes must change.
        encoded = int.from_bytes(proof[:32], 'little')
        y = encoded & (2**255-1)
        proof[:32] = (((2**255-19-y) % (2**255-19)) | ((1-(encoded>>255))<<255)).to_bytes(32,'little')
        refusal = 'artifact-rejected'
    elif change == 'commitment-bit':
        # A different valid commitment, so rejection must come from binding.
        commitments = bytes.fromhex(CASES[1]['commitments'])
        refusal = 'artifact-rejected'
    elif change == 'no-commitments':
        commitments = b''
    elif change == 'too-many':
        commitments *= 17
    elif change == 'wrong-rounds':
        rounds = 7
    path = directory / 'changed.proof'
    path.write_bytes(proof)
    verify(toolchain, journal, package, pin, path, commitments, rounds, refuses=refusal)


@pytest.mark.parametrize('query,draws', [('y', 1), ('z', 1), ('argument.fold_challenge', 3),
                                        ('argument.terminal_challenge', 17)])
def test_zero_challenges_stop_without_publishing_partial_proofs(toolchain, journal, directory, query, draws):
    # Deliberately replace one construction query. This exercises the refusal
    # without requiring an infeasible zero preimage of the real Keccak chain.
    import shutil
    family = directory / 'bulletproofs'
    shutil.copytree(ROOT / 'libraries/bulletproofs', family)
    manifest = family / 'zkc.toml'
    manifest.write_text(manifest.read_text().replace('"../zkc"', f'"{ROOT}/libraries/zkc"'))
    source = family / 'monero.zkc'
    before = f'on query {query}(t) {{ return transcript::Provider::draw(t); }}'
    after = f'on query {query}(t) {{ let (next, value) = transcript::Provider::draw(t); return (next, value - value); }}'
    assert before in source.read_text()
    source.write_text(source.read_text().replace(before, after))
    (directory / 'main.zkc').write_text((ROOT / PROJECT / 'main.zkc').read_text())
    (directory / 'zkc.toml').write_text('format = "zkc.project/0"\n[modules]\nexample = "main.zkc"\n'
                                       '[dependencies]\nbulletproofs = "bulletproofs"\n')
    package, pin = build_project(toolchain, journal, directory, directory)
    case = CASES[0]
    public = {'commitments': list(bytes.fromhex(case['commitments'])), 'rounds': '6'}
    public_path = journal.write('public.json', public)
    witness_path = journal.write('witness.json', {'values': ['0'], 'masks': case['masks']})
    proof = directory / 'partial.proof'
    args = [f'--package={package}', f'--sha256={pin}', f'--public={public_path}', '--allow-authored']
    report = journal.json([toolchain.runtime, '--json', 'prove', *args, f'--witness={witness_path}',
                           f'--output={proof}'], refuses='artifact-stopped')
    assert not proof.exists()
    assert report['execution']['cleanup_errors'] == []
    assert report['execution']['resources'][0]['state']['transitions'] == draws
    assert report['execution']['stop']['local']['site']
    proof.write_bytes(bytes.fromhex(case['proof']))
    report = journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'],
                           refuses='artifact-stopped')
    assert report['execution']['stop']['local']['site']


def test_prover_preserves_torsion_bearing_statement_bytes(toolchain, journal, directory):
    package, pin = build(toolchain, journal, directory, PROJECT, 'Proof', [])
    case = CASES[0]
    raw = int.from_bytes(bytes.fromhex(case['commitments']), 'little')
    changed = (((2**255-19-(raw & (2**255-1))) % (2**255-19)) | ((1-(raw>>255))<<255)).to_bytes(32,'little')
    public = journal.write('public.json', {'commitments': list(changed), 'rounds': '6'})
    witness = journal.write('witness.json', {'values': ['0'], 'masks': case['masks']})
    proof = directory / 'torsion.proof'
    journal.run([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}',
                 f'--public={public}', f'--witness={witness}', f'--output={proof}', '--allow-authored'])
    assert verify(toolchain, journal, package, pin, proof, changed, 6)['status'] == 'accepted'
    verify(toolchain, journal, package, pin, proof, bytes.fromhex(case['commitments']), 6,
           refuses='artifact-rejected')


@pytest.mark.parametrize('size,rounds,right,witness,y,valid', [
    (1,0,1,1,3,True), (4,2,4,4,3,True),
    (3,1,3,3,3,False), (4,1,4,4,3,False),
    (4,2,3,4,3,False), (4,2,4,3,3,False), (4,2,4,4,0,False),
])
def test_generic_argument_validates_dimensions_and_runs_on_bls(toolchain, journal, directory,
                                                             size, rounds, right, witness, y, valid):
    package, pin = build(toolchain, journal, directory, 'common/tests/fixtures/projects/weighted-inner-product', 'Proof', [])
    public = journal.write('public.json', {'count': str(size), 'rounds': str(rounds),
                                         'right_count': str(right), 'y': str(y)})
    private = journal.write('witness.json', {'witness_count': str(witness)})
    proof = directory / 'argument.proof'
    args = [f'--package={package}', f'--sha256={pin}', f'--public={public}']
    journal.run([toolchain.runtime, '--json', 'prove', *args, f'--witness={private}', f'--output={proof}'],
                refuses=None if valid else 'artifact-stopped')
    if valid:
        assert journal.json([toolchain.runtime, '--json', 'verify', *args, f'--proof={proof}'])['status'] == 'accepted'
    else:
        assert not proof.exists()


@pytest.mark.parametrize('zeros', [1, 3, 32])
def test_nonzero_blinding_consumes_rejected_candidates(toolchain, journal, directory, zeros):
    package, _ = build(toolchain, journal, directory, PROJECT, 'Proof', [])
    deployment = directory / 'deployment.json'
    deployment.write_text(json.loads(package.read_text())['artifact'])
    case = dict(CASES[0])
    case['coins'] = ['0'] * zeros + (case['coins'] if zeros < 32 else [])
    path = journal.write('coins.json', case)
    proof = directory / 'proof.bin'
    report = journal.attempt([toolchain.driver('bulletproofs_plus'), deployment, path, proof])
    diagnostics = json.loads(report.stderr)
    assert diagnostics['cleanup_errors'] == []
    assert diagnostics['resources'][0]['state']['transitions'] == len(case['coins'])
    if zeros < 32:
        assert report.returncode == 0, report.stdout
        assert proof.read_bytes() == bytes.fromhex(case['proof'])
    else:
        assert report.returncode == 1
        assert json.loads(report.stdout)['status'] == 'refused'
        assert diagnostics['stop']['kind'] == 'Explicit("reject")'
        assert not proof.exists()


@pytest.mark.parametrize('group,field', [
    ('bls12-381.g1', 'bls12-381.fr'),
    ('ristretto255.group', 'ristretto255.scalar'),
    ('edwards25519.prime', 'ristretto255.scalar'),
])
def test_coefficient_bases_match_dense_folds(toolchain, journal, directory, group, field):
    from entry import Entry
    from source_modules import library_modules

    source = '''module sample;
use bulletproofs::inner_product as ip;
use zkc::vector as vec;
use zkc::curve as curve;
use zkc::scalar as scalar;
use zkc::finite_domain::{range};
domain G = group("GROUP");
domain F = field("FIELD");
fn compare(challenges:vec::Vector<F>,y:F,n:index) {
  let g=curve::generator<G>();
  // Related points and identities exercise algebra only, not generator security.
  let left=curve::collect(range(0,n),fn(i)=>g*scalar::from_index<F>(i*i));
  let right=curve::collect(range(0,n),fn(i)=>g*(0-scalar::from_index<F>(i+7)));
  let original=ip::Bases<G>{left:left,right:right};
  let mut dense=original;
  let mut weights=(vec::fill<F>(1,1),vec::fill<F>(1,1));
  for i in 0..vec::length(challenges) {
    let x=vec::get(challenges,i);
    let inverse=scalar::inverse(x);
    dense=ip::fold_bases(dense,y,x);
    weights=(ip::fold_coefficients(weights.0,inverse,x),
      ip::fold_coefficients(weights.1,x,inverse));
  }
  let evaluated=ip::evaluate_bases(original,y,weights);
  return (curve::get(dense.left,0)==curve::get(evaluated.left,0)
    && curve::get(dense.right,0)==curve::get(evaluated.right,0),weights.0,weights.1);
}
protocol Check roles(P)(challenges:vec::Vector<F>@P,y:F@P,n:index@P)
 ->(result:(bool,vec::Vector<F>,vec::Vector<F>)@P) {
  return compare(challenges,y,n);
}
run Demo=Check;
'''.replace('GROUP', group).replace('FIELD', field)
    entry = Entry(toolchain, journal, directory, source,
                  library_modules('bulletproofs'))
    order = (2**252 + 27742317777372353535851937790883648493 if field.startswith('ristretto')
             else 52435875175126190479447740508185965837690552500527637822603658699938581184513)
    for rounds in range(5):
        challenges = [2, 3, 5, 7][:rounds]
        low, high = [1], [1]
        for x in challenges:
            inverse = pow(x, -1, order)
            low = [v * factor % order for v in low for factor in (inverse, x)]
            high = [v * factor % order for v in high for factor in (x, inverse)]
        for y in (1, 3, order-1):
            assert entry.run(f'rounds-{rounds}-y-{y}', {
                'challenges': list(map(str, challenges)), 'y': str(y), 'n': str(2**rounds),
            }) == {'result': [True, list(map(str, low)), list(map(str, high))]}
