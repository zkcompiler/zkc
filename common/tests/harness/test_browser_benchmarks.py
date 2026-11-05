"""Browser evidence refuses missing samples, changed pins and invented phases."""
import importlib
import json
from pathlib import Path
from copy import deepcopy

import pytest


@pytest.fixture
def browser(monkeypatch):
    monkeypatch.syspath_prepend(str(Path(__file__).resolve().parents[3]/'common/benchmarks'))
    return importlib.import_module('bench.browser')


def prepared(browser, tmp_path):
    fixture = tmp_path/'input'
    fixture.mkdir()
    from bench.oracle_policy import OraclePolicy
    from bench.configuration import SETTINGS
    options = {k.replace('-', '_'): v for k, (v, _) in SETTINGS.items()}
    options['oracle_realization'] = OraclePolicy().selection()
    (fixture/'entry.zkpkg').write_text(json.dumps({'artifact': '["fixture"]', 'options': options}))
    (fixture/'pin.txt').write_text(browser.digest(fixture/'entry.zkpkg'))
    (fixture/'public.json').write_text('{"x":"1"}')
    (fixture/'witness.json').write_text('{"secret":"2"}')
    path = tmp_path/'cases.json'
    path.write_text(json.dumps({'format': browser.CASE_FORMAT, 'cases': [
        {'name': 'example', 'directory': 'input', 'providers': ['plonky3'],
         'oracle_realization': OraclePolicy().record()}]}))
    return path, fixture


def observation(case):
    return {'format': 'zkc.browser-worker/0', 'status': 'passed', 'variants': ['portable'],
            'modules': [{'variant': 'portable', 'bytes': 8, 'fetch_ms': 1, 'compile_ms': 1,
                         'glue_initialize_ms': 2, 'instantiate_api_ms': 1}],
            'cases': [{'name': 'example', 'variant': 'portable', 'pin': case['pin'], 'providers': ['plonky3'],
                       'worker_ready_ms': 1, 'admit_roundtrip_ms': 1, 'checks': {'outputs_match': True},
                       'calls': [{'operation': op, 'input_index': 0, 'cycle': 0, 'phase': 'sample',
                                  'success': True, 'accepted': op == 'verify', 'outputs_sha256': 'a'*64,
                                  'end_to_end_ms': 3, 'worker_call_ms': 1, 'outside_worker_call_ms': 2}
                                 for op in ('prove', 'verify')]}]}


def test_capture_keeps_independent_pin_and_reusable_setup_bindings(browser, tmp_path):
    path, fixture = prepared(browser, tmp_path)
    (fixture/'pk.bin').write_bytes(b'opaque material')
    doc = json.loads(path.read_text())
    doc['cases'][0]['bindings'] = [{'name': 'pk', 'path': 'pk.bin'}]
    path.write_text(json.dumps(doc))
    capture = browser.Capture(tmp_path/'capture')
    cases = browser.prepare_cases(path, tmp_path/'out', capture)
    assert Path(cases[0]['bindings'][0]['path']).read_bytes() == b'opaque material'
    assert cases[0]['files']['entry.zkpkg']['gzip_bytes'] > 0
    capture.check()
    Path(cases[0]['package']).write_bytes(b'replaced')
    with pytest.raises(importlib.import_module('bench.io').MeasurementError, match='changed'):
        capture.check()


@pytest.mark.parametrize('change', ['pin', 'provider', 'name', 'unknown', 'statement', 'binding'])
def test_prepared_case_refusals(browser, tmp_path, change):
    path, fixture = prepared(browser, tmp_path)
    document = json.loads(path.read_text())
    case = document['cases'][0]
    if change == 'pin': (fixture/'pin.txt').write_text('0'*64)
    elif change == 'provider': case['providers'] = ['missing']
    elif change == 'name': case['name'] = '../escape'
    elif change == 'unknown': case['extra'] = True
    elif change == 'statement': case['statements'] = []
    elif change == 'binding': case['bindings'] = [{'name': '', 'path': 'public.json'}]
    path.write_text(json.dumps(document))
    with pytest.raises(importlib.import_module('bench.io').MeasurementError):
        browser.prepare_cases(path, tmp_path/'out', browser.Capture(tmp_path/'capture'))


@pytest.mark.parametrize('change', ['sample', 'variant', 'phase', 'input', 'acceptance', 'nan', 'inclusive', 'module', 'capture', 'invented'])
def test_observation_refuses_incomplete_or_mislabeled_evidence(browser, tmp_path, change):
    path, _ = prepared(browser, tmp_path)
    cases = browser.prepare_cases(path, tmp_path/'out', browser.Capture(tmp_path/'capture'))
    report = observation(cases[0])
    browser.validate_observation(report, cases, ['portable'], {'warmups': 0, 'samples': 1})
    row, call = report['cases'][0], report['cases'][0]['calls'][0]
    if change == 'sample': row['calls'].pop()
    elif change == 'variant': row['variant'] = 'simd'
    elif change == 'phase': call['phase'] = 'warmup'
    elif change == 'input': call['input_index'] = 1
    elif change == 'acceptance': row['calls'][1]['accepted'] = False
    elif change == 'nan': call['worker_call_ms'] = float('nan')
    elif change == 'inclusive': call['outside_worker_call_ms'] = 3
    elif change == 'module': report['modules'] = []
    elif change == 'capture': row['sdk_admission_ms'] = {'package_capture_ms': -1}
    elif change == 'invented': call['sdk_phases_ms'] = {'exact_transfer_ms': 1}
    with pytest.raises(importlib.import_module('bench.io').MeasurementError):
        browser.validate_observation(report, cases, ['portable'], {'warmups': 0, 'samples': 1})


def test_saved_browser_report_uses_shared_report_entry(browser, tmp_path):
    path, _ = prepared(browser, tmp_path)
    cases = browser.prepare_cases(path, tmp_path/'out', browser.Capture(tmp_path/'capture'))
    manifest = {'format': browser.FORMAT, 'observation': 'browser', 'status': 'passed', 'processes': 1,
                'plan': {'samples': 1, 'warmups': 0}, 'variants': ['portable'], 'cases': cases,
                'results': [{'repetition': 0, 'worker': observation(cases[0])}]}
    results = importlib.import_module('bench.results')
    directory = tmp_path/'report'
    directory.mkdir()
    results.publish(directory, manifest)
    saved = json.loads((directory/'summary.json').read_text())
    assert saved['rows'][0]['end_to_end_ms']['median'] == 3
    assert saved['rows'][0]['sdk_phases_ms']['output_encode_ms'] is None
    with pytest.raises(importlib.import_module('bench.io').MeasurementError, match='overlap'):
        results.compare(manifest, deepcopy(manifest))


def test_goldilocks_extension_oracle_and_distinct_fixture(browser):
    algebra = importlib.import_module('bench.algebra')
    fixtures = importlib.import_module('bench.browser_fixtures')
    f = algebra.FieldOracle('goldilocks.ext2-binomial7')
    assert f.mul((0, 1), (0, 1)) == (7, 0)
    assert f.mul((f.modulus-1, 1), (1, 1)) == (6, 0)
    program = fixtures.poseidon_distinct(3)
    states = program.inputs[0]['public']['states']
    assert len(states) == 48 and len({tuple(states[i:i+16]) for i in range(0, 48, 16)}) == 3
    assert program.proof is True


def test_quartic_keccak_fixture_uses_every_coordinate_and_derived_challenges(browser):
    fixtures = importlib.import_module('bench.browser_fixtures')
    program = fixtures.quartic_keccak()
    values = program.inputs[0]['witness']['values']
    public = program.inputs[0]['public']
    assert len(values) == int(public['width']) * int(public['height'])
    assert all(len(value) == 4 and all(int(c) > 0 for c in value) for value in values)
    assert public['expected'] == values[:int(public['width'])]
    assert program.proof and 'construction authored' not in program.source
    assert 'rows.merkle-keccak256.koala-bear.ext4-binomial3/0' in program.source
    assert 'hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0' in program.source


def test_quartic_keccak_fri_preserves_the_exact_consumer_and_independent_word(browser):
    from coset_reference import CosetReference
    fixtures = importlib.import_module('bench.browser_fixtures')
    root = Path(__file__).resolve().parents[3]
    program = fixtures.quartic_keccak_fri(root)
    source = root/'common/tests/evm/fixtures/fri_keccak.zkc'
    assert program.source == source.read_text()
    assert 'ScalarLowDegree<Direct<F>,5,0,3,8>' in program.source
    assert 'hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0' in program.source
    assert 'ext8' not in program.source
    assert program.entry == 'fri_keccak::Proof' and program.proof
    assert program.dependencies == ('protocols.polynomial.fri',)
    assert source in program.support
    inputs = program.inputs[0]
    assert inputs['public'] == {'shift': ['3', '1', '0', '0'], 'round_count': '3', 'query_count': '8'}
    word = [tuple(map(int, value)) for value in inputs['witness']['word']]
    assert len(word) == 32 and all(len(value) == 4 for value in word)
    reference = CosetReference('koala-bear.ext4-binomial3')
    domain = reference.domain((3, 1, 0, 0), 32)
    coefficients = [(i+1, i*i, 2*i, 1) for i in range(8)]
    # Interpolate a degree-seven prefix at held-out points, rather than merely
    # repeating the generator's Horner calculation on the same rows.
    for i in (8, 17, 31):
        assert word[i] == reference.lagrange(word[:8], domain[:8], domain[i])
        assert word[i] == reference.horner(coefficients, domain[i])


def test_quartic_keccak_fri_is_explicit_and_does_not_expand_defaults(browser, tmp_path):
    from types import SimpleNamespace
    fixtures = importlib.import_module('bench.browser_fixtures')
    root = Path(__file__).resolve().parents[3]
    assert 'quartic-keccak-fri' not in {name for name, _, _ in fixtures.catalog(root)}
    args = SimpleNamespace(source=root, output=tmp_path/'fixtures', compiler=None,
                           source_only=True, setup_material=None, case=['quartic-keccak-fri'])
    assert fixtures.prepare(args) == 0
    cases = json.loads((args.output/'cases.json').read_text())['cases']
    assert [case['name'] for case in cases] == ['quartic-keccak-fri']
    assert cases[0]['providers'] == ['plonky3']
    assert cases[0]['options'] == {'allow_authored': False}
    assert cases[0]['oracle_realization'] == fixtures.quartic_keccak_fri(root).oracle_policy.record()
    directory = Path(cases[0]['directory'])
    assert json.loads((directory/'options.json').read_text()) == {'allow_authored': False, 'providers': ['plonky3']}
    assert (directory/'main.zkc').read_bytes() == (root/'common/tests/evm/fixtures/fri_keccak.zkc').read_bytes()
    assert json.loads((directory/'witness.json').read_text()) == fixtures.quartic_keccak_fri(root).inputs[0]['witness']
    assert not (directory/'entry.zkpkg').exists()


def test_proof_identity_capture_keeps_process_wall_time(browser, tmp_path, monkeypatch):
    path, _ = prepared(browser, tmp_path)
    web = tmp_path/'web'
    (web/'pkg').mkdir(parents=True)
    for filename in ('zkc_web.js', 'zkc_web_bg.wasm'):
        (web/'pkg'/filename).write_bytes(b'test module')
    node = tmp_path/'node'
    node.write_bytes(b'explicit node identity')
    playwright = tmp_path/'playwright/index.mjs'
    playwright.parent.mkdir()
    playwright.write_bytes(b'explicit driver identity')
    (playwright.parent/'package.json').write_text('{"version":"1.64.1"}')
    output = tmp_path/'result'
    def command(self, argv, *, cwd):
        request = json.loads(Path(argv[-2]).read_text())
        value = observation(request['cases'][0])
        value['transport'] = 'borrowed'
        proof = output/'proofs/0/example/portable/0/browser.proof'
        proof.parent.mkdir(parents=True)
        proof.write_bytes(b'proof')
        value['proofs'] = [{'path': str(proof), 'sha256': browser.digest(proof), 'bytes': 5}]
        stdout = self.directory/'response.json'
        stdout.write_text(json.dumps(value))
        return {'stdout': str(stdout), 'stderr': str(self.directory/'response.stderr'), 'wall_seconds': 1.25}
    monkeypatch.setattr(browser.Journal, 'command', command)
    from types import SimpleNamespace
    args = SimpleNamespace(output=output, exclusive=False, processes=1, samples=1, warmups=0,
        label='test', revision='supplied-revision', transport='borrowed', native_example=None,
        variant=None, web=web, cases=path, node=node, playwright=playwright, timeout=30)
    assert browser.run(args) == 0
    result = json.loads((output/'manifest.json').read_text())
    assert result['results'][0]['process_wall_seconds'] == 1.25
    assert result['status'] == 'passed'


@pytest.mark.parametrize('location', ['candidate', 'package', 'saved'])
def test_browser_fri_policy_cannot_silently_default_to_clear(browser, tmp_path, location):
    from bench.oracle_policy import OCTIC_KECCAK, OraclePolicy
    path, fixture = prepared(browser, tmp_path)
    document = json.loads(path.read_text())
    candidate = document['cases'][0]
    candidate['name'] = 'fri-8'
    candidate['oracle_realization'] = OCTIC_KECCAK.record()
    package = json.loads((fixture/'entry.zkpkg').read_text())
    package['options']['oracle_realization'] = OCTIC_KECCAK.selection()
    if location == 'candidate':
        candidate['oracle_realization'] = OraclePolicy().record()
    elif location == 'package':
        package['options']['oracle_realization'] = OraclePolicy().selection()
    (fixture/'entry.zkpkg').write_text(json.dumps(package))
    (fixture/'pin.txt').write_text(browser.digest(fixture/'entry.zkpkg'))
    path.write_text(json.dumps(document))
    if location == 'saved':
        cases = browser.prepare_cases(path, tmp_path/'out', browser.Capture(tmp_path/'capture'))
        assert cases[0]['oracle_realization'] == OCTIC_KECCAK.record()
        cases[0]['published_options']['oracle_realization'] = OraclePolicy().selection()
        manifest = {'format': browser.FORMAT, 'observation': 'browser', 'status': 'failed',
                    'results': [], 'cases': cases}
        with pytest.raises(__import__('bench.io', fromlist=['MeasurementError']).MeasurementError, match='published oracle selection'):
            browser.validate_manifest(manifest)
    else:
        with pytest.raises(__import__('bench.io', fromlist=['MeasurementError']).MeasurementError, match='oracle'):
            browser.prepare_cases(path, tmp_path/'out', browser.Capture(tmp_path/'capture'))
