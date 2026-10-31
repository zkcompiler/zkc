"""Independent physical FRI policy and publication controls; no native tools."""
from copy import deepcopy
import importlib
import json
from pathlib import Path
from types import SimpleNamespace
import sys

import pytest

ROOT = Path(__file__).resolve().parents[3]


@pytest.fixture
def modules(monkeypatch):
    monkeypatch.syspath_prepend(str(ROOT/'common/benchmarks'))
    return SimpleNamespace(**{name: importlib.import_module('bench.'+name)
        for name in ('oracle_policy', 'configuration', 'execution', 'programs', 'stark', 'results', 'io', 'runner')})


def expected_policy(profile, scheme):
    # Literal contract expectations, independent of the producer's registry.
    return {'format': 'zkc.benchmark-oracle-policy/0', 'profile': profile,
            'selection': {'format': 'zkc.oracle-selection/0',
                'roots': {'kind': 'uniform', 'table': {'scheme': scheme,
                    'grouping': 'individual', 'order': 'natural'}},
                'order': 'unrestricted', 'authentication': 'per-query'}}


def options(selection):
    return {'simplify': True, 'finite_bulk': True, 'release_storage': False,
            'fuse_vector_reductions': False, 'fuse_collect_fold': False,
            'calculation_batching': True, 'oracle_realization': deepcopy(selection)}


OCTIC = ('fri-keccak256-koala-bear-octic', 'rows.merkle-keccak256.koala-bear.ext8-binomial3/0')
LIBRARIES = [
    ('koala-bear', 'fri-poseidon2-16-koala-bear-quartic', 'rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0'),
    ('baby-bear', 'fri-poseidon2-16-baby-bear-quartic', 'rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0'),
    ('goldilocks', 'fri-poseidon2-8-goldilocks-quadratic', 'rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0'),
]


@pytest.mark.parametrize('family,field,profile,scheme', [
    ('fri', None, *OCTIC), ('air', None, *OCTIC), ('machine', None, *OCTIC),
    *(('stark', *row) for row in LIBRARIES),
])
def test_generated_workload_field_hash_and_layout(modules, tmp_path, family, field, profile, scheme):
    coverage = importlib.import_module('bench.coverage')
    case = next(c for c in coverage.cases() if c.name == family
                and (family != 'stark' or c.shape.get('field', 'koala-bear') == field))
    program = case.generate(ROOT, tmp_path/family)
    assert program.oracle_policy.record() == expected_policy(profile, scheme)
    assert json.loads(program.oracle_policy.flag().split('=', 1)[1]) == expected_policy(profile, scheme)['selection']
    assert '--oracle-realization' not in modules.configuration.flags(
        {k: default for k, (default, _) in modules.configuration.SETTINGS.items()})
    # Physical selection does not rewrite the logical field or outer configuration.
    if family == 'fri':
        assert 'Direct<E>' in program.source and 'field("koala-bear.ext8-binomial3")' in program.source
        assert program.invalid_witness_stop == ('fri', 'padded')
    elif family == 'stark':
        configuration = {'koala-bear': 'koala_bear_quartic', 'baby-bear': 'baby_bear_quartic',
                         'goldilocks': 'goldilocks_quadratic'}[field]
        assert f'configurations::{configuration}::{{Poseidon2}}' in program.source


def saved_manifest(policy, field='baby-bear'):
    return {'format': 'zkc.benchmark/0', 'status': 'failed', 'results': [], 'compiler_options': [],
            'ingress': 'json', 'observation': 'timing',
            'contracts': {'stark-fixture': {'protocol': 'stark', 'category': 'protocol',
                'dimensions': {'field': field}, 'oracle_realization': deepcopy(policy)}},
            'compilation': {'stark-fixture': [{'oracle_realization': deepcopy(policy),
                'published_options': options(policy['selection'])}]}}


@pytest.mark.parametrize('location', ['contract', 'compilation', 'package'])
@pytest.mark.parametrize('change', ['missing', 'scheme', 'grouping', 'order', 'authentication', 'unknown'])
def test_saved_publication_independently_checks_all_policy_copies(modules, location, change):
    policy = expected_policy(*LIBRARIES[1][1:])
    manifest = saved_manifest(policy)
    modules.results.validate_manifest(manifest)
    contract = manifest['contracts']['stark-fixture']
    compilation = manifest['compilation']['stark-fixture'][0]
    owner, key = ((contract, 'oracle_realization') if location == 'contract' else
                  (compilation, 'oracle_realization') if location == 'compilation' else
                  (compilation['published_options'], 'oracle_realization'))
    if change == 'missing':
        del owner[key]
    else:
        selection = owner[key] if location == 'package' else owner[key]['selection']
        if change == 'scheme': selection['roots']['table']['scheme'] = ''
        elif change == 'grouping': selection['roots']['table']['grouping'] = 'antipodal-pairs'
        elif change == 'order': selection['roots']['table']['order'] = 'bit-reversed'
        elif change == 'authentication': selection['authentication'] = 'atomic-blocks'
        else: selection['unexpected'] = True
    with pytest.raises(modules.io.MeasurementError):
        modules.results.validate_manifest(manifest)


def test_matching_wrong_field_copies_cannot_authorize_publication(modules):
    manifest = saved_manifest(expected_policy(*LIBRARIES[0][1:]))
    with pytest.raises(modules.io.MeasurementError, match='field/family'):
        modules.results.validate_manifest(manifest)


@pytest.mark.parametrize('field', [None, [], {}, True])
def test_malformed_saved_field_has_a_controlled_refusal(modules, field):
    manifest = saved_manifest(expected_policy(*LIBRARIES[1][1:]), field)
    with pytest.raises(modules.io.MeasurementError, match='unsupported STARK oracle field'):
        modules.results.validate_manifest(manifest)


@pytest.mark.parametrize('change', ['missing', 'unknown', 'boolean', 'clear'])
def test_published_options_have_one_exact_schema(modules, change):
    policy = modules.oracle_policy.OCTIC_KECCAK
    published = options(policy.selection())
    if change == 'missing': del published['oracle_realization']
    elif change == 'unknown': published['unexpected'] = False
    elif change == 'boolean': published['simplify'] = 1
    else: published['oracle_realization']['roots']['table']['scheme'] = ''
    with pytest.raises(modules.io.MeasurementError):
        modules.configuration.validate_published(published, None, policy)


def test_optimization_candidate_records_separate_semantic_request(modules):
    configuration = {'profile': 'default',
        'values': {k: default for k, (default, _) in modules.configuration.SETTINGS.items()},
        'origins': {k: 'default' for k in (*modules.configuration.SETTINGS, 'oracle-realization')},
        'oracle_realization': expected_policy('clear-table', '')['selection']}
    modules.configuration.validate_published(options(expected_policy(*OCTIC)['selection']),
                                            configuration, modules.oracle_policy.OCTIC_KECCAK)
    configuration['oracle_realization'] = expected_policy(*OCTIC)['selection']
    with pytest.raises(modules.io.MeasurementError, match='optimization profiles'):
        modules.configuration.validate_candidate(configuration)


@pytest.mark.parametrize('drift', [False, True])
def test_compiler_receipt_matches_independent_expected_policy(modules, tmp_path, drift):
    policy = expected_policy(*OCTIC)
    compiler = tmp_path/'compiler'
    published = options(expected_policy('clear-table', '')['selection'] if drift else policy['selection'])
    compiler.write_text(f'''#!{sys.executable}
import json,sys
from pathlib import Path
selection=json.loads(next(a.split('=',1)[1] for a in sys.argv if a.startswith('--oracle-realization=')))
assert selection == {policy['selection']!r}
Path(next(a.split('=',1)[1] for a in sys.argv if a.startswith('--observations='))).write_text('{{"completed":true}}')
print(json.dumps({{'options':{published!r}}}))
''')
    compiler.chmod(0o755)
    source = tmp_path/'source'; source.mkdir()
    args = SimpleNamespace(source=source, compiler=compiler, timeout=5, compiler_option=[])
    program = modules.programs.Program('module example;', [], dependencies=(), oracle_policy=modules.oracle_policy.OCTIC_KECCAK)
    manifest = {}
    def call():
        return modules.execution.compile_program(args, tmp_path/'out', modules.runner.Capture(tmp_path/'capture'),
                                                 manifest, SimpleNamespace(identifier='fri-control'), program)
    if drift:
        with pytest.raises(modules.io.MeasurementError, match='published oracle selection'):
            call()
        assert not manifest
    else:
        call()
        receipt = manifest['compilation']['fri-control'][0]
        assert receipt['oracle_realization'] == policy
        assert receipt['published_options'] == published


@pytest.mark.parametrize('change', ['none', 'role', 'kind', 'local', 'code', 'status', 'exit', 'proof'])
def test_degree_control_requires_exact_prover_padding_stop(modules, tmp_path, change):
    report = {'format': 'zkc.entry-result/0', 'phase': 'execution', 'status': 'refused', 'code': 'artifact-stopped:Explicit("reject")', 'execution': {'stop': {
        'role': 'role00000000', 'kind': 'Explicit("reject")', 'local': {'function': 'padding'}}}}
    stop = report['execution']['stop']
    if change == 'role': stop['role'] = 'role00000001'
    elif change == 'kind': stop['kind'] = 'Cancelled'
    elif change == 'local': stop['local']['function'] = 'some_other_guard'
    elif change == 'code': report['code'] = 'artifact-binding'
    elif change == 'status': report['status'] = 'produced'
    runtime = tmp_path/'runtime'
    runtime.write_text(f'''#!{sys.executable}
import json,sys
from pathlib import Path
if {change == 'proof'!r}:
 Path(next(a.split('=',1)[1] for a in sys.argv if a.startswith('--output='))).write_bytes(b'invalid')
print(json.dumps({report!r}))
raise SystemExit({0 if change == 'exit' else 1})
''')
    runtime.chmod(0o755)
    package = tmp_path/'entry.zkpkg'
    original = '"local.func"() <{sym_name = "padding"}>\n}) {runtime.origin = ["s3h6672696h706164646564", []]}'
    package.write_text(json.dumps({'original': original}))
    args = SimpleNamespace(runtime=runtime, timeout=5)
    program = SimpleNamespace(invalid_witness_stop=('fri', 'padded'), invalid_witness={'word': []})
    def call():
        return modules.execution.check_prover_stop(args, modules.runner.Capture(tmp_path/'capture'), tmp_path,
            {'package': str(package), 'sha256': 'a'*64}, {'public': str(tmp_path/'public.json')}, program)
    if change == 'none':
        assert call()['source_function'] == 'fri::padded'
    else:
        with pytest.raises(modules.io.MeasurementError):
            call()


@pytest.mark.parametrize('change', ['missing', 'bare-code', 'verifier', 'published-proof', 'unknown'])
def test_saved_fri_control_requires_the_documented_prover_outcome(modules, change):
    manifest = saved_manifest(expected_policy(*OCTIC))
    contract = manifest['contracts']['stark-fixture']
    contract.update(protocol='fri', dimensions={})
    control = {'stage': 'prover', 'code': 'artifact-stopped:Explicit("reject")',
               'role': 'role00000000', 'source_function': 'fri::padded',
               'proof_published': False}
    contract['semantic_control'] = control
    compilations = manifest['compilation']['stark-fixture']
    receipt = control | {'function': 'retained_padding_function', 'report': 'prover-stop.json'}
    modules.oracle_policy.validate_workload(contract, compilations, control_receipts=[receipt])
    if change == 'missing': del contract['semantic_control']
    elif change == 'bare-code': control['code'] = 'artifact-stopped'
    elif change == 'verifier': control['stage'] = 'verifier'
    elif change == 'published-proof': control['proof_published'] = True
    else: control['unknown'] = None
    with pytest.raises(modules.io.MeasurementError, match='prover padding'):
        modules.oracle_policy.validate_workload(contract, compilations, control_receipts=[receipt])


@pytest.mark.parametrize('change', ['profile', 'format', 'unknown', 'missing'])
def test_oracle_policy_has_no_alternate_schema(modules, change):
    record = expected_policy(*OCTIC)
    if change == 'profile': record['profile'] = 'unknown'
    elif change == 'format': record['format'] = 'zkc.benchmark-oracle-policy/1'
    elif change == 'unknown': record['other'] = False
    else: del record['selection']
    with pytest.raises(modules.io.MeasurementError):
        modules.oracle_policy.read_policy(record)


def test_source_contract_comparison_excludes_invocation_receipt_paths(modules, monkeypatch, tmp_path):
    program = modules.stark.fri(ROOT, {'evaluation_size': 8, 'degree_bound': 2, 'queries': 1})
    case = SimpleNamespace(identifier='fri-8', name='fri', category='protocol', shape={}, mix=(),
                           limitation='bounded', generate=lambda *a, **k: program)
    args = SimpleNamespace(source=ROOT, timeout=5, input_count=1, ingress='json', preparation='enabled',
                           preparation_entries=None, preparation_bytes=None)

    def compile_program(args, output, capture, manifest, case, program):
        directory = output/'case'; directory.mkdir(parents=True)
        package = directory/'entry.zkpkg'
        package.write_text(json.dumps({'interface': json.dumps({'job': {'construction': {'format': 'zkc.framed/0'}}})}))
        return directory, package

    def proof_jobs(args, capture, directory, name, base, files, program, proof_format, *, semantic_control):
        semantic_control.update({'stage': 'prover', 'code': 'artifact-stopped:Explicit("reject")',
            'role': 'role00000000', 'source_function': 'fri::padded', 'proof_published': False,
            'function': 'generated_'+directory.parent.name, 'report': str(directory/'stop.json')})
        return [SimpleNamespace(implementation='zkc', boundary='admitted_entry_call')], None

    monkeypatch.setattr(modules.execution, 'compile_program', compile_program)
    monkeypatch.setattr(modules.execution, 'proof_jobs', proof_jobs)
    manifests = []
    for name in ('baseline', 'current'):
        manifest = {'contracts': {}, 'checks': []}
        modules.execution.prepare_case(args, tmp_path/name, modules.runner.Capture(tmp_path/name/'capture'), manifest, case)
        manifests.append(manifest)
    assert manifests[0]['contracts'] == manifests[1]['contracts']
    assert manifests[0]['checks'][0]['semantic_control'] != manifests[1]['checks'][0]['semantic_control']
