"""Optional table admission through native relations and the complete argument.

Absent configuration keeps its own authority and logical height. Polynomial
profile limits apply to present tables. These are ordinary semantic controls,
not a soundness claim about the argument.
"""

from copy import deepcopy
import json

import pytest

from input_files import input_files
from test_machine_stark import (EXAMPLE, FIXTURES, assert_refused,
                               compile_entry, prepare, prove_and_verify)
from test_relation_bundle_conformance import rebind


def optional_memory(authority, *, height=64, present=False, power_of_two=True):
    """Retain the external machine relation, changing only memory's policy.

    Instance-height memory uses public schedule columns: native Bundle formation
    correctly forbids configuration columns with instance height authority.
    """
    document = json.loads((FIXTURES / 'arithmetic-only/run.json').read_text())
    program, initial = prepare.machine.read_run(document)
    rows = prepare.machine.layout(prepare.machine.execute(program, initial),
                                  memory_clocks=32, memory_present=present)
    bundle, _ = prepare.machine.machine_bundle()
    configuration, instance, witness = prepare.machine.carriers(bundle, rows)
    table = bundle[3][2]
    if authority == 'fixed':
        table[2] = ['fixed', height]
        configuration[2][2][0] = None
    else:
        table[2] = [authority, 1, 64, power_of_two]
    schedule = configuration[2][2][1][0][:height * 2]
    configuration[2][2][1][0] = schedule
    if authority == 'config':
        configuration[2][2][0] = height
    elif authority == 'instance':
        table[4][0][1] = 'public'
        configuration[2][2] = [None, []]
        if present:
            instance[3][2] = ['present', height, [schedule]]
    if present:
        witness[2][2][0] = witness[2][2][0][:height * 5]
    return rebind([bundle, configuration, instance, witness])


def native_results(toolchain, journal, cases):
    wire = ''.join(json.dumps(candidate, separators=(',', ':')) + '\n'
                   for candidate in cases)
    reports = []
    for executable in [toolchain.tool('compiler', 'test/zkc-relation_bundle_conformance-test'),
                       toolchain.driver('relation_bundle_conformance')]:
        reports.append([json.loads(line) for line in journal.run(
            [executable], stdin=wire, keep=executable.name).splitlines()])
    assert len(reports[0]) == len(reports[1]) == len(cases)
    assert reports[0] == reports[1]
    return reports[0]


@pytest.mark.parametrize('authority', ['fixed', 'config', 'instance'])
def test_native_absent_table_admits_configuration_without_rows(toolchain, journal, authority):
    heights = [1, 3, 8, 64]
    cases = [optional_memory(authority, height=height, power_of_two=False)
             for height in heights]
    reports = native_results(toolchain, journal, cases)
    for report in reports:
        assert report['accepted'] and report['result']['satisfied'], report
        assert all(row[0] != 2 for row in report['result']['residuals'])
        # CPU memory records have zero multiplicity in this execution; the
        # absent memory table contributes no push or pull multiplicities.
        assert all(balance[4:6] == [0, 0] for balance in report['result']['balances']
                   if balance[1] == 1)
    assert all(report['result'] == reports[0]['result'] for report in reports)


def test_native_absent_table_preserves_authority_and_policy(toolchain, journal):
    cases = []

    def changed(name, authority, expected, change):
        candidate = optional_memory(authority)
        change(candidate)
        cases.append((name, rebind(candidate), expected))

    changed('required presence', 'config', 'bundle-table-missing',
            lambda c: c[0][3][2].__setitem__(1, 'required'))
    changed('configured power of two', 'config', 'bundle-height',
            lambda c: c[1][2][2].__setitem__(0, 3))
    changed('configured range', 'config', 'bundle-height',
            lambda c: c[1][2][2].__setitem__(0, 128))
    changed('configured zero', 'config', 'bundle-height',
            lambda c: c[1][2][2].__setitem__(0, 0))
    changed('fixed authority', 'fixed', 'bundle-height-authority',
            lambda c: c[1][2][2].__setitem__(0, 64))
    changed('instance authority', 'instance', 'bundle-height-authority',
            lambda c: c[1][2][2].__setitem__(0, 64))
    changed('configured columns', 'config', 'bundle-group-shape',
            lambda c: c[1][2][2][1][0].pop())
    changed('fixed columns', 'fixed', 'bundle-group-shape',
            lambda c: c[1][2][2][1][0].pop())
    changed('absent witness', 'config', 'bundle-witness-presence',
            lambda c: c[3][2].__setitem__(2, [['0'] * 320]))
    reports = native_results(toolchain, journal, [candidate for _, candidate, _ in cases])
    for (name, _, expected), report in zip(cases, reports, strict=True):
        assert not report['accepted'] and report['error'] == expected, (name, report)


@pytest.mark.parametrize('authority', ['fixed', 'config', 'instance'])
def test_native_present_table_can_exceed_protocol_height_bound(toolchain, journal, authority):
    # These rows satisfy the same relation at height 64. Rejection by a profile
    # with H=32 below is specifically the protocol's active-table obligation.
    (report,) = native_results(toolchain, journal, [optional_memory(authority, present=True)])
    assert report['accepted'] and report['result']['satisfied'], report
    assert any(row[0] == 2 for row in report['result']['residuals'])


def source_and_inputs(candidate, authority):
    source = (EXAMPLE / 'main.zkc').read_text()
    public, witness = prepare.inputs(*candidate) if authority != 'fixed' else ({}, {})
    if authority == 'fixed':
        # A fixed height has no relation formal, while the protocol's explicit
        # TableStatement still carries that logical height for admission.
        source = source.replace('parameter memory_height: index,\n', '')
        source = source.replace('in.memory_height@V, in.schedule@V, in.cells)',
                                'in.schedule@V, in.cells)')
        configured = deepcopy(candidate)
        configured[0][3][2][2] = ['config', 1, 64, False]
        configured[1][2][2][0] = candidate[0][3][2][2][1]
        public, witness = prepare.inputs(*rebind(configured))
    elif authority == 'instance':
        source = source.replace('parameter memory_height:', 'statement memory_height:')
        source = source.replace('parameter schedule:', 'statement schedule:')
        source = source.replace('table(memory_present, memory_height, schedule)',
                                'TableStatement { present: memory_present, height: memory_height, '
                                'configuration: none(), public_columns: schedule }')
    return source, (public, witness)


ADMISSION = '''
protocol InspectAdmission<R: Reduction<Extension>> roles(P)
    (initial: Base @P, final: Base @P, cpu_height: index @P, program_height: index @P,
     instructions: Vector<Base> @P, memory_present: bool @P, memory_height: index @P,
     schedule: Vector<Base> @P, shift: Base @P)
    -> (present: bool @P, height: index @P, logical_height: index @P,
        witness_width: index @P, configuration_width: index @P, public_width: index @P,
        inputs: index @P, assertions: index @P, records: index @P, auxiliary: index @P,
        claims: index @P, chunks: index @P, scopes: index @P) {
  let supplied @P = statement(initial, final, cpu_height, program_height, instructions,
    memory_present, memory_height, schedule, shift);
  let layouts @P = stark::whole_bundle::admit<Machine,R,5,6>(supplied);
  let memory_layout @P = layouts[2];
  let present @P = memory_layout.present;
  let height @P = memory_layout.height;
  let logical_height @P = supplied.tables[2].height;
  let witness_width @P = memory_layout.facts.witness;
  let configuration_width @P = memory_layout.facts.configuration;
  let public_width @P = memory_layout.facts.public_columns;
  let inputs @P = memory_layout.facts.inputs;
  let assertions @P = memory_layout.facts.assertions;
  let records @P = memory_layout.records.count;
  let auxiliary @P = memory_layout.reduction.columns;
  let claims @P = memory_layout.reduction.claims;
  let chunks @P = memory_layout.chunks;
  let scopes @P = zkc::indices::length(memory_layout.begin);
  return (present = present, height = height, logical_height = logical_height,
    witness_width = witness_width, configuration_width = configuration_width,
    public_width = public_width, inputs = inputs, assertions = assertions,
    records = records, auxiliary = auxiliary, claims = claims, chunks = chunks, scopes = scopes);
}
run AdmissionLogUp = InspectAdmission<LogUp<Extension>>;
run AdmissionProduct = InspectAdmission<GrandProduct<Extension>>;
'''


@pytest.mark.parametrize('entry', ['AdmissionLogUp', 'AdmissionProduct'])
@pytest.mark.parametrize('authority', ['fixed', 'config', 'instance'])
def test_absent_layout_retains_configuration_but_has_no_contributions(
        toolchain, journal, directory, authority, entry):
    candidate = optional_memory(authority)
    source, (public, _) = source_and_inputs(candidate, authority)
    asset = journal.write('bundle.json', candidate[0])
    package, pin = compile_entry(toolchain, journal, directory, entry,
                                source=source + ADMISSION, asset=asset)
    settings = {k: v for k, v in public.items()
                if k not in ('round_count', 'query_count', 'attempt_count', 'channel_count')}
    supplied = input_files(journal, 'admission', roles={'P': {'inputs': settings}})
    output = directory / 'admission.json'
    report = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                           f'--sha256={pin}', *supplied, f'--results={output}'])
    assert report['status'] == 'executed'
    result = json.loads(output.read_text())['roles']['P']
    expected = dict.fromkeys(('height', 'witness_width', 'configuration_width', 'public_width',
                              'inputs', 'assertions', 'records', 'auxiliary', 'claims',
                              'chunks', 'scopes'), '0')
    expected |= {'present': False, 'logical_height': '0' if authority == 'instance' else '64'}
    assert result == expected


@pytest.mark.parametrize('authority,entry,flags', [
    (authority, entry, ()) for authority in ['fixed', 'config', 'instance']
    for entry in ['ProofLogUp', 'ProofProduct']
] + [('config', 'ProofLogUp', ('--no-simplify',)),
     ('fixed', 'ProofProduct', ('--release-storage',))])
def test_machine_absent_table_does_not_use_active_height_bound(
        toolchain, journal, directory, authority, entry, flags):
    candidate = optional_memory(authority)
    source, pair = source_and_inputs(candidate, authority)
    asset = journal.write('bundle.json', candidate[0])
    package, pin = compile_entry(toolchain, journal, directory, entry,
                                 flags=flags, source=source, asset=asset)
    assert pair[0]['memory_height'] == ('0' if authority == 'instance' else '64')
    proof, _ = prove_and_verify(toolchain, journal, directory, package, pin, 'absent', pair)

    # Admission must still reject missing/extra configuration, a substituted
    # fixed height, nonzero absent instance height, and present height > H.
    public, witness = pair
    changes = [('absent witness', {}, {'cells': ['0']})]
    if authority == 'instance':
        changes += [('absent height', {'memory_height': '8'}, {}),
                    ('absent public columns', {'schedule': ['0']}, {})]
    else:
        changes += [('short configuration', {'schedule': public['schedule'][:-1]}, {}),
                    ('extra configuration', {'schedule': public['schedule'] + ['0']}, {}),
                    ('zero height', {'memory_height': '0', 'schedule': []}, {}),
                    ('non-power height', {'memory_height': '3', 'schedule': ['0'] * 6}, {}),
                    ('height beyond policy', {'memory_height': '128', 'schedule': ['0'] * 256}, {})]
        if authority == 'fixed':
            changes.append(('fixed height substitution',
                            {'memory_height': '32', 'schedule': ['0'] * 64}, {}))
    present = optional_memory(authority, present=True)
    _, active = source_and_inputs(present, authority)
    changes.append(('present exceeds profile', active[0], active[1]))
    for name, shared, secret in changes:
        producer = input_files(journal, name + '-prover', public=public | shared,
                               witness=witness | secret)
        produced = directory / (name + '.proof')
        report = assert_refused(journal.attempt([
            toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}',
            *producer, f'--output={produced}']))
        assert report['code'].startswith('artifact-stopped'), (name, report)
        assert not produced.exists()
        if shared:
            verifier = input_files(journal, name + '-verifier', public=public | shared)
            report = assert_refused(journal.attempt([
                toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}',
                *verifier, f'--proof={proof}']))
            # Public-input binding can refuse before the verifier executes.
            assert report['code'].startswith(('artifact-stopped', 'proof-header')), (name, report)


@pytest.mark.parametrize('authority,height,power_of_two', [
    ('fixed', 1, True), ('fixed', 3, False),
    ('config', 1, True), ('config', 3, False),
])
@pytest.mark.parametrize('entry', ['ProofLogUp', 'ProofProduct'])
def test_absent_table_needs_no_polynomial_domain(
        toolchain, journal, directory, authority, height, power_of_two, entry):
    candidate = optional_memory(authority, height=height, power_of_two=power_of_two)
    source, pair = source_and_inputs(candidate, authority)
    asset = journal.write('bundle.json', candidate[0])
    package, pin = compile_entry(toolchain, journal, directory, entry,
                                source=source, asset=asset)
    assert pair[0]['memory_height'] == str(height)
    prove_and_verify(toolchain, journal, directory, package, pin, 'absent-small', pair)
    public, witness = pair
    for name, change in [
        ('short configuration', {'schedule': public['schedule'][:-1]}),
        ('extra configuration', {'schedule': public['schedule'] + ['0']}),
        ('present non-domain', {'memory_present': True}),
    ]:
        inputs = input_files(journal, name, public=public | change, witness=witness)
        output = directory / (name + '.proof')
        report = assert_refused(journal.attempt([
            toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}',
            *inputs, f'--output={output}']))
        assert report['code'].startswith('artifact-stopped'), (name, report)
        assert not output.exists()
