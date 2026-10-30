"""Subtractive CPU installation selection through the owned compiler driver."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / 'fixtures'


def descriptor(name, providers):
    path = OUT / f'{name}.json'
    path.write_text(json.dumps({'format': 'zkc.cpu-target/0', 'providers': providers}))
    return f'--cpu-target={path}'


small = descriptor('small', ['plonky3'])
empty = descriptor('empty', [])
full = descriptor('full', ['arkworks', 'blst', 'dalek', 'halo2curves', 'plonky3'])


def source_options(text, entry='sample::Demo', name='sample'):
    path = OUT / f'{name}.zkc'
    path.write_text(text)
    return ['--source-format=zkc', '--entry=' + entry, f'--module=sample={path}']


def service_program(field, index=False):
    service = f'!protocol.service_ref<"random.{field}/0">'
    result = 'ui64' if index else 'i1'
    query = (
        f'%bound = "data.index"() {{value=4 : ui64}} : ()->ui64\n %reply = "protocol.query"(%coins,%bound) '
        f'{{method="index",owner="P",site="sample"}} : ({service},ui64)->ui64'
        if index else ''
    )
    value = '%reply' if index else '%value'
    return f'''module {{ "protocol.module"() ({{
      "protocol.func"() ({{ ^entry(%coins:{service},%value:{result}):
        {query}
        "protocol.return"({value}) : ({result})->()
      }}) {{sym_name="main",function_type=({service},{result})->{result},
        roles=["P"],input_roles=[["P"],["P"]],output_roles=[["P"]]}} : ()->()
    }}) {{profile=#protocol.profile<protocol>}} : ()->() }}'''


for index in (False, True):
    with case('unused service' if not index else 'index-only service'):
        text = service_program('goldilocks.ext2-binomial7', index)
        commands.source('protocol-bundle', text, small)
        commands.source('protocol-bundle', text, empty, refuses='cpu-target-unavailable')
        for options in ((), ('--no-simplify',)):
            omitted = service_program('bls12-381.fr')
            commands.source('protocol-bundle', omitted, small, *options,
                            refuses='cpu-target-unavailable')

with case('empty installation preserves a provider-independent Host entry'):
    options = source_options('module sample; entry fn Demo(x:bool)->bool{return x;}')
    baseline = commands.run([compiler, 'language-package', *options])
    assert commands.run([compiler, 'language-package', *options, empty]) == baseline

with case('generic numerical Host compilation and target-independent checking'):
    for field in ('koala-bear', 'bls12-381.fr'):
        options = source_options(f'''module sample;
          domain Fr=field("{field}");
          math fn add<F:Field>(x:F,y:F)->F{{return x+y;}}
          fn work(x:Fr)->Fr{{return add<Fr>(x,x);}}
          entry fn Demo(x:Fr)->Fr{{return work(x);}}''')
        logical = commands.run([compiler, 'language-check', *options])
        assert commands.run([compiler, 'language-check', *options, empty]) == logical
        original = commands.run([compiler, 'language-emit', *options])
        assert commands.run([compiler, 'language-emit', *options, empty]) == original
        if field == 'koala-bear':
            package = commands.run([compiler, 'language-package', *options, small])
            assert 'plonky3/numerical.' in package or 'plonky3/field.add' in package
        else:
            commands.run([compiler, 'language-package', *options, small],
                         refuses='cpu-target-unavailable')

for field in ('koala-bear', 'bls12-381.fr'):
    with case(f'generic Host call preserves target at internal-field child: {field}'):
        options = source_options(f'''module sample;
          domain Fr=field("{field}");
          fn from_index<F:Field>(value:index)->F=primitive("field.from_index");
          protocol Child<F:Field> roles(P)(x:index@P)->(value:bool@P){{
            let a=from_index<F>(x);return(value=a==0);}}
          protocol Work<F:Field> roles(P)(x:index@P)->(value:bool@P){{
            let value=Child<F>(x);return(value=value);}}
          entry fn Relay(inputs:Work<Fr>::Inputs){{return Work<Fr>::run(inputs);}}
          entry fn Demo(inputs:Work<Fr>::Inputs){{return Relay(inputs);}}''',
                                 name=f'internal-field-{field}')
        # The default-target control must publish the same Host call and child
        # even for the field omitted by the reduced installation.
        baseline = json.loads(commands.run([compiler, 'language-package', *options],
                                          keep=f'internal-field-{field}-baseline'))
        host = json.loads(baseline['artifact'])
        assert host['format'] == 'zkc.host/0'
        assert len(host['functions']) == 2 and len(host['deployments']) == 1
        for function in host['functions']:
            signature = function['signature']
            schemas = [p['schema'] for p in signature['parameters']] + [signature['result']]
            leaves = {leaf for schema in schemas for leaf in schema['leaves']}
            assert leaves == {'index', 'bool'}, 'outer Host ports expose nongeneric data'
        deployment = host['deployments'][0]['id']
        demo = next(f for f in host['functions']
                    if f['signature']['symbol'] == host['entry'])
        relay = next(f for f in host['functions']
                     if f['signature']['symbol'] != host['entry'])
        assert any(op['op'] == 'call' and op['callee'] == relay['signature']['symbol']
                   for op in demo['body']['operations'])
        assert any(op['op'] == 'invoke' and op['deployment'] == deployment
                   for op in relay['body']['operations'])
        observations = OUT / f'internal-field-{field}.json'
        package = commands.run(
            [compiler, 'language-package', *options, small,
             f'--observations={observations}'],
            refuses=None if field == 'koala-bear' else 'cpu-target-unavailable',
            keep=f'internal-field-{field}-reduced')
        journal = json.loads(observations.read_text())
        assert journal['completed'] == (field == 'koala-bear')
        physical_passes = [p for p in journal['passes']
                           if p['pass'] == 'zkc-select-physical']
        assert physical_passes, 'physical pass observation was never reached'
        for record in physical_passes:
            expected_names = {'linear-contraction-eligible', 'linear-contraction-selected',
                              'linear-contraction-selected-producers'}
            statistics = record['statistics']
            assert isinstance(record['statistics_enabled'], bool)
            assert {s['name'] for s in statistics} == (
                expected_names if record['statistics_enabled'] else set())
            assert all(type(s['value']) is int and s['value'] >= 0 for s in statistics)
        phases = [phase for phase in journal['phases']
                  if phase['unit'] == ['sample::Demo', deployment, 'sample::Work']]
        assert any(phase['phase'] == 'protocol' and
                   phase['histogram'].get('algebra.field_equal', 0) > 0
                   for phase in phases), 'internal child field computation was never reached'
        assert any(phase['phase'] == 'exec' for phase in phases), 'child lowering was never reached'
        if field == 'koala-bear':
            assert 'plonky3/field.from_index' in package

with case('inactive aggregate alternatives and zero-length numerical children'):
    for field in ('koala-bear', 'bls12-381.fr'):
        for payload in ('Choice', '[Fr;0]'):
            options = source_options(f'''module sample;
              domain Fr=field("{field}");
              enum Choice {{Empty(),Hidden((bool,[Fr;0]),Fr)}}
              entry fn Demo(x:{payload})->{payload}{{return x;}}''')
            commands.run([compiler, 'language-package', *options, small],
                         refuses=None if field == 'koala-bear' else 'cpu-target-unavailable')

with case('explicit full target preserves proof deployment bytes'):
    args = ['--source-format=zkc', '--entry=sample::Demo',
            f'--module=sample={FIXTURES / "language/host_proof.zkc"}']
    baseline = commands.run([compiler, 'language-bundle', *args])
    assert commands.run([compiler, 'language-bundle', *args, full]) == baseline
    commands.run([compiler, 'language-bundle', *args, small],
                 refuses='cpu-target-unavailable')

with case('Protocol IR proof driver receives the same target'):
    path = FIXTURES / 'mathematical/relation-r1cs.mlir'
    policy = OUT / 'policy.json'
    policy.write_text(json.dumps(['zkc.native-proof-policy/0', 'main', 'P', 'V',
                                  '1', '', [], ['0', '1'], [], 'zkc.framed/0', '']))
    args = [compiler, 'protocol-proof', path, policy]
    baseline = commands.run(args)
    assert commands.run([*args, full]) == baseline
    commands.run([*args, empty], refuses='cpu-target-unavailable')
    commands.run([*args, full, empty], refuses='native-proof-options')

with case('malformed, unknown and oversized target files refuse before publication'):
    options = source_options('module sample; entry fn Demo(x:bool)->bool{return x;}')
    for text, code in [
        ('{"format":"zkc.cpu-target/0","providers":["unknown"]}', 'cpu-target-invalid'),
        ('{"format":"zkc.cpu-target/0","providers":[],"providers":[]}', 'cpu-target-invalid'),
        ('{"format":"zkc.cpu-target/1","providers":[]}', 'cpu-target-invalid'),
        (' ' * 4097, 'cpu-target-limit'),
    ]:
        path = OUT / 'malformed.json'
        path.write_text(text)
        commands.run([compiler, 'language-package', *options, f'--cpu-target={path}'],
                     refuses=code)
    commands.run([compiler, 'language-package', *options, full, empty],
                 refuses='source.options')
    commands.run([compiler, 'language-package', *options, '--cpu-target='],
                 refuses='cpu-target-invalid')

print(f'CPU target driver: {counted()} cases')
