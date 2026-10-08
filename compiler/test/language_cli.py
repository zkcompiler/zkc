"""Fresh source capture, explicit Entry selection, and native runtime fixtures."""
import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
FIXTURES = Path(__file__).parent / 'fixtures/language'
modules = [f'--module={name}={FIXTURES / (name + ".zkc")}' for name in ('transfer', 'algebra')]
options = ['--source-format=zkc', '--entry=transfer::Demo', *modules]

with case('explicit source path retains its original and interface'):
    commands.run([compiler, 'language-check', *options])
    original = commands.run([compiler, 'language-emit', *options])
    interface = json.loads(commands.run([compiler, 'language-interface', *options]))
    assert interface['format'] == 'zkc.language-interface/3'
    assert interface['entry'] == 'transfer::Demo'
    assert interface['protocol'] == 's8_transfer8_Transfer'
    assert 'clauses' not in interface
    assert [p['name'] for p in interface['outputs']] == ['first', 'second', 'delta', 'ok']
    assert original.count('"protocol.exchange"') == 2
    assert original.count('"protocol.restrict_roles"') == 3
    (OUT / 'transfer.mlir').write_text(original)

with case('explicit assets change capture without changing executable original'):
    relations = Path(__file__).resolve().parents[2] / 'examples/relations'
    asset_args = [f'--asset=circuit=r1cs-json={relations / "multiply.r1cs.json"}',
                  f'--asset=trace_constraints=air-json={relations / "squaring.air.json"}']
    commands.run([compiler, 'language-check', *options, *asset_args])
    captured = json.loads(commands.run([compiler, 'language-interface', *options, *asset_args]))
    assert captured['capture'] != interface['capture']
    assert captured['original'] == interface['original']
    assert commands.run([compiler, 'language-emit', *options, *asset_args]) == original
    commands.run([compiler, 'language-check', *options, *asset_args, asset_args[0]], refuses='source.asset')
    commands.run([compiler, 'language-check', *options,
                  f'--asset=bad=guess={relations / "multiply.r1cs.json"}'], refuses='source.options')
    commands.run([compiler, 'language-check', *options,
                  f'--asset=bad=r1cs-binary={relations / "multiply.r1cs.json"}'], refuses='source.asset')

for optimized in (0, 1):
    for released in (0, 1):
        with case(f'participant compilation {optimized=} {released=}'):
            flags = ([] if optimized else ['--no-simplify']) + (['--release-storage'] if released else [])
            bundle = commands.run([compiler, 'language-bundle', *options, *flags])
            value = json.loads(bundle)
            assert value['entry'] == interface['protocol']
            assert value['roles'] == ['P', 'V']
            (OUT / f'transfer-{optimized}-{released}.bundle').write_text(bundle)

with case('same-signature protocols execute through distinct Entries'):
    source = OUT / 'entries.zkc'
    source.write_text('''module entries;
      domain Fr=field("bls12-381.fr");
      protocol First roles(P)(x:Fr@P)->(r:Fr@P){return(r=x+1);}
      protocol Second roles(P)(x:Fr@P)->(r:Fr@P){return(r=x*2);}
      math fn plus(x:Fr,)->Fr{return x+1;}
      math fn is_three(x:Fr,)->bool{return x==3;}
      protocol Helpers roles(P,)(x:Fr@P,)->(r:Fr@P,b:bool@P,){
        return(b=is_three(x,),r=entries::plus(x,),);
      }
      entry One=First; entry Two=Second; entry Alias=First; entry Math=Helpers;
    ''')
    for name, protocol in [('One', 'First'), ('Two', 'Second'), ('Alias', 'First'), ('Math', 'Helpers')]:
        args = ['--source-format=zkc', f'--entry=entries::{name}', f'--module=entries={source}']
        bundle = commands.run([compiler, 'language-bundle', *args])
        value = json.loads(bundle)
        assert value['entry'] == f's7_entries{len(protocol)}_{protocol}'
        (OUT / f'{name}.bundle').write_text(bundle)
        selected = json.loads(commands.run([compiler, 'language-interface', *args]))
        assert selected['entry'] == f'entries::{name}'
        assert selected['protocol'] == value['entry']

for args, refusal in [
    (options[1:], 'source.options'),
    ([*options, '--entry=other'], 'source.options'),
    ([*options, '--source-format=zkc'], 'source.options'),
    ([*options, '--guess'], 'source.options'),
    (['--source-format=json', *options[1:]], 'source.format'),
    (['--source-format=zkc', '--entry=transfer::Transfer', *modules], 'source.entry'),
    (['--source-format=zkc', '--entry=missing::Demo', *modules], 'source.entry'),
    (['--source-format=zkc', '--entry=transfer::Demo', modules[0]], 'source.import'),
    ([*options, modules[0]], 'source.module'),
]:
    with case(f'explicit invocation refuses {refusal}: {args[0]}'):
        commands.run([compiler, 'language-bundle', *args], refuses=refusal)

with case('target admission failure names its phase and related source declaration'):
    source = OUT / 'expansion.zkc'
    helpers = ['math fn f0()->Fr{return 1;}']
    helpers += [f'math fn f{i}()->Fr{{return f{i-1}()+f{i-1}();}}' for i in range(1, 18)]
    source.write_text('module expansion; domain Fr=field("bls12-381.fr");\n' + '\n'.join(helpers) +
                      '\nprotocol Small roles(P)()->(r:Fr@P){return(r=1);}' +
                      '\nprotocol Unused roles(P)()->(r:Fr@P){return(r=f17());}entry Demo=Unused;')
    attempt = commands.attempt([compiler, 'language-check', '--source-format=zkc',
                                '--entry=expansion::Demo', f'--module=expansion={source}'])
    assert attempt.returncode != 0 and not attempt.stdout
    diagnostic = attempt.stderr
    assert 'target.admission' in diagnostic
    assert 'related source declaration: expansion::' in diagnostic
    assert f'at {source}:' in diagnostic

for name in ('record', 'array', 'loop', 'variant', 'resource', 'component',
             'associated', 'associated_domain', 'bool', 'boolean_formula', 'branch', 'resource_control', 'group', 'variant_wire', 'variant_custody', 'index', 'dynamic', 'matrix', 'trace', 'vector_rounds'):
    args = ['--source-format=zkc', '--entry=sample::Demo',
            f'--module=sample={FIXTURES / (name + ".zkc")}']
    with case(f'typed source participant compilation: {name}'):
        for optimized in (0, 1):
            flags = [] if optimized else ['--no-simplify']
            bundle = commands.run([compiler, 'language-bundle', *args, *flags])
            (OUT / f'typed-{name}-{optimized}.bundle').write_text(bundle)
        schema = json.loads(commands.run([compiler, 'language-interface', *args]))
        for direction in ('inputs', 'outputs'):
            native = [index for port in schema[direction] for index in port['native']]
            assert native == list(range(len(native)))
        if name == 'record':
            assert schema['inputs'][0]['native'] == [0, 1]
            assert [f['name'] for f in schema['inputs'][0]['schema']['fields']] == ['left', 'right']
        if name == 'resource':
            assert schema['inputs'] == schema['outputs'] == []

for entry in ('Demo', 'LocalDemo'):
    with case(f'formal source mathematics: {entry}'):
        args = ['--source-format=zkc', f'--entry=sample::{entry}',
                f'--module=sample={FIXTURES / "polynomial.zkc"}']
        for optimized in (0, 1):
            for released in (0, 1):
                flags = ([] if optimized else ['--no-simplify']) + (['--release-storage'] if released else [])
                bundle = commands.run([compiler, 'language-bundle', *args, *flags])
                (OUT / f'polynomial-{entry}-{optimized}-{released}.bundle').write_text(bundle)

with case('protocol composition preserves distributed results'):
    args = ['--source-format=zkc', '--entry=sample::Demo',
            f'--module=sample={FIXTURES / "application.zkc"}']
    original = commands.run([compiler, 'language-emit', *args])
    assert original.count('"protocol.apply"') == 3
    for optimized in (0, 1):
        flags = [] if optimized else ['--no-simplify']
        bundle = commands.run([compiler, 'language-bundle', *args, *flags])
        (OUT / f'application-{optimized}.bundle').write_text(bundle)

with case('managed aliases retain ordered queries and owner guards'):
    args = ['--source-format=zkc', '--entry=sample::Demo',
            f'--module=sample={FIXTURES / "services.zkc"}']
    original = commands.run([compiler, 'language-emit', *args])
    assert original.count('"protocol.query"') == 2
    assert original.count('"protocol.guard"') == 1
    schema = json.loads(commands.run([compiler, 'language-interface', *args]))
    assert schema['services'] == [{'name': 'coins', 'owner': 'V',
                                   'contract': 'random.bls12-381.fr/1', 'native': 1}]
    for optimized in (0, 1):
        flags = [] if optimized else ['--no-simplify']
        bundle = commands.run([compiler, 'language-bundle', *args, *flags])
        (OUT / f'services-{optimized}.bundle').write_text(bundle)

for fixture in ('repeat', 'conditional_query', 'repeat_nested', 'repeat_affine'):
    with case(f'distributed control retains its region: {fixture}'):
        args = ['--source-format=zkc', '--entry=sample::Demo',
                f'--module=sample={FIXTURES / (fixture + ".zkc")}']
        original = commands.run([compiler, 'language-emit', *args])
        assert original.count('"protocol.repeat"') == (2 if fixture == 'repeat_nested' else 1)
        for optimized in (0, 1):
            flags = [] if optimized else ['--no-simplify']
            bundle = commands.run([compiler, 'language-bundle', *args, *flags])
            (OUT / f'{fixture}-{optimized}.bundle').write_text(bundle)


for fixture in ('completion', 'completion_nested', 'completion_affine'):
    with case(f'owner completion preserves native control: {fixture}'):
        args = ['--source-format=zkc', '--entry=sample::Demo',
                f'--module=sample={FIXTURES / (fixture + ".zkc")}']
        original = commands.run([compiler, 'language-emit', *args])
        assert original.count('"protocol.finish_if"') == 1
        for optimized in (0, 1):
            flags = [] if optimized else ['--no-simplify']
            bundle = commands.run([compiler, 'language-bundle', *args, *flags])
            (OUT / f'{fixture}-{optimized}.bundle').write_text(bundle)


for fixture in ('dispatch', 'service_order'):
    with case(f'selected closure keeps distinct bindings: {fixture}'):
        args = ['--source-format=zkc', '--entry=sample::Demo',
                f'--module=sample={FIXTURES / (fixture + ".zkc")}']
        for optimized in (0, 1):
            flags = [] if optimized else ['--no-simplify']
            bundle = commands.run([compiler, 'language-bundle', *args, *flags])
            (OUT / f'{fixture}-{optimized}.bundle').write_text(bundle)

counted()
