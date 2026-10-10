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

with case('definition checking never treats empty Entry selection as omission'):
    for args in [
        ['--source-format=zkc', '--entry=', *modules],
        ['--source-format=', '--source-format=zkc', *modules],
        ['--source-format=zkc', '--declarations', '--declarations', *modules],
        ['--source-format=zkc', '--no-simplify', *modules],
    ]:
        commands.run([compiler, 'language-check', *args], refuses='source.options')
    commands.run([compiler, 'language-emit', *options, '--declarations'], refuses='source.options')
    invalid = commands.attempt([compiler, 'language-check', '--unknown=\x1b\n'])
    assert invalid.returncode > 0 and '\x1b' not in invalid.stderr
    assert '\\1B' in invalid.stderr and len(invalid.stderr) < 65536

with case('explicit source path retains its original and interface'):
    commands.run([compiler, 'language-check', *options])
    original = commands.run([compiler, 'language-emit', *options])
    interface = json.loads(commands.run([compiler, 'language-interface', *options]))
    assert interface['format'] == 'zkc.language-interface/0'
    assert interface['entry'] == 'transfer::Demo'
    assert interface['protocol'] == 's8h7472616e736665728h5472616e73666572'
    protocol = next(p for p in interface['protocols'] if p['symbol'] == interface['protocol'])
    assert protocol['clauses'] == []
    assert [p['name'] for p in protocol['outputs']] == ['first', 'second', 'delta', 'ok']
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
            assert value['roles'] == ['role00000000', 'role00000001']
            (OUT / f'transfer-{optimized}-{released}.bundle').write_text(bundle)

with case('Entry packages retain exact source, interface and artifact bytes'):
    package_bytes = commands.run([compiler, 'language-package', *options])
    package = json.loads(package_bytes)
    assert set(package) == {'format', 'original', 'interface', 'artifact', 'assets', 'options'}
    assert package['format'] == 'zkc.entry/0'
    assert package['original'] == commands.run([compiler, 'language-emit', *options])
    assert json.loads(package['interface']) == interface
    assert package['artifact'] == commands.run([compiler, 'language-bundle', *options]).removesuffix('\n')
    assert package['options'] == {'simplify': True, 'release_storage': False}
    assert package_bytes.endswith('}')
    (OUT / 'transfer.zkpkg').write_text(package_bytes)

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
      run One=First; run Two=Second; run Alias=First; run Math=Helpers;
    ''')
    for name, protocol in [('One', 'First'), ('Two', 'Second'), ('Alias', 'First'), ('Math', 'Helpers')]:
        args = ['--source-format=zkc', f'--entry=entries::{name}', f'--module=entries={source}']
        bundle = commands.run([compiler, 'language-bundle', *args])
        value = json.loads(bundle)
        assert value['entry'] == f's7h656e7472696573{len(protocol)}h{protocol.encode().hex()}'
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
                      '\nprotocol Unused roles(P)()->(r:Fr@P){return(r=f17());}run Demo=Unused;')
    definitions = json.loads(commands.run([compiler, 'language-check', '--source-format=zkc',
                                             f'--module=expansion={source}']))
    assert definitions['scope'] == 'definitions'
    attempt = commands.attempt([compiler, 'language-check', '--source-format=zkc',
                                '--entry=expansion::Demo', f'--module=expansion={source}'])
    assert attempt.returncode > 0 and not attempt.stdout
    diagnostic = attempt.stderr
    assert 'target.admission' in diagnostic
    assert 'related source declaration: expansion::' in diagnostic
    assert f'at {source}:' in diagnostic

for name in ('record', 'array', 'loop', 'variant', 'resource', 'component',
             'associated', 'associated_domain', 'bool', 'boolean_formula', 'branch', 'resource_control', 'group', 'variant_wire', 'variant_custody', 'index', 'dynamic', 'matrix', 'trace', 'vector_rounds', 'host_values'):
    args = ['--source-format=zkc', '--entry=sample::Demo',
            f'--module=sample={FIXTURES / (name + ".zkc")}']
    with case(f'typed source participant compilation: {name}'):
        for optimized in (0, 1):
            flags = [] if optimized else ['--no-simplify']
            bundle = commands.run([compiler, 'language-bundle', *args, *flags])
            (OUT / f'typed-{name}-{optimized}.bundle').write_text(bundle)
            if optimized:
                package = commands.run([compiler, 'language-package', *args, *flags])
                (OUT / f'typed-{name}.zkpkg').write_text(package)
        schema = json.loads(commands.run([compiler, 'language-interface', *args]))
        schema = next(p for p in schema['protocols'] if p['symbol'] == schema['protocol'])
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
    schema = next(p for p in schema['protocols'] if p['symbol'] == schema['protocol'])
    assert schema['services'] == [{'name': 'coins', 'owner': 'V',
                                   'contract': 'random.bls12-381.fr/0', 'native': 1}]
    (OUT / 'host-services.zkpkg').write_text(commands.run([compiler, 'language-package', *args]))
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

for fixture, entry in [('relation_sumcheck', 'Demo'), ('relation_sumcheck', 'ProductControl'),
                       ('relation_r1cs', 'Demo'), ('relation_group', 'Demo'),
                       ('specification_execution', 'Demo')]:
    with case(f'source relation execution boundary: {fixture}::{entry}'):
        args = ['--source-format=zkc', f'--entry=sample::{entry}',
                f'--module=sample={FIXTURES / (fixture + ".zkc")}']
        schema = json.loads(commands.run([compiler, 'language-interface', *args]))
        selected = next(p for p in schema['protocols'] if p['symbol'] == schema['protocol'])
        assert len(selected['clauses']) == (0 if entry == 'ProductControl' else 1)
        if selected['clauses']:
            assert schema['relations']
        for optimized in (0, 1):
            flags = [] if optimized else ['--no-simplify']
            bundle = commands.run([compiler, 'language-bundle', *args, *flags])
            (OUT / f'{fixture}-{entry}-{optimized}.bundle').write_text(bundle)

with case('source Host export admission retains affine custody obligations'):
    args = ['--source-format=zkc', '--entry=sample::Demo',
            f'--module=sample={FIXTURES / "completion_affine.zkc"}']
    package = commands.run([compiler, 'language-package', *args])
    (OUT / 'host-custody.zkpkg').write_text(package)

with case('maximum source schema depth binds in the native Host'):
    nested = 'bool'
    for _ in range(30):
        nested = f'({nested},)'
    source = OUT / 'deep-schema.zkc'
    source.write_text(f"""module deep;
type Inner = {nested};
type Deep = (Inner,);
protocol Identity roles(P)(value:Deep@P)->(result:Deep@P){{return(result=value);}}
run Demo=Identity;
""")
    args = ['--source-format=zkc', '--entry=deep::Demo', f'--module=deep={source}']
    package = commands.run([compiler, 'language-package', *args])
    schema = json.loads(json.loads(package)['interface'])['protocols'][0]['inputs'][0]['schema']
    depth = 1
    while schema['fields']:
        schema = schema['fields'][0]['schema']
        depth += 1
    assert depth == 32
    (OUT / 'deep-schema.zkpkg').write_text(package)

for suite, identity in enumerate(('merlin3.bls12-381.fr64be/0',
                                   'spongefish0.7.4.keccak.bls12-381.fr64be/0')):
    with case(f'proof Entry compiles through explicit construction: {identity}'):
        source = OUT / f'proof-{suite}.zkc'
        source.write_text((FIXTURES / 'schnorr.zkc').read_text().replace(
            'merlin3.bls12-381.fr64be/0', identity))
        args = ['--source-format=zkc', '--entry=sample::Demo', f'--module=sample={source}']
        schema = json.loads(commands.run([compiler, 'language-interface', *args]))
        assert schema['job']['construction']['suite'] == identity
        assert schema['job']['public'] == [0, 1]
        for simplified in (0, 1):
            for released in (0, 1):
                flags = ([] if simplified else ['--no-simplify']) + (['--release-storage'] if released else [])
                deployment = commands.run([compiler, 'language-bundle', *args, *flags])
                assert json.loads(deployment)[0] == 'zkc.native-proof/0'
                (OUT / f'source-proof-{suite}-{simplified}-{released}.json').write_text(deployment)
                package = commands.run([compiler, 'language-package', *args, *flags])
                assert json.loads(package)['artifact'] == deployment.removesuffix('\n')
                (OUT / f'source-proof-{suite}-{simplified}-{released}.zkpkg').write_text(package)

with case('publish authored proof with logical products and empty public inputs'):
    args = ['--source-format=zkc', '--entry=sample::Demo',
            f'--module=sample={FIXTURES / "host_proof.zkc"}']
    package = commands.run([compiler, 'language-package', *args])
    (OUT / 'host-proof.zkpkg').write_text(package)

for entry in ('Run', 'Prove'):
    with case(f'source setup associations compile through common native execution: {entry}'):
        args = ['--source-format=zkc', f'--entry=sample::{entry}',
                f'--module=sample={FIXTURES / "pcs_setup.zkc"}']
        package = commands.run([compiler, 'language-package', *args])
        interface = json.loads(json.loads(package)['interface'])
        assert [slot['name'] for slot in interface['setups']] == ['first', 'second']
        assert interface['setups'][1]['inputs'] == [{'port': 4, 'path': []}, {'port': 5, 'path': []}]
        (OUT / f'pcs-setup-{entry}.zkpkg').write_text(package)

for entry in ('Derived', 'Plain', 'Once', 'Run'):
    with case(f'named attempt selection and operational budgets: {entry}'):
        source = OUT / f'attempt-{entry}.zkc'
        source.write_text((FIXTURES / 'attempts.zkc').read_text())
        suites = ('merlin3.bls12-381.fr64be/0', 'spongefish0.7.4.keccak.bls12-381.fr64be/0') if entry == 'Derived' else ('merlin3.bls12-381.fr64be/0',)
        for suite, identity in enumerate(suites):
            source.write_text((FIXTURES / 'attempts.zkc').read_text().replace(suites[0], identity))
            args = ['--source-format=zkc', f'--entry=sample::{entry}', f'--module=sample={source}']
            package = commands.run([compiler, 'language-package', *args])
            view = json.loads(json.loads(package)['interface'])
            if entry in ('Derived', 'Plain'):
                assert view['job']['completion'] == {'direction':'output', 'port':1, 'role':'P', 'path':[0]}
            elif entry == 'Once':
                assert view['job']['completion'] is None
            (OUT / f'attempt-{entry}-{suite}.zkpkg').write_text(package)

counted()
