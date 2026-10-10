"""Finite vector binders and checked fusion through source compilation and Host.

Integer and extension-polynomial arithmetic below supply independent expected
values. Resource comparisons describe these executions, not a refinement theorem.
"""
import json
import math
import random
from pathlib import Path

import pytest

from entry import Entry
from octic_reference import ONE, P, ZERO, add, coordinates, mul

ROOT = Path(__file__).resolve().parents[2]
FIELDS = [
    ('bls12-381.fr', 1, 66, 32,
     52435875175126190479447740508185965837690552500527637822603658699938581184513),
    ('bn254.fr', 40, 41, 32,
     21888242871839275222246405745257275088548364400416034343698204186575808495617),
    ('ristretto255.scalar', 13, 14, 32, 2**252 + 27742317777372353535851937790883648493),
    ('koala-bear', 19, 20, 4, P),
]
OPTIONS = [[], ['--fuse-vector-reductions'],
           ['--fuse-vector-reductions', '--no-simplify'],
           ['--fuse-vector-reductions', '--release-storage']]

SOURCE = '''module sample;
domain F = field("FIELD");
type Vector<E: Field> = builtin("vector", E);
fn sum<E: Field>(v: Vector<E>) -> E = primitive("vector.sum");
fn product<E: Field>(v: Vector<E>) -> E = primitive("vector.product");
reduction ∑ = sum;
reduction ∏ = product;
fn work<E: Field>(a: Vector<E>, b: Vector<E>, ignored: Vector<E>, α: E)
    -> (E,E,E,E,E,E) {
  let zipped = ∑ [(x,y,_) in zip(a,b,ignored)] { x*y };
  let named = reduce sum [(x,y,_) in zip(a,b,ignored)] { x*y };
  let products = ∏ [(x,y,_) in zip(a,b,ignored)] { x*y };
  let native = product(a);
  let shifted = ∑ [x in a] { α*x+α };
  let square = ∑ [x in a] { x*x };
  return (zipped,named,products,native,shifted,square);
}
protocol Run roles(P)(a:Vector<F>@P,b:Vector<F>@P,ignored:Vector<F>@P,α:F@P)
    -> (result:(F,F,F,F,F,F)@P) { return work(a,b,ignored,α); }
run Demo = Run;
'''


def field_wire(tag, value, width=4):
    payload = coordinates(value) if isinstance(value, list) else value.to_bytes(width, 'little')
    return (b'ZKCV\0' + bytes([tag]) + payload).hex()


def vector_wire(tag, values, width=4):
    payload = b''.join(coordinates(x) if isinstance(x, list) else x.to_bytes(width, 'little')
                       for x in values)
    return (b'ZKCV\0' + bytes([tag]) + len(values).to_bytes(4, 'little') + payload).hex()


def subdirectory(directory, name):
    result = directory / name
    result.mkdir()
    return result


@pytest.mark.parametrize('flags', OPTIONS)
@pytest.mark.parametrize('field,scalar_tag,vector_tag,width,modulus', FIELDS)
def test_prime_reductions_values_empty_and_all_zip_guards(
    toolchain, journal, directory, flags, field, scalar_tag, vector_tag, width, modulus,
):
    entry = Entry(toolchain, journal, directory, SOURCE.replace('FIELD', field), flags)
    rng = random.Random(7951)
    def scalar(x):
        return field_wire(scalar_tag, x, width)
    def vector(xs):
        return vector_wire(vector_tag, xs, width)
    for n in (0, 1, 3, 17):
        a, b = ([rng.randrange(modulus) for _ in range(n)] for _ in range(2))
        if n >= 3:
            a[:3] = [0, 1, modulus-1]
        α = modulus-2
        rows = [x*y % modulus for x, y in zip(a, b, strict=True)]
        expected = [sum(rows), sum(rows), math.prod(rows), math.prod(a),
                    sum(α*x+α for x in a), sum(x*x for x in a)]
        inputs = {'a': vector(a), 'b': vector(b), 'ignored': vector([1]*n), 'α': scalar(α)}
        assert entry.run(f'rows-{n}', inputs)['result'] == [scalar(x % modulus) for x in expected]
    for name, a, b, ignored in [('used', [2, 3], [5], [7, 7]),
                               ('ignored', [2, 3], [5, 7], [7]),
                               ('empty', [], [], [1])]:
        refused = entry.run(name, {'a': vector(a), 'b': vector(b), 'ignored': vector(ignored),
                                   'α': scalar(1)}, refuses='entry-run-incomplete')
        assert 'rejected:require' in json.dumps(refused)


@pytest.mark.parametrize('flags', OPTIONS)
def test_extension_reductions_use_full_coefficients(toolchain, journal, directory, flags):
    entry = Entry(toolchain, journal, directory,
                  SOURCE.replace('FIELD', 'koala-bear.ext8-binomial3'), flags)
    rng = random.Random(9102)
    for n in (0, 1, 4):
        a, b = ([[rng.randrange(P) for _ in range(8)] for _ in range(n)] for _ in range(2))
        α = [rng.randrange(P) for _ in range(8)]
        rows = [mul(x, y) for x, y in zip(a, b, strict=True)]
        def fold(values, operation, initial):
            result = initial
            for value in values:
                result = operation(result, value)
            return result
        expected = [fold(rows, add, ZERO), fold(rows, add, ZERO), fold(rows, mul, ONE),
                    fold(a, mul, ONE), fold([add(mul(α, x), α) for x in a], add, ZERO),
                    fold([mul(x, x) for x in a], add, ZERO)]
        inputs = {'a': vector_wire(27, a), 'b': vector_wire(27, b),
                  'ignored': vector_wire(27, [ONE]*n), 'α': field_wire(26, α)}
        assert entry.run(f'rows-{n}', inputs)['result'] == [field_wire(26, x) for x in expected]
    refused = entry.run('ignored-empty', {'a': vector_wire(27, []), 'b': vector_wire(27, []),
                        'ignored': vector_wire(27, [ONE]), 'α': field_wire(26, ONE)},
                        refuses='entry-run-incomplete')
    assert 'rejected:require' in json.dumps(refused)


@pytest.mark.parametrize('flags', OPTIONS[:2])
def test_collections_execute_once_in_written_order(toolchain, journal, directory, flags):
    source = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
fn sum(v:Vector<F>)->F=primitive("vector.sum");
fn fill(x:F,n:index)->Vector<F>=primitive("vector.fill");
fn work(n:index)->(F,index){
  let mut state=0;
  let result=reduce sum [(x,y) in zip(
      {state=state+1; fill(2,n)}, {state=state*10+3; fill(5,n)})] {x*y};
  return(result,state);
}
protocol Run roles(P)(n:index@P)->(result:(F,index)@P){return work(n);}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    for n in (0, 3):
        assert entry.run(f'rows-{n}', {'n': n})['result'] == [field_wire(19, 10*n), 13]


@pytest.mark.parametrize('flags', OPTIONS[:2])
def test_custom_reducer_keeps_its_stop(toolchain, journal, directory, flags):
    source = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
fn length(v:Vector<F>)->index=primitive("vector.length");
fn sum(v:Vector<F>)->F=primitive("vector.sum");
fn nonempty(v:Vector<F>)->F{require length(v)>0;return sum(v);}
reduction ∑=nonempty;
fn work(a:Vector<F>,b:Vector<F>)->F{return ∑ [(x,y) in zip(a,b)] {x*y};}
protocol Run roles(P)(a:Vector<F>@P,b:Vector<F>@P)->(result:F@P){return work(a,b);}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('nonempty', {'a': vector_wire(20, [2, 3]),
                                 'b': vector_wire(20, [5, 7])})['result'] == field_wire(19, 31)
    refused = entry.run('empty', {'a': vector_wire(20, []), 'b': vector_wire(20, [])},
                        refuses='entry-run-incomplete')
    assert 'rejected:require' in json.dumps(refused)


@pytest.mark.parametrize('flags', OPTIONS)
def test_published_finite_reductions_project(toolchain, journal, directory, flags):
    package = directory / 'reductions.zkpkg'
    built = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                          f'--project={ROOT}/examples/projects/finite-reductions/zkc.toml',
                          'example::Demo', f'--output={package}', *flags])
    request = journal.write('input.json', {'format': 'zkc.entry-run/0', 'session': 'reductions',
        'roles': {'P': {'inputs': {'left': vector_wire(20, [2, 3]),
            'right': vector_wire(20, [5, 7]), 'α': field_wire(19, 2)}}}})
    outputs = directory / 'outputs.json'
    result = journal.json([toolchain.runtime, 'run', package, built['package_sha256'], request,
                           f'--results={outputs}'])
    assert result['status'] == 'executed'
    assert json.loads(outputs.read_text())['roles']['P'] == {
        'symbolic': field_wire(19, 31), 'named': field_wire(19, 31),
        'dot': field_wire(19, 31), 'product': field_wire(19, 20)}
    assert json.loads(package.read_text())['options']['fuse_vector_reductions'] == \
        ('--fuse-vector-reductions' in flags)


MAP_SUM = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
math fn times(x:F,y:F,ignored:F)->F{return x*y;}
fn sum(v:Vector<F>)->F=primitive("vector.sum");
fn work(a:Vector<F>,b:Vector<F>,unused:Vector<F>)->F{
  let mapped=map times(each a,each b,each unused);
  return sum(mapped);
}
protocol Run roles(P)(a:Vector<F>@P,b:Vector<F>@P,unused:Vector<F>@P)->(result:F@P){
  return work(a,b,unused);
}
run Demo=Run;
'''


def run_report(entry, name, inputs, capacity=None, refuses=None):
    request = entry.journal.write(f'{name}.inputs.json', {
        'format': 'zkc.entry-run/0', 'session': 'reduction_resources',
        'roles': {'P': {'inputs': inputs}}})
    output = entry.directory / f'{name}.outputs.json'
    command = [entry.tools.runtime, 'run', entry.package, entry.pin, request,
               f'--results={output}']
    if capacity:
        command.append(f'--capacity={capacity}')
    result = entry.journal.json(command, refuses=refuses)
    if refuses:
        assert not output.exists()
    return result


@pytest.mark.parametrize('extra', [[], ['--no-simplify'], ['--release-storage']])
def test_fusion_preserves_values_and_guards_with_different_resource_charges(
    toolchain, journal, directory, extra,
):
    entries = {name: Entry(toolchain, journal, subdirectory(directory, name), MAP_SUM,
                           [*extra, *flags])
               for name, flags in [('baseline', []), ('fused', ['--fuse-vector-reductions'])]}
    n = 1024
    inputs = {'a': vector_wire(20, [2]*n), 'b': vector_wire(20, [3]*n),
              'unused': vector_wire(20, [7]*n)}
    usage = {}
    for name, entry in entries.items():
        report = run_report(entry, f'{name}-usage', inputs)
        assert report['status'] == 'executed'
        usage[name] = report['execution']['roles'][0]['usage']
        assert entry.run(f'{name}-value', inputs)['result'] == field_wire(19, 6*n)
        for case, changed in [('ignored', {'unused': vector_wire(20, [7])}),
                               ('used', {'b': vector_wire(20, [])})]:
            refused = entry.run(f'{name}-{case}', inputs | changed,
                                refuses='entry-run-incomplete')
            assert 'rejected:require' in json.dumps(refused)
    baseline, fused = usage['baseline'], usage['fused']
    # Separate ledgers: fewer instructions and cumulative allocations in this
    # fixed case do not imply identical exhaustion or lower peak live storage.
    assert fused['instructions'] < baseline['instructions']
    assert fused['logical_bytes'] < baseline['logical_bytes']
    assert fused['total_value_bytes'] < baseline['total_value_bytes']
    ceiling = (fused['total_value_bytes'] + baseline['total_value_bytes']) // 2
    capacity = journal.write('between-allocation-charges.json', [
        'zkc.native-capacity/0', '65536', '4096', '16777216', '67108864',
        ['1000000', '100000', '4294967296'], [str(ceiling), str(ceiling)]])
    assert run_report(entries['fused'], 'limited-fused', inputs, capacity)['status'] == 'executed'
    refused = run_report(entries['baseline'], 'limited-baseline', inputs, capacity,
                         refuses='entry-run-incomplete')
    assert 'exhausted' in json.dumps(refused).lower()


PROOF = '''module sample;
domain F=field("bls12-381.fr");
type Vector<E:Field>=builtin("vector",E);
fn sum(v:Vector<F>)->F=primitive("vector.sum");
fn weighted(a:Vector<F>,b:Vector<F>)->F{
  return reduce sum [(x,y) in zip(a,b)] {x*y};
}
protocol Check roles(P,V)(a:Vector<F>@(P,V),b:Vector<F>@(P,V),coins:Random<F>@V)
    ->(accepted:bool@V){
  let challenge=coins.draw();
  let delivered=send V->P(challenge);
  let answer @P=weighted(a,b)+delivered;
  let received=send P->V(answer);
  let expected @V=weighted(a,b)+challenge;
  let accepted @V=received==expected;
  return(accepted=accepted);
}
proof Demo=Check{prover P;verifier V;public{a,b};accept accepted;
  construction fiat_shamir("merlin3.bls12-381.fr64be/0",coins);}
'''


def test_fusion_proof_construction_preserves_protocol_origins(toolchain, journal, directory):
    descriptors = []
    for name, flags in [('baseline', []), ('fused', ['--fuse-vector-reductions'])]:
        entry = Entry(toolchain, journal, subdirectory(directory, name), PROOF, flags)
        package = json.loads(entry.package.read_text())
        deployment = json.loads(package['artifact'])
        assert deployment[7] == ['true', 'false', 'true' if flags else 'false']
        descriptors.append(deployment[2])
        request = journal.write(f'{name}.proof-inputs.json', {
            'format': 'zkc.entry-proof/0', 'public': {
                'a': vector_wire(66, [2, 3], 32), 'b': vector_wire(66, [5, 7], 32)},
            'inputs': {}})
        proof = entry.directory / 'proof.bin'
        journal.json([toolchain.runtime, 'prove', entry.package, entry.pin, request, proof])
        verified = journal.json([toolchain.runtime, 'verify', entry.package, entry.pin, request, proof])
        assert verified['status'] == 'accepted' and verified['binding_scope'] == 'transcript'
        truncated = entry.directory / 'truncated.bin'
        truncated.write_bytes(proof.read_bytes()[:-1])
        journal.json([toolchain.runtime, 'verify', entry.package, entry.pin, request, truncated],
                     refuses='proof-truncated')
    assert descriptors[0] == descriptors[1]


def test_fusion_flag_is_compile_only(toolchain, journal, directory):
    source = directory / 'sample.zkc'
    source.write_text(MAP_SUM)
    journal.run([toolchain.compiler, 'language-check', '--source-format=zkc',
                 f'--module=sample={source}', '--fuse-vector-reductions'], refuses='source.options')
    journal.json([toolchain.runtime, 'check', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', '--fuse-vector-reductions'], refuses=True)


@pytest.mark.parametrize('flags', OPTIONS[:2])
def test_binder_and_body_shadowing_keep_outer_values(toolchain, journal, directory, flags):
    source = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
fn sum(v:Vector<F>)->F=primitive("vector.sum");
fn work(a:Vector<F>,x:F,α:F)->(F,F){
  let total=reduce sum [x in a] {let x=x+1; x*α};
  return(total,x);
}
protocol Run roles(P)(a:Vector<F>@P,x:F@P,α:F@P)->(result:(F,F)@P){return work(a,x,α);}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    assert entry.run('shadowed', {'a': vector_wire(20, [2, 3]), 'x': field_wire(19, 77),
                                 'α': field_wire(19, 5)})['result'] == [
                                     field_wire(19, 35), field_wire(19, 77)]
