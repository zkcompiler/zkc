"""Finite vector binders and checked fusion through source compilation and Host.

Integer and extension-polynomial arithmetic below supply independent expected
values. Resource comparisons describe these executions, not a refinement theorem.
"""
import json
import math
import random
from pathlib import Path

import pytest

from entry import Entry, joint_execution, joint_package
from input_files import decimal_values, input_files
from octic_reference import ONE, P, ZERO, add, mul
from test_total_callback_selection import operation_sites

ROOT = Path(__file__).resolve().parents[3]
FIELDS = [
    ('bls12-381.fr',
     52435875175126190479447740508185965837690552500527637822603658699938581184513),
    ('bn254.fr',
     21888242871839275222246405745257275088548364400416034343698204186575808495617),
    ('ristretto255.scalar', 2**252 + 27742317777372353535851937790883648493),
    ('koala-bear', P),
]
OPTIONS = [[], ['--fuse-vector-reductions'],
           ['--fuse-vector-reductions', '--no-simplify'],
           ['--fuse-vector-reductions', '--release-storage']]

FINITE = '''
domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("zip");
fn fold<I:Type+Copy+Drop,S:Type>(rows:domain<I>,initial:S,step:fn(S,item:I)->S effects(stop) where item_from(item, rows))->S effects(stop)=finite("local.fold");
fn sum<I:Type+Copy+Drop,E:Field>(rows:domain<I>,term:fn(item:I)->E effects(stop) where item_from(item, rows))->E effects(stop){return fold(rows,0,fn(state, item)=>state+term(item));}
fn product<I:Type+Copy+Drop,E:Field>(rows:domain<I>,term:fn(item:I)->E effects(stop) where item_from(item, rows))->E effects(stop){return fold(rows,1,fn(state, item)=>state*term(item));}
reduction ∑=sum;
reduction ∏=product;
'''


SOURCE = '''module sample;
domain F = field("FIELD");
type Vector<E: Field> = builtin("vector", E);
FINITE
fn vector_product<E:Field>(v:Vector<E>)->E=primitive("vector.product");
fn work<E: Field>(a: Vector<E>, b: Vector<E>, ignored: Vector<E>, α: E)
    -> (E,E,E,E,E,E) {
  let zipped = ∑ ((x,y),_) in zip(zip(a,b),ignored), x*y;
  let named = sum(zip(zip(a,b),ignored),fn(((x,y),_))=>x*y);
  let products = ∏ ((x,y),_) in zip(zip(a,b),ignored), x*y;
  let native = vector_product(a);
  let shifted = ∑ x in a, (α*x+α);
  let square = ∑ x in a, x*x;
  return (zipped,named,products,native,shifted,square);
}
protocol Run roles(P)(a:Vector<F>@P,b:Vector<F>@P,ignored:Vector<F>@P,α:F@P)
    -> (result:(F,F,F,F,F,F)@P) { return work(a,b,ignored,α); }
run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''.replace('FINITE', FINITE)


def subdirectory(directory, name):
    result = directory / name
    result.mkdir()
    return result


@pytest.mark.parametrize('flags', OPTIONS)
@pytest.mark.parametrize('field,modulus', FIELDS)
def test_prime_reductions_values_empty_and_all_zip_guards(
    toolchain, journal, directory, flags, field, modulus,
):
    entry = Entry(toolchain, journal, directory, SOURCE.replace('FIELD', field), flags)
    rng = random.Random(7951)
    def scalar(x):
        return decimal_values(x)
    def vector(xs):
        return decimal_values(xs)
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
                                   'α': scalar(1)}, refuses='entry-host-run-failed')
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
        inputs = {'a': decimal_values(a), 'b': decimal_values(b),
                  'ignored': decimal_values([ONE]*n), 'α': decimal_values(α)}
        assert entry.run(f'rows-{n}', inputs)['result'] == [decimal_values(x) for x in expected]
    refused = entry.run('ignored-empty', {'a': decimal_values([]), 'b': decimal_values([]),
                        'ignored': decimal_values([ONE]), 'α': decimal_values(ONE)},
                        refuses='entry-host-run-failed')
    assert 'rejected:require' in json.dumps(refused)


@pytest.mark.parametrize('flags', OPTIONS[:2])
def test_collections_execute_once_in_written_order(toolchain, journal, directory, flags):
    source = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
FINITE
fn fill(x:F,n:index)->Vector<F>=primitive("vector.fill");
fn work(n:index)->(F,index){
  let mut state:index=0;
  let result=sum(zip(
      {state=state+1; fill(2,n)}, {state=state*10+3; fill(5,n)}),fn((x,y))=>x*y);
  return(result,state);
}
protocol Run roles(P)(n:index@P)->(result:(F,index)@P){return work(n);}
run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source.replace('FINITE', FINITE), flags)
    for n in (0, 3):
        assert entry.run(f'rows-{n}', {'n': n})['result'] == [decimal_values(10*n), '13']


@pytest.mark.parametrize('flags', OPTIONS[:2])
def test_custom_reducer_keeps_its_stop(toolchain, journal, directory, flags):
    source = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
fn length(v:Vector<F>)->index=primitive("vector.length");
fn sum(v:Vector<F>)->F=primitive("vector.sum");
fn nonempty(v:Vector<F>)->F{require !(length(v)==0);return sum(v);}
domain fn zip<A:Type+Copy+Drop,B:Type+Copy+Drop>(a:domain<A>,b:domain<B>)->domain<(A,B)>=domain("zip");
fn collect<I:Type+Copy+Drop,E:Field>(rows:domain<I>,term:fn(item:I)->E effects(stop) where item_from(item, rows))->Vector<E> effects(stop)=finite("local.collect.vector");
fn work(a:Vector<F>,b:Vector<F>)->F{let terms=collect(zip(a,b),fn((x,y))=>x*y);return nonempty(terms);}
protocol Run roles(P)(a:Vector<F>@P,b:Vector<F>@P)->(result:F@P){return work(a,b);}
run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source.replace('FINITE', FINITE), flags)
    assert entry.run('nonempty', {'a': decimal_values([2, 3]),
                                 'b': decimal_values([5, 7])})['result'] == decimal_values(31)
    refused = entry.run('empty', {'a': decimal_values([]), 'b': decimal_values([])},
                        refuses='entry-host-run-failed')
    after = joint_execution(refused)['roles'][0]['after']
    assert after[0] == 'stopped' and after[1]['cause'][0] == 'explicit'


@pytest.mark.parametrize('flags', OPTIONS)
def test_published_finite_reductions_project(toolchain, journal, directory, flags):
    package = directory / 'reductions.zkpkg'
    built = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                          f'--project={ROOT}/common/tests/fixtures/projects/finite-reductions/zkc.toml',
                          'example::Demo', f'--output={package}', *flags])
    request = input_files(journal, 'input.json', session='reductions',
        package=package, arguments={'inputs': {'P': {'left': decimal_values([2, 3]),
            'right': decimal_values([5, 7]), 'α': decimal_values(2)}}})
    outputs = directory / 'outputs.json'
    result = journal.json([toolchain.runtime, '--json', 'run', f'--package={package}',
                           f'--sha256={built["package_sha256"]}', *request,
                           f'--results={outputs}'])
    assert result['status'] == 'executed'
    assert json.loads(outputs.read_text())['value']['P'] == {
        'symbolic': decimal_values(31), 'named': decimal_values(31),
        'dot': decimal_values(31), 'product': decimal_values(20)}
    assert json.loads(package.read_text())['options']['fuse_vector_reductions'] == \
        ('--fuse-vector-reductions' in flags)
    assert built['options'] == json.loads(package.read_text())['options']
    source = [f'--compiler={toolchain.compiler}',
              f'--project={ROOT}/common/tests/fixtures/projects/finite-reductions/zkc.toml', *flags]
    checked = journal.json([toolchain.runtime, '--json', 'inputs', 'check',
                            '--operation=run', *source, *request])
    assert checked['status'] == 'inputs-checked'
    direct_outputs = directory / 'direct.outputs.json'
    direct = journal.json([toolchain.runtime, '--json', 'run', *source, *request,
                           f'--results={direct_outputs}'])
    assert direct['status'] == 'executed'
    assert direct['package_sha256'] == checked['package_sha256'] == built['package_sha256']
    assert direct['options'] == built['options']
    assert json.loads(direct_outputs.read_text()) == json.loads(outputs.read_text())


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
run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''


def run_report(entry, name, inputs, capacity=None, refuses=None):
    request = input_files(entry.journal, f'{name}.inputs.json', session='reduction_resources',
                          package=entry.package, arguments={'inputs': {'P': inputs}})
    output = entry.directory / f'{name}.outputs.json'
    command = [entry.tools.runtime, '--json', 'run', f'--package={entry.package}',
               f'--sha256={entry.pin}', *request,
               f'--results={output}']
    if capacity:
        command.append(f'--capacity={capacity}')
    result = entry.journal.json(command, refuses=refuses)
    if refuses:
        assert not output.exists()
    return result


BINDER_SUM = MAP_SUM.replace(
    'fn sum(v:Vector<F>)->F=primitive("vector.sum");', FINITE).replace(
    'let mapped=map times(each a,each b,each unused);\n  return sum(mapped);',
    'return ∑ ((x,y),_) in zip(zip(a,b),unused),x*y;')


def test_pointwise_sum_has_checked_bulk_and_ordered_resource_choices(
    toolchain, journal, directory,
):
    source = BINDER_SUM.replace('unused),x*y;', 'unused),(x*x+y);')
    entries = {name: Entry(toolchain, journal, subdirectory(directory, name), source, flags)
               for name, flags in [('bulk', []), ('ordered', ['--no-finite-bulk'])]}
    n = 1024
    inputs = {'a': decimal_values([2]*n), 'b': decimal_values([3]*n),
              'unused': decimal_values([7]*n)}
    usage = {}
    for name, entry in entries.items():
        report = run_report(entry, f'{name}-usage', inputs)
        usage[name] = joint_execution(report)['roles'][0]['usage']
        assert entry.run(f'{name}-value', inputs)['result'] == str(7*n)
    assert usage['bulk']['iterations'] == 0
    assert usage['ordered']['iterations'] == n
    assert usage['bulk']['instructions'] < usage['ordered']['instructions']
    journal.write('pointwise-resource-ledgers.json', usage)
    ceiling = (usage['bulk']['instructions'] + usage['ordered']['instructions']) // 2
    capacity = journal.write('between-instruction-charges.json', [
        'zkc.native-capacity/0', '65536', '4096', '16777216', '67108864',
        [str(ceiling), '100000', '4294967296'], ['67108864', '268435456']])
    assert run_report(entries['bulk'], 'limited-bulk', inputs, capacity)['status'] == 'executed'
    refused = run_report(entries['ordered'], 'limited-ordered', inputs, capacity,
                         refuses='entry-host-run-failed')
    assert joint_execution(refused)['roles'][0]['after'][1]['cause'] == ['limit']


@pytest.mark.parametrize('extra', [[], ['--no-simplify'], ['--release-storage']])
def test_fusion_preserves_values_and_guards_with_different_resource_charges(
    toolchain, journal, directory, extra,
):
    # Repeat the same computation so the allocation gap exceeds the separate
    # input-loading charge on the original three vectors.
    repetitions = 8
    source = MAP_SUM.replace('return work(a,b,unused);',
                            'return ' + '+'.join(['work(a,b,unused)'] * repetitions) + ';')
    entries = {name: Entry(toolchain, journal, subdirectory(directory, name), source,
                           [*extra, *flags])
               for name, flags in [('baseline', []), ('fused', ['--fuse-vector-reductions'])]}
    n = 1024
    inputs = {'a': decimal_values([2]*n), 'b': decimal_values([3]*n),
              'unused': decimal_values([7]*n)}
    usage, outer_allocations = {}, {}
    for name, entry in entries.items():
        report = run_report(entry, f'{name}-usage', inputs)
        assert report['status'] == 'executed'
        usage[name] = joint_execution(report)['roles'][0]['usage']
        outer_allocations[name] = report['execution']['usage']['fresh_bytes']
        assert entry.run(f'{name}-value', inputs)['result'] == decimal_values(6*n*repetitions)
        for case, changed in [('ignored', {'unused': decimal_values([7])}),
                               ('used', {'b': decimal_values([])})]:
            refused = entry.run(f'{name}-{case}', inputs | changed,
                                refuses='entry-host-run-failed')
            assert 'rejected:require' in json.dumps(refused)
    baseline, fused = usage['baseline'], usage['fused']
    # Separate ledgers: fewer instructions and cumulative allocations in this
    # fixed case do not imply identical exhaustion or lower peak live storage.
    assert fused['instructions'] < baseline['instructions']
    assert fused['logical_bytes'] < baseline['logical_bytes']
    assert fused['total_value_bytes'] < baseline['total_value_bytes']
    assert all(isinstance(u['live_value_bytes'], int) for u in usage.values())
    journal.write('measured-resource-ledgers.json', usage)
    # The selected capacity applies to the whole Entry invocation, including
    # Host arguments, context, diagnostics and result products.
    assert outer_allocations['fused'] < outer_allocations['baseline']
    ceiling = (outer_allocations['fused'] + outer_allocations['baseline']) // 2
    capacity = journal.write('between-allocation-charges.json', [
        'zkc.native-capacity/0', '65536', '4096', '16777216', '67108864',
        ['1000000', '100000', '4294967296'], ['67108864', str(ceiling)]])
    assert run_report(entries['fused'], 'limited-fused', inputs, capacity)['status'] == 'executed'
    refused = run_report(entries['baseline'], 'limited-baseline', inputs, capacity,
                         refuses='entry-host-run-failed')
    after = joint_execution(refused)['roles'][0]['after']
    assert after[0] == 'stopped'
    cause = after[1]['cause']
    assert cause == ['limit'] or (
        cause[0] == 'backend' and 'exhausted:output-bytes' in cause[1]['text']), cause


PROOF = '''module sample;
domain F=field("bls12-381.fr");
type Vector<E:Field>=builtin("vector",E);
fn sum(v:Vector<F>)->F=primitive("vector.sum");
math fn times(x:F,y:F)->F{return x*y;}
fn weighted(a:Vector<F>,b:Vector<F>)->F{
  return sum(map times(each a,each b));
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
run Interactive(inputs: Check::Inputs) { return Check::run(inputs); }
'''


def test_fusion_proof_construction_preserves_protocol_origins(toolchain, journal, directory):
    descriptors, wire_sites, candidates = [], [], []
    for name, flags in [('baseline', []), ('fused', ['--fuse-vector-reductions'])]:
        entry = Entry(toolchain, journal, subdirectory(directory, name), PROOF, flags)
        package = json.loads(entry.package.read_text())
        deployment = json.loads(package['artifact'])
        assert deployment[7] == ['true', 'false', 'true' if flags else 'false', 'true', 'false', 'true']
        descriptors.append(deployment[2])
        wire_sites.append(deployment[8])
        candidates.append(deployment[4:6])
        original = entry.directory / 'original.mlir'
        original.write_text(journal.run([
            toolchain.compiler, 'language-emit', '--source-format=zkc',
            f'--module=sample={entry.directory / "kernels.zkc"}', '--entry=sample::Demo']))
        policy = journal.write(f'{name}.policy.json', deployment[2][1])
        candidate = entry.directory / 'candidate.mlir'
        candidate.write_text(journal.run([
            toolchain.compiler, 'protocol-construct-proof', original, policy, *flags]))
        # Projection retains the map and its policy; physical selection owns
        # the concrete dot or map realization. Check both boundaries.
        projected = candidate.read_text()
        assert 'algebra.map_realize' in projected
        assert 'algebra.exec.vector_dot' not in projected
        assert f'policy = [true, {str(bool(flags)).lower()}, false]' in projected
        sites = operation_sites(json.loads(deployment[4]))
        assert bool(sites['vector.dot']) == bool(flags), sites
        assert bool(sites['numerical.map']) != bool(flags), sites
        journal.run([toolchain.compiler, 'protocol-check-proof', original, policy,
                     candidate, *flags])
        journal.run([toolchain.compiler, 'protocol-check-proof', original, policy,
                     candidate, *([] if flags else ['--fuse-vector-reductions'])],
                    refuses='native-proof-correspondence')
        request = input_files(journal, f'{name}.proof-inputs.json',
                              public={'a': [2, 3], 'b': [5, 7]})
        proof = entry.directory / 'proof.bin'
        journal.json([toolchain.runtime, '--json', 'prove', f'--package={entry.package}',
                      f'--sha256={entry.pin}', *request, f'--output={proof}'])
        verified = journal.json([toolchain.runtime, '--json', 'verify', f'--package={entry.package}',
                                f'--sha256={entry.pin}', *request, f'--proof={proof}'])
        assert verified['status'] == 'accepted' and verified['binding_scope'] == 'transcript'
        source = [f'--compiler={toolchain.compiler}',
                  f'--module=sample={entry.directory / "kernels.zkc"}', *flags]
        direct_proof = entry.directory / 'direct.proof.bin'
        produced = journal.json([toolchain.runtime, '--json', 'prove', *source, *request,
                                 f'--output={direct_proof}'])
        accepted = journal.json([toolchain.runtime, '--json', 'verify', *source, *request,
                                 f'--proof={direct_proof}'])
        assert produced['status'] == 'produced' and accepted['status'] == 'accepted'
        assert produced['package_sha256'] == accepted['package_sha256'] == entry.pin
        assert produced['options']['fuse_vector_reductions'] == bool(flags)
        truncated = entry.directory / 'truncated.bin'
        truncated.write_bytes(proof.read_bytes()[:-1])
        journal.json([toolchain.runtime, '--json', 'verify', f'--package={entry.package}',
                     f'--sha256={entry.pin}', *request, f'--proof={truncated}'],
                     refuses='proof-truncated')
    assert descriptors[0] == descriptors[1]
    assert wire_sites[0] == wire_sites[1]
    assert candidates[0] != candidates[1]


@pytest.mark.parametrize('bulk', [False, True])
@pytest.mark.parametrize('simplify', [False, True])
def test_finite_proof_policy_reconstructs_actual_candidate(
    toolchain, journal, directory, bulk, simplify,
):
    source = PROOF.replace('fn sum(v:Vector<F>)->F=primitive("vector.sum");', FINITE)
    source = source.replace('return sum(map times(each a,each b));',
                            'return ∑ (x,y) in zip(a,b), x*y;')
    selection = [] if bulk else ['--no-finite-bulk']
    flags = selection + ([] if simplify else ['--no-simplify'])
    entry = Entry(toolchain, journal, directory, source, flags)
    package = json.loads(entry.package.read_text())
    assert package['options'] == {'simplify': simplify, 'release_storage': False,
                                  'fuse_vector_reductions': False, 'finite_bulk': bulk,
                                  'fuse_collect_fold': False, 'calculation_batching': True}
    deployment = json.loads(package['artifact'])
    assert deployment[7] == [str(simplify).lower(), 'false', 'false', str(bulk).lower(), 'false', 'true']
    original = directory / 'original.mlir'
    original.write_text(package['original'])
    policy = journal.write('policy.json', deployment[2][1])
    candidate = directory / 'candidate.mlir'
    candidate.write_text(journal.run([
        toolchain.compiler, 'protocol-construct-proof', original, policy, *selection]))
    assert ('algebra.exec.vector_dot' in candidate.read_text()) == bulk
    journal.run([toolchain.compiler, 'protocol-check-proof', original, policy,
                 candidate, *selection])
    journal.run([toolchain.compiler, 'protocol-check-proof', original, policy,
                 candidate, *(['--no-finite-bulk'] if bulk else [])],
                refuses='native-proof-correspondence')
    request = input_files(journal, 'inputs.json', public={'a': [2, 3], 'b': [5, 7]})
    proof = directory / 'proof.bin'
    journal.json([toolchain.runtime, '--json', 'prove', f'--package={entry.package}',
                  f'--sha256={entry.pin}', *request, f'--output={proof}'])
    accepted = journal.json([toolchain.runtime, '--json', 'verify', f'--package={entry.package}',
                            f'--sha256={entry.pin}', *request, f'--proof={proof}'])
    assert accepted['status'] == 'accepted'


@pytest.mark.parametrize('flag', ['--fuse-vector-reductions', '--no-finite-bulk'])
def test_mathematical_flag_requires_source_compilation(toolchain, journal, directory, flag):
    source = directory / 'sample.zkc'
    source.write_text(MAP_SUM)
    journal.run([toolchain.compiler, 'language-check', '--source-format=zkc',
                 f'--module=sample={source}', flag], refuses='source.options')
    journal.json([toolchain.runtime, '--json', 'check', f'--compiler={toolchain.compiler}',
                  f'--module=sample={source}', flag], refuses='cli-option')
    for operation in ('run', 'prove', 'verify', 'bindings', 'inputs check'):
        refused = journal.json([toolchain.runtime, '--json', *operation.split(),
                                '--package=missing.zkpkg', f'--sha256={"0" * 64}',
                                flag], refuses='cli-usage')
        assert refused['phase'] == 'arguments'


@pytest.mark.parametrize('flags', OPTIONS[:2])
def test_binder_and_body_shadowing_keep_outer_values(toolchain, journal, directory, flags):
    source = '''module sample;
domain F=field("koala-bear");
type Vector<E:Field>=builtin("vector",E);
FINITE
fn work(a:Vector<F>,x:F,α:F)->(F,F){
  let total=∑ x in a,{let x=x+1;x*α};
  return(total,x);
}
protocol Run roles(P)(a:Vector<F>@P,x:F@P,α:F@P)->(result:(F,F)@P){return work(a,x,α);}
run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source.replace('FINITE', FINITE), flags)
    assert entry.run('shadowed', {'a': decimal_values([2, 3]), 'x': decimal_values(77),
                                 'α': decimal_values(5)})['result'] == [
                                     decimal_values(35), decimal_values(77)]


def test_registered_participant_pipeline_forwards_fusion(toolchain, journal, directory):
    source = directory / 'source.zkc'
    source.write_text(MAP_SUM)
    original = directory / 'original.mlir'
    package = journal.json([
        toolchain.compiler, 'language-package', '--source-format=zkc',
        f'--module=sample={source}', '--entry=sample::Demo'])
    original.write_text(joint_package(package)['original'])
    for fuse in (False, True):
        choice = 'true' if fuse else 'false'
        projected = journal.run([
            toolchain.optimizer, original,
            f'--zkc-participant-pipeline=project-only=true fuse-vector-reductions={choice}'])
        assert 'algebra.map_realize' in projected
        assert 'algebra.exec.vector_dot' not in projected
        assert f'policy = [true, {choice}, false]' in projected
        physical = journal.run([
            toolchain.optimizer, original,
            f'--zkc-participant-pipeline=fuse-vector-reductions={choice}'])
        physical_file = directory / f'physical-{choice}.mlir'
        physical_file.write_text(physical)
        sites = operation_sites(journal.json([
            toolchain.compiler, 'protocol-export', physical_file]))
        assert bool(sites['vector.dot']) == fuse, sites
        assert bool(sites['numerical.map']) != fuse, sites
