"""The same maintained physical pass selects both module contractions."""
import copy
import json
from pathlib import Path
from cases import case
from commands import Commands
from tools import corpus, optimizer, records

root = Path(__file__).resolve().parents[2]
source = (corpus / "linear-contractions.pir").read_text()


commands = Commands(records())


def run(mode, value, *options, refuses=None, selected=None):
    """`selected` names the physical implementation the choice must report."""
    printed = commands.source(mode, value, *options, refuses=refuses)
    if selected is not None:
        assert f'selected={selected}\n' in commands.last.stderr, commands.last.stderr
    return printed


def plan(value=source, selected=2):
    return json.loads(run('protocol-compile', value, '--linear-contractions', selected=selected))


def bindings(p):
    return {b[0]: b for b in p[1]}


def functions(p):
    return {f[1]: f for f in p[3]}


def logical_bodies(p):
    table = bindings(p)
    result = []
    for f in p[3]:
        body = copy.deepcopy(f[4])
        for op in body[:-1]:
            op[2] = table[op[2]][1]
        result.append((f[1], body))
    return result


dense = json.loads(run('protocol-compile', source))
optimized = plan()
assert logical_bodies(dense) == logical_bodies(optimized)
assert dense[4:] == optimized[4:]  # All role actions, cuts and protocol sites.
assert not any('-diagonal/' in b[3] for b in dense[1])
assert len(optimized[1]) == len(dense[1])+4
selected_impls = {b[3] for b in optimized[1] if '-diagonal/' in b[3]}
assert selected_impls == {'arkworks-diagonal/vector.mul', 'arkworks-diagonal/vector.dot',
                          'dalek-diagonal/curve.scale_each', 'dalek-diagonal/curve.msm'}
assert bindings(optimized)['mul'][3] == 'arkworks/vector.mul'
assert functions(optimized)['Dense'] == functions(dense)['Dense']

# Helpers are retained in common MLIR, then expanded before the shared planner.
# This joins the new composition boundary to both existing contraction families;
# outlining a producer and its consumer must not hide their eligible use edge.
nested = json.loads(run('protocol-source', source))
for fn in nested[2][:2]:
    producer, consumer = copy.deepcopy(fn[4][:2])
    map_name, contract_name = fn[1] + 'Map', fn[1] + 'Contract'
    mapped_type = fn[2][2][1]
    nested[2].extend([
        ['function', map_name, copy.deepcopy(fn[2][1:]), [mapped_type],
         [producer, ['return', ['mapped']]], [map_name, []]],
        ['function', contract_name, [copy.deepcopy(fn[2][0]), ['mapped', mapped_type]],
         copy.deepcopy(fn[3]), [consumer, ['return', ['result']]], [contract_name, []]],
    ])
    fn[4][:2] = [
        ['apply', 'map', map_name, [], ['factors', 'values'], ['mapped']],
        ['apply', 'contract', contract_name, [], ['w', 'mapped'], ['result']],
    ]
nested_text = json.dumps(nested)
assert run('protocol-import', nested_text).count('call @') == 4
nested_dense = json.loads(run('protocol-compile', nested_text))
nested_optimized = plan(nested_text)
assert logical_bodies(nested_dense) == logical_bodies(nested_optimized)
assert nested_dense[4:] == nested_optimized[4:]
assert {b[3] for b in nested_optimized[1] if '-diagonal/' in b[3]} == selected_impls
assert not any(i[0] == 'apply' for f in nested_optimized[3] for i in f[4])
assert all(i[1].startswith('lc_') for f in nested_optimized[3][:2]
           for i in f[4] if i[0] == 'op')

ir = run('protocol-physical-ir', source, '--linear-contractions', '--locations', selected=2)
assert 'arkworks.fr-diagonal/1' in ir and 'dalek.ristretto-diagonal/1' in ir
assert json.loads(run('protocol-export', ir)) == optimized

# Pass-manager option and the CLI invoke the same planner and produce the same
# inspected artifact. Statistics are available through standard MLIR reporting.
logical_ir = run('protocol-import', source)
planned = commands.run([optimizer, '--zkc-project-participants',
                        '--zkc-plan-participants=linear-contractions=true',
                        '--verify-each', '--mlir-pass-statistics'], stdin=logical_ir)
assert 'linear-contractions: producers=3 eligible=2 selected=2' in commands.last.stderr, \
    commands.last.stderr
assert json.loads(run('protocol-export', planned)) == optimized

# A wrong operand role or an escape leaves the entire producer dense.
# Values are ordered: the pass must not exploit commutativity to swap dot inputs.
for before, after in [
    ('[contract] let result = dot(w, mapped);', '[contract] let result = dot(mapped, w);'),
    ('[contract] let result = dot(w, mapped);', '[contract] let result = dot(mapped, mapped);'),
]:
    assert before in source, before
    changed = source.replace(before, after)
    p = plan(changed, 1)
    assert not any(b[3].startswith('arkworks-diagonal/') for b in p[1])

# One shared map feeds both contractions; three fresh bindings, not two copies
# of the producer or a partial optimization of just one consumer.
shared = source.replace('[contract] let result = dot(w, mapped);',
    '[other] let unused = dot(w, mapped);\n    [contract] let result = dot(w, mapped);')
shared_plan = plan(shared, 3)
assert len(shared_plan[1]) == len(dense[1]) + 5
shared_body = functions(shared_plan)['Dot'][4]
assert [bindings(shared_plan)[op[2]][3] for op in shared_body[:-1]] == [
    'arkworks-diagonal/vector.mul', 'arkworks-diagonal/vector.dot',
    'arkworks-diagonal/vector.dot']
assert len({op[2] for op in shared_body[:-1]}) == 3
assert logical_bodies(json.loads(run('protocol-compile', shared))) == logical_bodies(shared_plan)
assert plan(shared, 3) == shared_plan  # deterministic source-order clone naming

# The independently installed group contraction has the same sharing rule.
both_shared = shared.replace('[contract] let result = msm(w, mapped);',
    '[other] let unused = msm(w, mapped);\n    [contract] let result = msm(w, mapped);')
p = plan(both_shared, 4)
assert len(p[1]) == len(dense[1]) + 6
assert [bindings(p)[op[2]][3] for op in functions(p)['MSM'][4][:-1]] == [
    'dalek-diagonal/curve.scale_each', 'dalek-diagonal/curve.msm', 'dalek-diagonal/curve.msm']
run('protocol-import', json.dumps(p))

# A chain materializes the inner product. Exactly the final depth-one view is
# selected; there is no representation conversion or recursive diagonal backing.
chain = source.replace('[multiply] let mapped = mul(factors, values);',
    '[inner] let backing = mul(factors, values);\n    [multiply] let mapped = mul(factors, backing);', 1)
p = plan(chain)
body = functions(p)['Dot'][4]
assert bindings(p)[body[0][2]][3] == 'arkworks/vector.mul'
assert bindings(p)[body[1][2]][3] == 'arkworks-diagonal/vector.mul'
assert len(body) == 4

# Alternate domains have dense implementations but no reserved diagonal choice.
for value in [source.replace('bls12-381.fr', 'ristretto255.scalar'),
              source.replace('ristretto255.scalar', 'bls12-381.fr')
                    .replace('ristretto255.group', 'bls12-381.g1')]:
    plan(value, 1)

# Explicit per-source-binding selections take precedence. They are not
# overwritten by optimization, including choices used by multiple functions.
d = records()
selection = Path(d)/'choices.json'
selection.write_text(json.dumps([['mul', 'arkworks/vector.mul']]))
p = json.loads(run('protocol-compile', source, '--linear-contractions',
                  '--implementations='+str(selection), selected=1))
assert not any(b[3].startswith('arkworks-diagonal/') for b in p[1])
# Concrete syntax for a bound implementation is independently exercised by the
# existing explicit-construction suite; JSON avoids depending on a new spelling.
common = json.loads(run('protocol-source', source))
common[1][0][3] = 'arkworks/vector.mul'
plan(json.dumps(common), 1)

# Hand-authored physical artifacts must obey representation lifetime and exact
# signature constraints, even without using the optimizer.
corrupt = copy.deepcopy(optimized)
corrupt[3][0][2][0][1] = 'vector:bls12-381.fr@arkworks.fr-diagonal/1'
run('protocol-import', json.dumps(corrupt), refuses='binding-representation')
corrupt = copy.deepcopy(optimized)
f = functions(corrupt)['Dot']
f[4].insert(1, copy.deepcopy(f[4][1]))
f[4][1][1] = 'duplicate'
f[4][1][-1] = ['extra']
run('protocol-import', json.dumps(corrupt))  # Immutable sharing is admitted.
corrupt = copy.deepcopy(optimized)
f = functions(corrupt)['Dot']
f[4][1][4] = [f[2][0][0], f[2][1][0]]  # Unused selected producer.
run('protocol-import', json.dumps(corrupt), refuses='binding-operation-signature')
corrupt = copy.deepcopy(optimized)
for b in corrupt[1]:
    if b[3] == 'dalek-diagonal/curve.msm':
        b[3] = 'arkworks-diagonal/curve.msm'
run('protocol-import', json.dumps(corrupt), refuses='binding-implementation')
run('protocol-compile', source, '--linear-contractions', '--linear-contractions', refuses='duplicate-option')
run('protocol-import', source, '--linear-contractions', refuses='unsupported-option')
# Random draws, transcript observations and a potentially rejecting guard can
# lie between producer and contraction. Selection changes neither their sites
# nor their structural order; the diagonal producer retains its own shape check.
common = json.loads(run('protocol-source', source))
cuts = copy.deepcopy(common)
rng = 'rng:bls12-381.fr'
transcript = 'transcript:merlin3.bls12-381.fr64be/1'
cuts[1] += [['draw', 'random.draw', ['bls12-381.fr'], ''],
            ['observe', 'transcript.observe.vector', ['merlin3.bls12-381.fr64be/1',
              'bls12-381.fr', 'zkcv.vector.bls12-381.fr/1'], ''],
            ['require', 'control.require', [], '']]
f = cuts[2][0]
f[2] += [['coins', rng], ['state', transcript], ['allowed', 'bool']]
f[3] += [rng, transcript]
f[4][1:1] = [['op', 'draw', 'draw', [], ['coins'], ['challenge', 'next_coins']],
              ['op', 'observe', 'observe', ['Main', 'message', 'weights', 'P', 'V'],
               ['state', 'w'], ['next_state']],
              ['op', 'guard', 'require', [], ['allowed'], []]]
f[4][-1][1] += ['next_coins', 'next_state']
protocol = cuts[3][0]
protocol[4] += [['coins', 'P', rng], ['state', 'P', transcript], ['allowed', 'P', 'bool']]
protocol[5] += [['P', rng], ['P', transcript]]
protocol[7][0][4] += ['coins', 'state', 'allowed']
protocol[7][0][5] += ['next_coins', 'next_state']
protocol[7][-1][1] += ['next_coins', 'next_state']
dense_cuts = json.loads(run('protocol-compile', json.dumps(cuts)))
opt_cuts = plan(json.dumps(cuts))
assert logical_bodies(dense_cuts) == logical_bodies(opt_cuts)
assert [op[1] for op in functions(opt_cuts)['Dot'][4][:-1]] == [
    'multiply', 'draw', 'observe', 'guard', 'contract']
assert dense_cuts[4:] == opt_cuts[4:]

# No pair can be synthesized across a function return, a protocol loop or a
# message between roles. Generic projection needs no field/group cases.
for escape in ['loop', 'message']:
    escaped = copy.deepcopy(common)
    f = escaped[2][0]
    f[2] = [f[2][0], f[2][2]]
    f[4] = [['op', 'contract', 'dot', [], ['w', 'values'], ['result']],
            ['return', ['result']]]
    protocol = escaped[3][0]
    if escape == 'loop':
        prefix = [['loop', 'rounds', ['constant', '2'], [['carried', 'v']], ['a'],
                   [['local', 'make', 'P', 'Dense', ['a', 'carried'], ['next']],
                    ['yield', ['next']]], ['received']]]
    else:
        prefix = [['local', 'make', 'P', 'Dense', ['a', 'v'], ['sent']],
                  ['message', 'wire', 'vector', 'P', 'V', 'sent', 'received']]
        protocol[4][0][1] = 'V'
        protocol[5][0][0] = 'V'
        protocol[7][0][2] = 'V'
    protocol[7][0][4] = ['w', 'received']
    protocol[7][:0] = prefix
    escaped_plan = plan(json.dumps(escaped), 1)
    assert not any(b[3].startswith('arkworks-diagonal/') for b in escaped_plan[1])
    assert json.loads(run('protocol-compile', json.dumps(escaped)))[4:] == escaped_plan[4:]

# Known kernels can lack either optional interface and still compile densely.
unsupported = copy.deepcopy(common)
unsupported[1][0][1] = 'vector.add'
plan(json.dumps(unsupported), 1)
unsupported = copy.deepcopy(common)
unsupported[1].append(['sum', 'vector.sum', ['bls12-381.fr'], ''])
unsupported[2][0][4][1][2] = 'sum'
unsupported[2][0][4][1][4] = ['mapped']
plan(json.dumps(unsupported), 1)

# The opt-in choice stays dense if fresh operation bindings would exceed the
# existing declaration budget. Optional selection does not invalidate this input.
crowded = copy.deepcopy(common)
crowded[1] += [[f'unused_{i}', 'vector.sum', ['bls12-381.fr'], ''] for i in range(4091)]
crowded_plan = plan(json.dumps(crowded), 0)
assert len(crowded_plan[1]) == 4095

# Fixing only one consumer prevents selection of its shared producer and the
# other consumer. Explicit physical choices are authoritative as a group.
shared_common = json.loads(run('protocol-source', shared))
shared_common[1].append(['fixed_dot', 'vector.dot', ['bls12-381.fr'], 'arkworks/vector.dot'])
shared_common[2][0][4][2][2] = 'fixed_dot'
fixed_plan = plan(json.dumps(shared_common), 1)
assert not any(b[3].startswith('arkworks-diagonal/') for b in fixed_plan[1])

# Budget boundary for a two-consumer group. With two slots left it stays dense;
# the independent MSM pair can still use those two slots. With three slots left
# the whole shared group fits, and the later MSM stays dense.
for used, selected, field_selected in [(4094, 1, False), (4093, 2, True)]:
    crowded = json.loads(run('protocol-source', shared))
    crowded[1] += [[f'crowd_{i}', 'vector.sum', ['bls12-381.fr'], '']
                   for i in range(used-len(crowded[1]))]
    p = plan(json.dumps(crowded), selected)
    assert len(p[1]) == 4096
    assert any(b[3].startswith('arkworks-diagonal/') for b in p[1]) == field_selected

# Fresh symbols cannot collide with unrelated user binding/function symbols.
collision = shared.replace('bind mul =', 'bind diagonal_0 = vector::sum(bls12-381.fr);\n  bind mul =')
collision = collision.replace('fn Dense(', 'fn diagonal_1(').replace('= Dense(', '= diagonal_1(')
p = plan(collision, 3)
assert bindings(p)['diagonal_0'][3] == 'arkworks/vector.sum'
assert 'diagonal_1' in functions(p)
assert len({b[0] for b in p[1]}) == len(p[1])

# Independently authored partial/nested/wrong-role physical selections refuse.
for mutation in ['partial', 'coefficients', 'nested', 'return', 'unused']:
    with case(f"{mutation} plan mutation is refused"):
        corrupt = copy.deepcopy(shared_plan)
        f = functions(corrupt)['Dot']
        if mutation == 'partial':
            f[4][2][2] = 'dot'  # dense signature cannot consume the selected view
        elif mutation == 'coefficients':
            f[4][2][4] = list(reversed(f[4][2][4]))
        elif mutation == 'nested':
            extra = copy.deepcopy(f[4][0])
            extra[1], extra[4][1], extra[5] = 'nested', f[4][0][5][0], ['nested_result']
            f[4].insert(1, extra)
        elif mutation == 'return':
            f[4][-1][1] = [f[4][0][5][0]]
        else:
            f[4] = [f[4][0], ['return', []]]
            f[3] = []
            # Run physical admission on a local-only change with coherent caller.
            # Signature/caller validation may refuse first; no unused view can admit.
        run('protocol-import', json.dumps(corrupt),
            refuses='function-return-types' if mutation == 'return' else 'binding-operation-signature')

print(f'linear contractions: {commands.save()} pipeline checks; both domains, shared bindings, escapes, depth one')
