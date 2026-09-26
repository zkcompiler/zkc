"""Construction suites and whole-call origins through the current C++ pipeline.

Structural/candidate checks only; no native arithmetic or proof execution claim.
"""
import copy
import json
from pathlib import Path
from commands import Commands
from tools import examples, records



commands = Commands(records())


def run(mode, value, *args, refuses=None):
    """A source given as text or as the record it serializes to."""
    printed = commands.source(mode, value if isinstance(value, str) else json.dumps(value),
                              *args, refuses=refuses)
    if refuses:
        assert commands.last.returncode == 1, commands.last.stderr
        return None
    return json.loads(printed) if printed.startswith('[') else printed.strip()


def fixture(field='bls12-381.fr'):
    v, f, r = ('vector:' + field, 'field:' + field, 'rng:' + field)
    bindings = [[name, contract, [] if contract == 'control.require' else [field], '']
                for name, contract in [('mul', 'vector.mul'), ('dot', 'vector.dot'),
                    ('draw', 'random.draw'), ('equal', 'field.equal'),
                    ('require', 'control.require'), ('constant', 'field.constant')]]
    def fn(name, args, results, body):
        return ['function', name, args, results, body, [name, []]]
    functions = [
        fn('Shared', [['w', v], ['a', v], ['b', v], ['allowed', 'bool']], [f], [
            ['op', 'multiply', 'mul', [], ['a', 'b'], ['product']],
            ['op', 'guard', 'require', [], ['allowed'], []],
            ['op', 'first', 'dot', [], ['w', 'product'], ['one']],
            ['op', 'second', 'dot', [], ['w', 'product'], ['two']],
            ['return', ['two']]]),
        fn('Draw', [['rng', r]], [f, r], [
            ['op', 'sample', 'draw', [], ['rng'], ['challenge', 'after']],
            ['return', ['challenge', 'after']]]),
        fn('Check', [['x', f]], ['bool'], [
            ['op', 'equal', 'equal', [], ['x', 'x'], ['ok']],
            ['op', 'guard', 'require', [], ['ok'], []], ['return', ['ok']]])]
    protocol = ['protocol', 'Main', ['P', 'V'], [],
        [['w', 'P', v], ['a', 'P', v], ['b', 'P', v], ['allowed', 'P', 'bool'], ['coins', 'V', r]],
        [['V', 'bool'], ['V', r]], [], [
            ['local', 'compute', 'P', 'Shared', ['w', 'a', 'b', 'allowed'], ['answer']],
            ['message', 'answer', 'answer', 'P', 'V', 'answer', 'received'],
            ['local', 'sample', 'V', 'Draw', ['coins'], ['challenge', 'after']],
            ['message', 'challenge', 'challenge', 'V', 'P', 'challenge', 'seen'],
            ['local', 'check', 'V', 'Check', ['received'], ['ok']],
            ['return', ['ok', 'after']]]]
    source = ['zkc.protocol/1', bindings, functions, [protocol],
              [['instance', 'main_instance', 'Main', [], [], [['P', 'P'], ['V', 'V']]]],
              [['entry', 'main', 'main_instance']]]
    suite = ('merlin3.bls12-381.fr64be/1' if field == 'bls12-381.fr' else
             'merlin3.ristretto255.scalar64le/1')
    return source, ['zkc.construction/1', 'main', 'P', 'V', [], ['coins', [['Draw', 'sample']]], '0', suite, 'exact']


def walk(body):
    for ins in body:
        yield ins
        if ins[0] == 'loop':
            yield from walk(ins[5])


def reached_local_calls(common):
    instances = {i[1]: i for i in common[4]}
    protocols = {p[1]: p for p in common[3]}
    visited, calls = set(), []
    def visit(name):
        if name in visited:
            return
        visited.add(name)
        inst = instances[name]
        def visit_body(body):
            for op in body:
                if op[0] == 'local':
                    calls.append(op)
                elif op[0] == 'call':
                    visit(dict(inst[4])[op[2]])
                elif op[0] == 'loop':
                    count = op[2][1] if op[2][0] == 'constant' else dict(inst[3])[op[2][1]]
                    if int(count):
                        visit_body(op[5])
        visit_body(protocols[inst[2]][7])
    for entry in common[5]:
        visit(entry[2])
    return calls


d = records()
d = Path(d)
descriptor_path, candidate = d/'descriptor.json', d/'candidate.json'
for field in ['bls12-381.fr', 'ristretto255.scalar']:
    source, descriptor = fixture(field)
    for identity in ['exact', 'normalized']:
        descriptor[8] = identity
        descriptor_path.write_text(json.dumps(descriptor))
        result = run('protocol-construct', source, descriptor_path)
        common = result[2]
        functions = {f[1]: f for f in common[2]}
        origins = {(row[0], row[1]): row for row in result[4]}
        assert len(origins) == len(result[4])
        calls = reached_local_calls(common)
        preserved = [functions[c[3]] for c in calls
                     if len(functions[c[3]][4]) == 5]
        assert len(preserved) == 1
        local = preserved[0]
        original = functions['Shared']
        assert local[2:5] == original[2:5]  # arguments, results, exact body
        for op in local[4][:-1]:
            row = origins[local[1], op[1]]
            assert row[4:] == ['Shared', op[1], 'P', 'original']
        # All reached generated operations have their own source origin.
        for call in calls:
            for op in functions[call[3]][4][:-1]:
                assert (call[3], op[1]) in origins
        # Selected challenges still use one-operation construction helpers.
        challenge_rows = [row for row in result[4] if row[4] == 'Draw']
        assert len(challenge_rows) == 2
        assert all(row[7] == 'construction' and len(functions[row[0]][4]) == 2
                   for row in challenge_rows)
        # Suite/domain/codec arguments are recomputed, never normalized to BLS.
        for _, contract, args, _ in common[1]:
            if contract.startswith('transcript.'):
                assert args[0] == descriptor[7]
                if contract == 'transcript.observe.field':
                    assert args == [descriptor[7], field, 'zkcv.field.'+field+'/1']
        plan = run('protocol-compile', common, '--linear-contractions')
        physical_functions = {f[1]: f for f in plan[3]}
        bindings = {b[0]: b for b in plan[1]}
        implementations = [bindings[op[2]][3] for op in physical_functions[local[1]][4][:-1]]
        if field == 'bls12-381.fr':
            assert implementations == ['arkworks-diagonal/vector.mul', 'arkworks/control.require',
                                       'arkworks-diagonal/vector.dot', 'arkworks-diagonal/vector.dot']
        else:
            assert not any('-diagonal/' in impl for impl in implementations)
        candidate.write_text(json.dumps(result))
        assert run('protocol-check-construction', source, descriptor_path, candidate) == 'construction-checked'
        # Changing a nonfirst operation/origin cannot escape exact checking.
        for kind in ['missing-origin', 'duplicate-origin', 'wrong-origin', 'drop-guard', 'reorder', 'binding']:
            bad = copy.deepcopy(result)
            target = next(f for f in bad[2][2] if f[1] == local[1])
            row_index = next(i for i, row in enumerate(bad[4])
                             if row[0] == local[1] and row[1] == local[4][2][1])
            if kind == 'missing-origin':
                bad[4].pop(row_index)
            elif kind == 'duplicate-origin':
                bad[4].append(copy.deepcopy(bad[4][row_index]))
            elif kind == 'wrong-origin':
                bad[4][row_index][5] = 'different'
            elif kind == 'drop-guard':
                target[4].pop(1)
            elif kind == 'reorder':
                target[4][1], target[4][2] = target[4][2], target[4][1]
            else:
                target[4][2][2] = 'equal'
            candidate.write_text(json.dumps(bad))
            run('protocol-check-construction', source, descriptor_path, candidate,
                refuses='construction-candidate-mismatch')
    # Wrong field of the selected RNG refuses before using any draw.
    wrong = copy.deepcopy(descriptor)
    wrong[7] = ('merlin3.ristretto255.scalar64le/1' if field == 'bls12-381.fr'
                else 'merlin3.bls12-381.fr64be/1')
    descriptor_path.write_text(json.dumps(wrong))
    run('protocol-construct', source, descriptor_path, refuses='construction-rng-port')
    for suite in ['other', 'merlin3.ristretto255.scalar64be/1', field]:
        wrong[7] = suite
        descriptor_path.write_text(json.dumps(wrong))
        run('protocol-construct', source, descriptor_path, refuses='construction-suite-or-roles')

# Whole-call preservation must not suppress needed validator recipes.
source, descriptor = fixture()
source[3][0][7].insert(-1, ['message', 'accepted', 'accepted', 'V', 'P', 'ok', 'p_ok'])
descriptor_path.write_text(json.dumps(descriptor))
result = run('protocol-construct', source, descriptor_path)
rows = [row for row in result[4] if row[4] == 'Check']
assert {row[7] for row in rows} == {'original', 'recipe'}
functions = {f[1]: f for f in result[2][2]}
assert all(len(functions[row[0]][4]) == 2 for row in rows)
assert not any(row[5] == 'guard' and row[7] == 'recipe' for row in rows)

# Repeated calls to the same source function get distinct per-op maps.
source, descriptor = fixture()
other = copy.deepcopy(source[3][0][7][0])
other[1], other[5] = 'again', ['other_answer']
source[3][0][7].insert(1, other)
result = run('protocol-construct', source, descriptor_path)
rows = [row for row in result[4] if row[4] == 'Shared']
assert len({row[0] for row in rows}) == 2
assert {row[3] for row in rows} == {'compute', 'again'}
assert len({(row[0], row[1]) for row in rows}) == 8

# Selected port has the suite field but the selected draw uses another RNG.
source, descriptor = fixture('ristretto255.scalar')
source[1][2][2] = ['bls12-381.fr']
source[2][1][2][0][1] = 'rng:bls12-381.fr'
source[2][1][3] = ['field:bls12-381.fr', 'rng:bls12-381.fr']
source[3][0][4].append(['other_coins', 'V', 'rng:bls12-381.fr'])
source[3][0][5][1][1] = 'rng:bls12-381.fr'
source[3][0][7][2][4] = ['other_coins']
descriptor_path.write_text(json.dumps(descriptor))
run('protocol-construct', source, descriptor_path, refuses='construction-challenge-field')

# A BLS12-381 RNG port cannot become Ristretto by changing only the suite.
bls_source = json.loads((examples / 'two-factor.json').read_text())
desc = json.loads((examples / 'two-factor.construction.json').read_text())
desc[7] = 'merlin3.ristretto255.scalar64le/1'
descriptor_path.write_text(json.dumps(desc))
run('protocol-construct', bls_source, descriptor_path, refuses='construction-rng-port')

print(f'construction locals: {commands.save()} current-compiler checks; both suites, per-op origins, reached shared pair, hostile manifests')
