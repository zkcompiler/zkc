"""Native callable IR, bounded expansion, admission and construction regressions.

What the independent Lean consumer makes of the same sources and plans is a
separate test, tests/protocol/test_local_algorithms_reference.py, because it needs
another build. The edited sources both of them judge are built in one place,
tests/support/algorithm_variants.py.
"""
from algorithm_variants import cycle, nested, with_identity
import copy
import json
from pathlib import Path
from commands import Commands
from tools import compiler, corpus, optimizer, records

root = Path(__file__).resolve().parents[2]


commands = Commands(records())


def run(tool, *args, refuses=None, text=None):
    return commands.run([tool, *args], stdin=text, refuses=refuses)


def native(mode, value, refuses=None):
    """A source given as text or as the record it serializes to."""
    result = run(compiler, mode, '-', refuses=refuses,
                 text=value if isinstance(value, str) else json.dumps(value))
    return json.loads(result) if not refuses and result.startswith('[') else result


text = (corpus / "local-algorithms.pir").read_text()
source = native('protocol-source', text)
common = native('protocol-import', source)
assert common.count('call @') == 5
assert native('protocol-source', native('protocol-format', text)) == source
assert 'let ' in native('protocol-format', source)
roundtrip = native('protocol-export', common)
assert sum(i[0] == 'apply' for f in roundtrip[2] for i in f[4]) == 5
run(optimizer, '--verify-each', text=common)
native('protocol-source', text.replace('Twice(x);', 'Twice::<koala-bear>(x);'), 'generic-static-arity')
expanded_ir = run(optimizer, '--zkc-expand-algorithms', text=common)
assert 'call @' not in expanded_ir
assert run(optimizer, '--zkc-expand-algorithms', text=expanded_ir) == expanded_ir
expanded = native('protocol-expand', source)
assert native('protocol-export', expanded_ir) == expanded
physical = native('protocol-compile', source)
assert not any(i[0] == 'apply' for f in physical[3] for i in f[4])
origins = native('protocol-algorithm-map', source)
assert origins[:2] == ['zkc.algorithm-expansion/1', 'canonical-expanded-locals/1']
scale = [r for r in origins[2] if r[0] == 'Linear' and r[2] == 'Scale']
assert len(scale) == 2 and scale[0][1] != scale[1][1]
assert scale[0][4] == [['left', 'Scale']] and scale[1][4] == [['right', 'Scale']]
# Forward references and two nested call edges share the same finite contract.
nested_source = nested(source)
nested_plan = native('protocol-compile', nested_source)
nested_origins = native('protocol-algorithm-map', nested_source)
assert any(r[0] == 'Nested' and r[4] == [['inner', 'Linear'], ['left', 'Scale']] for r in nested_origins[2])

# Native transformation changes a callable body before expansion, without
# reparsing authored text. The independent checker rejects the changed candidate.
identity_source = with_identity(source)
changed_ir = native('protocol-import', identity_source).replace('call @Twice', 'call @Identity')
changed_source = native('protocol-export', changed_ir)
changed_plan = native('protocol-compile', changed_source)
assert changed_plan != native('protocol-compile', identity_source)


def mutation(change, error, mode='protocol-source'):
    value = copy.deepcopy(source)
    change(value)
    native(mode, value, error)


mutation(lambda s: s[2][0][4].insert(0, ['apply', 'recursive', 'Twice', [], ['x'], ['q']]), 'interactive-call-cycle')
mutation(lambda s: s[2][0][4].insert(0, ['apply', 'missing', 'Absent', [], ['x'], ['q']]), 'algorithm-call-symbol')
mutation(lambda s: s[2][2][4][0].__setitem__(4, ['g']), 'algorithm-call-signature')
mutation(lambda s: s[2][2][4][0].__setitem__(5, []), 'interactive-shape')
mutation(lambda s: s[2][5][4].insert(1, ['apply', 'again', 'Commit', [], ['bases', 'n'], ['c2', 'n2']]), 'interactive-resource-reuse')
mutation(lambda s: s[2][3][4][-1].__setitem__(1, ['c', 'n']), 'interactive-resource-reuse')
mutation(lambda s: s[3][0][7].insert(0, ['apply', 'bad', 'Twice', [], ['x'], ['t']]), 'algorithm-call-context')
mutation(lambda s: s[2][0].__setitem__(4, 'external'), 'algorithm-call-symbol')
mutation(lambda s: s[2][2][4][0].__setitem__(1, 'a' * 125), 'algorithm-origin-limit', 'protocol-compile')
# The entire DAG is formed, including unused definitions and shared suffixes.
native('protocol-source', cycle(source), 'interactive-call-cycle')
# Empty bodies still consume expansion work; DAG sharing cannot bypass bounds.
large = copy.deepcopy(source)
large[2].append(['function', 'E0', [], [], [['return', []]], ['E0', []]])
for n in range(1, 17):
    name = f'E{n}'
    large[2].append(['function', name, [], [], [
        ['apply', 'a', f'E{n-1}', [], [], []], ['apply', 'b', f'E{n-1}', [], [], []], ['return', []]], [name, []]])
native('protocol-source', large)
native('protocol-compile', large, 'algorithm-expansion-limit')
# Final participant export rejects residual algorithm calls.
logical_ir = run(optimizer, '--zkc-project-participants', text=common)
run(optimizer, '--zkc-expand-algorithms', text=logical_ir, refuses='algorithm-expansion-stage')
foreign = logical_ir.replace('"algebra.sum"', '"func.call"', 1)
run(optimizer, '--verify-each', text=foreign, refuses='callee')

# A declaration selector denotes every expanded invocation of its primitive.
directory = records()
d = Path(directory)
f, r = 'field:bls12-381.fr', 'rng:bls12-381.fr'
draw = ['function', 'Draw', [['r', r]], [f, r], [
    ['op', 'sample', 'draw', [], ['r'], ['x', 'next']], ['return', ['x', 'next']]], ['Draw', []]]
twice = ['function', 'Two', [['r', r]], [f, r], [
    ['apply', 'first', 'Draw', [], ['r'], ['a', 'r1']],
    ['apply', 'second', 'Draw', [], ['r1'], ['b', 'r2']], ['return', ['b', 'r2']]], ['Two', []]]
check = ['function', 'Check', [['x', f]], ['bool'], [
    ['op', 'equal', 'equal', [], ['x', 'x'], ['ok']],
    ['op', 'guard', 'guard', [], ['ok'], []], ['return', ['ok']]], ['Check', []]]
src = ['zkc.protocol/1', [['draw', 'random.draw', ['bls12-381.fr'], ''],
    ['equal', 'field.equal', ['bls12-381.fr'], ''], ['guard', 'control.require', [], '']], [draw, twice, check],
    [['protocol', 'Main', ['P', 'V'], [], [['coins', 'V', r]], [['V', 'bool'], ['V', r]], [], [
        ['local', 'draw', 'V', 'Two', ['coins'], ['x', 'r2']],
        ['message', 'sample', 'field', 'V', 'P', 'x', 'seen'],
        ['local', 'check', 'V', 'Check', ['x'], ['ok']], ['return', ['ok', 'r2']]]]],
    [['instance', 'concrete', 'Main', [], [], [['P', 'P'], ['V', 'V']]]], [['entry', 'main', 'concrete']]]
descriptor = ['zkc.construction/1', 'main', 'P', 'V', [], ['coins', [['Draw', 'sample']]], '0', 'merlin3.bls12-381.fr64be/1', 'exact']
sp, dp = d / 'source.json', d / 'descriptor.json'
sp.write_text(json.dumps(src)); dp.write_text(json.dumps(descriptor))
result = json.loads(run(compiler, 'protocol-construct', sp, dp))
assert result[1] == descriptor
assert not any(i[0] == 'apply' for fn in result[2][2] for i in fn[4])
origins = [row for row in result[4] if row[4] == 'Two' and 'sample' in row[5]]
assert len({row[5] for row in origins}) == 2
cp = d / 'construction.json'; cp.write_text(json.dumps(result))
run(compiler, 'protocol-check-construction', sp, dp, cp)
native('protocol-compile', result[2])
assert native('protocol-prepare', src)[3:] == src[3:]

# A non-convertible sampler cannot use the selected RNG, even if its
# sampled value is dead or it follows the last selected scalar draw.
# The selected carrier is removed from the constructed result contract.
for before in (True, False):
    mixed = copy.deepcopy(src)
    mixed[1].append(['private_vector', 'random.vector', ['bls12-381.fr'], ''])
    two_body = mixed[2][1][4]
    if before:
        two_body[0][4] = ['r0']
        two_body.insert(0, ['op', 'private', 'private_vector', ['1'],
                           ['r'], ['ignored', 'r0']])
    else:
        two_body.insert(-1, ['op', 'private', 'private_vector', ['1'],
                            ['r2'], ['ignored', 'r3']])
        two_body[-1][1][1] = 'r3'
    native('protocol-source', mixed)
    sp.write_text(json.dumps(mixed))
    run(compiler, 'protocol-construct', sp, dp,
        refuses='construction-selected-rng-sampler:random.vector')

# A separate verifier-private provider is legitimate and stays private.
private = copy.deepcopy(src)
private[1].append(['private_vector', 'random.vector', ['bls12-381.fr'], ''])
private[2].append(['function', 'Private', [['r', r]], [r], [
    ['op', 'sample', 'private_vector', ['1'], ['r'], ['ignored', 'next']],
    ['return', ['next']]], ['Private', []]])
protocol = private[3][0]
protocol[4].append(['noise', 'V', r])
protocol[5].append(['V', r])
protocol[7].insert(0, ['local', 'private', 'V', 'Private', ['noise'], ['next_noise']])
protocol[7][-1][1].append('next_noise')
sp.write_text(json.dumps(private))
private_result = json.loads(run(compiler, 'protocol-construct', sp, dp))
native('protocol-compile', private_result[2])

# A function's own name and the origin it carries reach the same copies,
# including those expanded into its caller, and together select each once.
grouped = copy.deepcopy(src)
grouped[2][0][5] = ['Sampling', []]
gp, gd = d / 'grouped-source.json', d / 'grouped-descriptor.json'
gp.write_text(json.dumps(grouped)); gd.write_text(json.dumps(descriptor))
alone = json.loads(run(compiler, 'protocol-construct', gp, gd))
assert len({row[5] for row in alone[4] if row[4] == 'Two' and 'sample' in row[5]}) == 2
both = copy.deepcopy(descriptor)
both[5][1] = [['Sampling', 'sample'], ['Draw', 'sample']]
gd.write_text(json.dumps(both))
together = json.loads(run(compiler, 'protocol-construct', gp, gd))
assert together[1] == both and together[2:] == alone[2:]
both[5][1] = [['Draw', 'sample'], ['Draw', 'sample']]
gd.write_text(json.dumps(both))
run(compiler, 'protocol-construct', gp, gd, refuses='construction-draw-selector')
print(f'{commands.save()} local algorithm checks passed')
