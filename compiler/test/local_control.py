"""Structured local control: how it is represented, and what is rejected.

What the native runtime and the independent Lean consumer make of the same
source is a separate test, tests/execution/test_local_control_reference.py, because
it needs two further builds.
"""
import copy
import json
from pathlib import Path
import re
from commands import Commands
from tools import compiler, corpus, optimizer, records

root = Path(__file__).resolve().parents[2]
root = Path(root)


commands = Commands(records())


def run(args, text=None, refuses=None):
    return commands.run(args, stdin=text, refuses=refuses)


def native(mode, value, *flags, refuses=None):
    """A source given as text or as the record it serializes to."""
    text = value if isinstance(value, str) else json.dumps(value)
    result = run([compiler, mode, '-', *flags], text, refuses)
    return json.loads(result) if refuses is None and result.startswith('[') else result


def walk(body):
    for ins in body:
        yield ins
        if ins[0] == 'if':
            yield from walk(ins[4])
            yield from walk(ins[5])
        if ins[0] == 'for':
            yield from walk(ins[7])


text = (corpus / 'local-control.pir').read_text()
source = native('protocol-source', text)
# Preparation must discover calls inside local control, not only at the root.
prepared = native('protocol-prepare', text)
assert prepared != source, "nested calls did not trigger preparation"
assert not any(ins[0] == 'apply' for fn in prepared[2] if isinstance(fn[4], list) for ins in walk(fn[4]))

formatted = native('protocol-format', text)
assert native('protocol-source', formatted) == source
assert native('protocol-format', formatted) == formatted
canonical = native('protocol-format', source)
assert 'capture (' in canonical and 'carry (' in canonical
assert native('protocol-source', canonical) == source
logical = native('protocol-import', text)
assert '"pir.local_if"' in logical and '"pir.local_for"' in logical
run([optimizer, '--verify-each'], logical)
assert native('protocol-export', native('protocol-import', native('protocol-export', logical))) == native('protocol-export', logical)
expanded = run([optimizer, '--zkc-expand-algorithms', '--verify-each'], logical)
assert 'call @' not in expanded and '"pir.local_for"' in expanded
assert run([optimizer, '--zkc-expand-algorithms'], expanded) == expanded
plans = []
for flags in [[], ['--release-storage']]:
    plan = native('protocol-compile', source, *flags)
    physical = native('protocol-physical-ir', source, *flags)
    run([optimizer, '--verify-each'], physical)
    assert native('protocol-export', physical) == plan
    assert native('protocol-export', native('protocol-import', plan)) == plan
    plans.append(plan)

# Readable conveniences work without configuring a generic function, too.
closed = '''module {
  fn Local(x: koala-bear::Element) -> koala-bear::Element {
    let values = [x, field::add(x, x)];
    let mut result = values[0];
    for i in 0..2 { result = field::add(result, values[i]); }
    if true { result = field::neg(result); } else { }
    return result;
  }
}'''
native('protocol-import', closed)
native('protocol-import', closed.replace('Local(', '__binding_0('))
profile = '''module "arkworks.bls12-381/1" {
  fn Local(x: field, enabled: bool) -> field {
    let mut result = x;
    if enabled { result = field.add(x, field.add(x, x)); }
    let values = [result, x];
    for i in 0..values.len() { result = field::add(result, values[i]); }
    return result;
  }
}'''
profile_source = native('protocol-source', profile)
native('protocol-import', profile)
assert native('protocol-source', native('protocol-format', profile_source)) == profile_source
assert len([b for b in profile_source[1] if b[1] == 'field.add']) == 1
assert all(b[3] == ('native/' if b[1].startswith(('index.', 'indices.')) else 'arkworks/') + b[1]
           for b in profile_source[1])
native('protocol-source', 'module { fn Work<>() -> Indices {let xs = [0,1,2]; return xs;} }')
native('protocol-source', 'module { fn Work<F: Field>() -> Vector<F::Element> {let xs: Vector<F::Element> = []; return xs;} }')
for fragment, replacement, code in [
    ('let mut acc = x;', 'let acc = x;', 'source-assignment'),
    ('if enabled', 'if x', 'source-condition-type'),
    ('start..end', 'x..end', 'source-loop-bound-type'),
    ('let values = [x, acc];', 'let values = [x, enabled];', 'source-type-mismatch'),
    ('let values = [x, acc];', 'let values = [];', 'source-vector-type'),
    ('values[1]', 'values[enabled]', 'source-type-mismatch'),
    ('acc = Twice::<F>(acc);', 'return acc;', 'source-control-return'),
    ('acc = Twice::<F>(acc);', 'let branch_only = acc;', ''),
]:
    changed = text.replace(fragment, replacement)
    if replacement == 'let branch_only = acc;':
        changed = changed.replace('let values = [x, acc];', 'let values = [x, branch_only];')
        code = 'source-name-unresolved'
    native('protocol-source', changed, refuses=code)
native('protocol-source', text.replace('for i in start..end', 'while enabled'), refuses='source-syntax')
native('protocol-source', text.replace('local P:', 'if enabled {} else {} local P:'), refuses='source-syntax')
# Surface expression depth and reserved-looking quoted helpers are deliberate.
native('protocol-source', text.replace('values[1]', 'values' + '[0]' * 70), refuses='source-depth')
native('protocol-source', text.replace('values.len()', 'values.len() attributes (1)'), refuses='source-expression')
native('protocol-source', 'module { fn "helper.len"<>() -> index { let n = 0; return n; } fn Use<>() -> index { let n = "helper.len"(); return n; } }')
assert native('protocol-source', text.replace('[x, acc]', '[x, acc,]')) == source
# Dead branches must be well formed, even when the condition is a literal.
native('protocol-source', closed.replace('else { }', 'else { result = missing; }'), refuses='source-name-unresolved')
native('protocol-source', closed.replace('else { }', 'else { yield; }'), refuses='source-control-yield')
# Quoted names and same spelling in disjoint scopes must survive printing.
for keyword in ('if', 'for', 'else', 'mut', 'true', 'false'):
    renamed = closed.replace('Local(', json.dumps(keyword) + '(')
    common = native('protocol-source', renamed)
    assert native('protocol-source', native('protocol-format', common)) == common

# Admission reaches dormant regions and checks the complete site namespace.
prepared = native('protocol-prepare', source)
for label, mutate in [
    ('capture', lambda loop: loop[6].append('not_in_scope')),
    ('yield', lambda loop: loop[7][-1].__setitem__(1, [])),
    ('bound_type', lambda loop: loop.__setitem__(3, 'x')),
]:
    bad = copy.deepcopy(prepared)
    loop = next(i for f in bad[2] for i in f[4] if i[0] == 'for')
    mutate(loop)
    native('protocol-import', bad, refuses='')
# Portable isolated scopes may reuse an enclosing spelling that was not
# captured. Explicit printing must not invent a hidden lexical parent.
shadow = ['zkc.protocol/1', [['index','index.constant',[],'']], [
    ['function','Local',[['enabled','bool'],['outer','index']],['index'],[
        ['if','choice','enabled',[],[['op','left','index',['1'],[],['outer']],['yield',['outer']]],
         [['op','right','index',['2'],[],['outer']],['yield',['outer']]],['result']],
        ['return',['result']]],['Local',[]]]],[],[],[]]
assert native('protocol-source',native('protocol-format',shadow)) == shadow
for spelling in ('a..b', 'a.'):
    renamed = json.loads(json.dumps(shadow).replace('"outer"', json.dumps(spelling)))
    assert native('protocol-source', native('protocol-format', renamed)) == renamed

# Explicit captures are immutable region arguments: outer mutation must not
# silently disappear when the region supplies only its explicitly named yields.
explicit = '''module {
  fn Local(flag: bool, x: koala-bear::Element) -> koala-bear::Element {
    let mut acc = x;
    if flag capture (acc) -> () {
      acc = field::add(acc, acc); yield;
    } else { yield; }
    return acc;
  }
}'''
native('protocol-source', explicit, refuses='source-assignment')
native('protocol-source', explicit.replace('acc = field::add(acc, acc);', 'let hidden = field::add(acc, x);'), refuses='source-value-reference')
shadow[2][0][4] = [
    ['for','range','outer','outer','outer',[['state','outer']],[],[['yield',['state']]],['result']],
    ['return',['result']]]
assert native('protocol-source',native('protocol-format',shadow)) == shadow
for spelling in ('a..b', 'a.'):
    renamed = json.loads(json.dumps(shadow).replace('"outer"', json.dumps(spelling)))
    assert native('protocol-source', native('protocol-format', renamed)) == renamed

# A region interface must diagnose malformed input before accessing short ranges.
loop_line = next(line for line in logical.splitlines() if '"pir.local_for"(' in line)
broken = logical.replace(loop_line, re.sub(r'local_for"\([^)]*\)', 'local_for"()', loop_line), 1)
run([optimizer, '--verify-each'], broken, refuses='')
# Affine loop state must be carried, not implicitly borrowed on every trip.
affine = """module {
  fn Advance<F: Field>(rng: Rng<F>) -> Rng<F> {
    let (ignored, next) = random::draw(rng); return next;
  }
  fn Loop<F: Field>(rng: Rng<F>) -> Rng<F> {
    let mut state = rng;
    for i in 0..2 { state = Advance(state); }
    return state;
  }
  configure Concrete = Loop(F = bls12-381.fr);
}"""
native('protocol-import', affine)
native('protocol-source', affine.replace('state = Advance(state);', 'let lost = Advance(rng);'), refuses='')

temp = records()
directory = Path(temp)
save = commands.write
# Static schedule consumers refuse rather than flattening dynamic regions.
run([compiler, 'oracle-inspect', save('static-source.json', source), 'main'], refuses='execution-local-control-static-trace')
construction = corpus / 'local-control-construction.json'
descriptor = corpus / 'local-control-construction.descriptor.json'
constructed = json.loads(run([compiler, 'protocol-construct', construction, descriptor]))
run([compiler, 'protocol-check-construction', construction, descriptor,
     save('construction.json', constructed)])
constructed_plan = native('protocol-compile', constructed[2])
assert any(i[0] == 'for' for f in constructed_plan[3] for i in walk(f[4]))
replay = json.loads(construction.read_text())
replay[3][0][7].insert(-1, ['message', 'result', 'boolean', 'V', 'P', 'ok', 'seen_ok'])
run([compiler, 'protocol-construct', save('replay-source.json', replay), descriptor],
    refuses='construction-local-control-replay')
print(f"local control: {commands.save()} checks passed")
