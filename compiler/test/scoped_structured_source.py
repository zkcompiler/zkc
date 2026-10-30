"""Checked scoped CFG export preserves closed SSA binders and actual bodies."""
import json
import re

from cases import case, counted
from commands import Commands
from tools import ROOT, compiler, records
from project import project_inputs

out = records()
commands = Commands(out)
prefix = 'module sample; domain Fr=field("bls12-381.fr");\n'


def emit(label, source):
    path = out / (label + '.zkc')
    path.write_text(prefix + source)
    return commands.run([compiler, 'language-emit', '--source-format=zkc',
                         f'--module=sample={path}', '--subject=sample::Run'])


def export(source, refusal=None):
    symbol = re.search(r'"protocol.func"[^\n]*sym_name = "([^"]+)"', source)[1]
    raw = commands.source('protocol-structured', source, '--symbol=' + symbol,
                          refuses=refusal)
    return None if refusal else json.loads(raw)


def local(snapshot):
    return next(d for d in snapshot[7] if d[0] == 'function' and d[2] == 'local')


with case('scoped ordinary identity has a logical formal signature'):
    identity = emit('identity', '''
fn identity(x:Fr)->Fr{return x;}
protocol Run roles(P)(x:Fr@P)->(r:Fr@P){return identity(x);}
''')
    definition = local(export(identity))
    assert definition[4:6] == [[['apply', 'field', [['domain', 'Field', 'bls12-381.fr']]]]] * 2
    assert definition[9] == ['block', [], ['return', [0]]]

# Shared fixture setup is outside the cases: each mutation can then be judged
# independently, without relying on a preceding case to finish successfully.
conditional = emit('conditional', '''
fn choose(x:Fr,y:Fr,go:bool)->Fr{return if go{x}else{y};}
protocol Run roles(P)(x:Fr@P,y:Fr@P,go:bool@P)->(r:Fr@P){return choose(x,y,go);}
''')
branch = local(export(conditional))[9][1][0]
with case('closed conditional regions retain separate formal positions'):
    assert branch[0:2] == [['if'], [2, 0, 1]]
    assert branch[3][0][2][2] == ['yield', [0]]
    assert branch[3][1][2][2] == ['yield', [1]]

with case('aliased actual arguments do not collapse closed formal positions'):
    call = re.search(r'"protocol.local_call"\(([^)]+)\)', conditional)
    first, second, condition = call[1].split(', ')
    changed = conditional.replace(call[0], f'"protocol.local_call"({first}, {first}, {condition})')
    alias = export(changed)
    protocol = next(d for d in alias[7] if d[2] == 'protocol')
    assert protocol[9][1][0][1] == [0, 0, 2]
    assert local(alias)[9][1][0] == branch

with case('actual branch payload changes the exported formal body'):
    match = re.search(r'"exec.complete"\(([^)]+)\)', conditional)
    scope, first = match[1].split(', ')
    second = '%arg' + str(int(first.removeprefix('%arg')) + 1)
    changed = conditional[:match.start()] + conditional[match.start():].replace(
        match[0], f'"exec.complete"({scope}, {second})', 1)
    actual = local(export(changed))[9][1][0]
    assert actual[3][0][2][2] == ['yield', [1]]
    assert actual != branch

with case('changed occurrence is retained and not inferred from origin'):
    changed = conditional.replace('site = "s2"', 'site = "actual"')
    assert local(export(changed))[9][1][0][4] == 'actual'

with case('inconsistent branch captures are refused before export'):
    changed = conditional
    enter = re.search(r'"runtime.enter_scope"\(([^)]+)\)', changed)
    scope, first, second = enter[1].split(', ')
    changed = changed.replace(enter[0], f'"runtime.enter_scope"({scope}, {first}, {first})', 1)
    export(changed, 'structured-source-original')

with case('loop captures are transported as closed formal arguments'):
    loop = emit('loop', '''
fn replace(x:Fr,y:Fr,n:index)->Fr{let mut r=x;for _ in 0..n{r=y;}return r;}
protocol Run roles(P)(x:Fr@P,y:Fr@P,n:index@P)->(r:Fr@P){return replace(x,y,n);}
''')
    body = local(export(loop))[9][1]
    iteration = next(op for op in body if op[0] == ['for'])
    region = iteration[3][0]
    assert region[0] == [['apply', 'index', []], ['apply', 'field', [['domain', 'Field', 'bls12-381.fr']]], ['apply', 'field', [['domain', 'Field', 'bls12-381.fr']]]]
    assert region[1] == [['apply', 'field', [['domain', 'Field', 'bls12-381.fr']]]] * 2
    assert region[2][2] == ['yield', [2, 2]]

with case('stopping arm keeps its reason and occurrence'):
    stopped = emit('stopped', '''
fn check(x:Fr,go:bool)->Fr{return if go{x}else{stop "reject";};}
protocol Run roles(P)(x:Fr@P,go:bool@P)->(r:Fr@P){return check(x,go);}
''')
    stop = local(export(stopped))[9][1][0][3][1][2][2]
    assert stop[:2] == ['stop', 'reject'] and stop[2]

with case('mathematical request retains actual helper and equation'):
    computation = emit('computation', '''
math fn add(x:Fr,y:Fr)->Fr{return x+y;}
fn work(x:Fr,y:Fr)->Fr{return add(x,y);}
protocol Run roles(P)(x:Fr@P,y:Fr@P)->(r:Fr@P){return work(x,y);}
''')
    snapshot = export(computation)
    target = local(snapshot)[9][1][0][0]
    assert target[0] == 'apply'
    realized = next(d for d in snapshot[7] if d[1] == target[1])
    assert realized[0] == 'realize'
    equation = next(d for d in snapshot[7] if d[1] == realized[4])
    assert equation[2] == 'math'
    assert equation[9][1][0][0] == ['field.add', 'bls12-381.fr']

# One native invocation operation carries an explicit contract binding. A
# same-port contract change must be reflected in the exported declaration.
primitive = emit('primitive', '''
fn plus(x:index,y:index)->index{return x+y;}
protocol Run roles(P)(x:index@P,y:index@P)->(r:index@P){return plus(x,y);}
''')
with case('primitive identity comes from its binding and exact data ports'):
    snapshot = export(primitive)
    step = local(snapshot)[9][1][0]
    assert step[0][0:2] == ['exec', 'exec.apply']
    binding = next(row for row in snapshot[6] if row[1] == step[0][2])
    assert binding[2:] == ['index.add', [], '', [['apply', 'index', []]] * 2, [['apply', 'index', []]]]
    assert step[1:4] == [[0, 1], [['apply', 'index', []]], []]

with case('same-port contract retargeting remains visible'):
    changed = primitive.replace('contract = "index.add"', 'contract = "index.sub"')
    assert changed != primitive
    snapshot = export(changed)
    step = local(snapshot)[9][1][0]
    assert step[0][0:2] == ['exec', 'exec.apply']
    binding = next(row for row in snapshot[6] if row[1] == step[0][2])
    assert binding[2:] == ['index.sub', [], '', [['apply', 'index', []]] * 2, [['apply', 'index', []]]]

with case('invocation parameters export semantic records'):
    constant = emit('constant', '''
fn answer()->index{return 42;}
protocol Run roles(P)()->(r:index@P){return answer();}
''')
    snapshot = export(constant)
    step = local(snapshot)[9][1][0]
    assert step[0][0:2] == ['exec', 'exec.apply']
    assert step[0][3] == [['natural', '42']]
    binding = next(row for row in snapshot[6] if row[1] == step[0][2])
    assert binding[2:] == ['index.constant', [], '', [], [['apply', 'index', []]]]

with case('retired per-primitive operation has no source reader'):
    changed = primitive.replace('"exec.apply"', '"algebra.exec.index_add"')
    assert changed != primitive
    export(changed, 'structured-source-original')

modules, assets = project_inputs(ROOT / 'compiler/test/fixtures/structured-source/map-callers.toml')
assert not assets
mapped = commands.run([compiler, 'language-emit', '--source-format=zkc',
    '--subject=map_examples::LinearCombination',
    *[f'--module={name}={path}' for name, path in sorted(modules.items())]])
mapping = export(mapped)
collection = next(d for d in mapping[7] if d[0] == 'collect')
domain = next(d for d in mapping[4] if d[1] == collection[5])
with case('collection preserves all zipped operands including an unused row'):
    assert domain[3:] == [[['elements', 0], ['elements', 1], ['zip', [1, 0]],
                          ['elements', 2], ['zip', [1, 0]]], 0]
    assert collection[4] == [['apply', 'vector', [['domain', 'Field', 'bls12-381.fr']]]]
    assert collection[7] == ''
    callback = next(d for d in mapping[7] if d[1] == collection[6])
    assert callback[2:4] == ['local', 'private']
    assert callback[4][:3] == [['apply', 'field', [['domain', 'Field', 'bls12-381.fr']]]] * 3
    assert callback[4][3:] == collection[3]
    computation = next(d for d in mapping[7] if d[1] == callback[9][1][0][0][1])
    assert computation[0] == 'realize'

with case('domain item order follows the actual SSA zip operands'):
    zipped = re.search(r'"data.domain_zip"\(([^)]+)\)', mapped)
    operands = zipped[1].split(', ')
    changed = mapped.replace(zipped[0], '"data.domain_zip"(' + ', '.join(reversed(operands)) + ')')
    actual = next(d for d in export(changed)[4] if d[1] == domain[1])
    assert actual[3][2] == ['zip', [0, 1]]
    assert actual[3][-1] == ['zip', [1, 0]]

with case('unused domain constructors retain their ordered admission'):
    element = re.search(r'"data.domain_elements"[^\n]+', mapped)[0]
    terminal = mapped.index('"data.domain_yield"')
    line = mapped.rfind('\n', 0, terminal) + 1
    changed = mapped[:line] + '      %unused = ' + element + '\n' + mapped[line:]
    actual = next(d for d in export(changed)[4] if d[1] == domain[1])
    assert actual[3] == domain[3] + [['elements', 0]]
    assert actual[4] == 1

commands.save()
print(f'scoped-structured-source: {counted()} cases')
