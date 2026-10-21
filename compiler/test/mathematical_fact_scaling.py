"""Simple available proofs remain usable at realistic declaration sizes."""
from cases import case
from commands import Commands
from entry_artifacts import compile_run_package
from tools import compiler, optimizer, records

output = records()
commands = Commands(output)
prelude = '''module m;
domain Fr=field("koala-bear");
type Array<F:Field,N:nat>=builtin("field_array",F,N);
type Vector<F:Field>=builtin("vector",F);
'''

with case('independent same-sized arrays retain immediate constant bounds'):
    count = 128
    arguments = ', '.join(f'x{k}:Array<Fr,4>' for k in range(count))
    reads = '\n'.join(
        f'let y{k}=intrinsic<Array<Fr,4>>("container.at",x{k},0);'
        for k in range(count))
    path = output / 'arrays.zkc'
    path.write_text(prelude + f'math fn subject({arguments})->Fr {{\n'
                    f'{reads}\nreturn y{count-1};}}\n')
    commands.run([compiler, 'language-check', '--source-format=zkc',
                  f'--module=m={path}'])

with case('source and emitted IR agree on a direct bound among many premises'):
    count = 192
    arguments = ', '.join(['i:index'] + [f'x{k}:Vector<Fr>' for k in range(count)])
    conditions = ', '.join(['in_bounds(i,x0)'] + [
        f'equal_extent(x{k},x{k+1})' for k in range(count-1)])
    actuals = ', '.join(['i'] + ['xs'] * count)
    path = output / 'preconditions.zkc'
    path.write_text(prelude + f'''
domain fn indices<F:Field>(xs:Vector<F>)->domain<index>=domain("indices");
math fn total<I:Type+Copy+Drop,S:Type+Copy+Drop>(rows:domain<I>,initial:S,
 step:math fn(S,item:I)->S where item_from(item,rows))->S=finite("math.fold");
math fn subject({arguments})->Fr where {conditions} {{
 return intrinsic<Vector<Fr>>("container.at",x0,i);
}}
math fn work(xs:Vector<Fr>)->Fr {{
 return total(indices(xs),0,fn(state,i)=>state+subject({actuals}));
}}
protocol Demo roles(P)(xs:Vector<Fr>@P)->(r:Fr@P){{return work(xs);}}
run Run(inputs: Demo::Inputs) {{ return Demo::run(inputs); }}
''')
    options = ['--source-format=zkc', f'--module=m={path}']
    commands.run([compiler, 'language-check', *options])
    emitted = compile_run_package(commands, *options)['original']
    original = output / 'preconditions.mlir'
    original.write_text(emitted)
    commands.run([optimizer, original, '-o', output / 'checked.mlir'])

with case('identity forwarding preserves a direct bound among many premises'):
    count = 128
    arguments = ', '.join(['%i:ui64'] + [f'%x{k}:!S' for k in range(count)])
    conditions = ', '.join(['#data.index_bound<0,1,0>'] + [
        f'#data.equal_extent<{k},0,{k+1},0>' for k in range(1, count)])
    commands.verified(f'''!S = !data.sequence<i1>
module {{
 func.func private @identity(%s:!S)->!S {{ func.return %s : !S }}
 func.func @subject({arguments})->i1 attributes {{data.preconditions=[{conditions}]}} {{
  %alias = func.call @identity(%x0) : (!S)->!S
  %v = "data.bounded_at"(%alias,%i) : (!S,ui64)->i1
  func.return %v : i1
 }}
}}
''')


def nested_domain(wrappers, leaf, item, inputs):
    lines = [f'"data.domain"() ({{ ^entry({inputs}):', leaf]
    lines += [
        f'%d{k+1} = "data.domain_product"(%d{k}) : '
        f'(!data.domain<{item}>)->!data.domain<{item}>'
        for k in range(wrappers)
    ]
    lines += [
        f'"data.domain_yield"(%d{wrappers}) : (!data.domain<{item}>)->()',
        '}) {sym_name="items",sym_visibility="private",'
        f'function_type=({",".join(a.split(":")[1] for a in inputs.split(","))})'
        f'->!data.domain<{item}>}} : ()->()',
    ]
    return '\n'.join(lines)


# Each descriptor and helper dependency graph is below its declaration limit.
# Only their composed interpretation path exceeds the extraction ceiling.
for wrappers, appends, refused in ((0, 70, False), (60, 50, False),
                                   (60, 70, True), (0, 90, True)):
    with case(f'domain depth {wrappers} composes with {appends} append calls'):
        domain = nested_domain(
            wrappers,
            '%d0 = "data.domain_elements"(%xs) : (!S)->!data.domain<!F>',
            '!F', '%xs:!S')
        calls = '\n'.join(
            f'%s{k+1} = func.call @append(%s{k},%x) : (!S,!F)->!S'
            for k in range(appends))
        commands.verified(f'''!F = !algebra.field<"bls12-381.fr">
!S = !data.sequence<!F>
!A = !algebra.field_array<"bls12-381.fr", {appends}>
module {{
{domain}
func.func private @body(%x:!F,%xs:!S)->!F {{ func.return %x : !F }}
func.func private @append(%xs:!S,%x:!F)->!S {{
 %r = "data.sequence_append"(%xs,%x) : (!S,!F)->!S
 func.return %r : !S
}}
func.func @subject(%x:!F)->!A {{
 %s0 = "data.sequence_empty"() : ()->!S
 {calls}
 %r = "algebra.finite_collect"(%s{appends}) {{domain=@items,body=@body}} : (!S)->!A
 func.return %r : !A
}}
}}
''', refuses='finite-analysis-limit' if refused else None)

for wrappers, forwards, refused in ((0, 220, False), (60, 180, False),
                                    (60, 220, True), (0, 257, True)):
    with case(f'domain depth {wrappers} composes with {forwards} endpoint forwards'):
        domain = nested_domain(
            wrappers,
            '%d0 = "data.domain_range"(%lo,%hi) : (ui64,ui64)->!data.domain<ui64>',
            'ui64', '%lo:ui64,%hi:ui64')
        calls = '\n'.join(
            f'%n{k+1} = func.call @identity(%n{k}) : (ui64)->ui64'
            for k in range(forwards))
        commands.verified(f'''!F = !algebra.field<"bls12-381.fr">
!A = !algebra.field_array<"bls12-381.fr", 3>
module {{
{domain}
func.func private @body(%i:ui64,%lo:ui64,%hi:ui64,%x:!F)->!F {{
 func.return %x : !F
}}
func.func private @identity(%n:ui64)->ui64 {{ func.return %n : ui64 }}
func.func @subject(%x:!F)->!A {{
 %lo = "data.index"() {{value="0"}} : ()->ui64
 %n0 = "data.index"() {{value="3"}} : ()->ui64
 {calls}
 %r = "algebra.finite_collect"(%lo,%n{forwards},%x) {{domain=@items,body=@body}}
   : (ui64,ui64,!F)->!A
 func.return %r : !A
}}
}}
''', refuses='finite-analysis-limit' if refused else None)
