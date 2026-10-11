"""Simple available proofs remain usable at realistic declaration sizes."""
from cases import case
from commands import Commands
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
run Run=Demo;
''')
    options = ['--source-format=zkc', f'--module=m={path}']
    commands.run([compiler, 'language-check', *options])
    emitted = commands.run([compiler, 'language-emit', *options])
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
