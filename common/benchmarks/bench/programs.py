"""Source-level operation and control workloads. Generation is never timed."""
from dataclasses import dataclass, field
from copy import deepcopy
from typing import Callable

from . import algebra as a
from .oracle_policy import OraclePolicy


@dataclass
class Program:
    source: str
    inputs: list
    entry: str = 'example::Demo'
    dependencies: tuple = ('core.collections',)
    assets: dict = field(default_factory=dict)
    proof: bool = False
    changed: dict | None = None
    incorrect: dict | None = None
    invalid_witness: dict | None = None
    mutate_proof: Callable[[bytes], bytes] | None = None
    oracle: str = 'independent Python arithmetic; expected result checked on every call'
    support: tuple = ()
    oracle_policy: OraclePolicy = field(default_factory=OraclePolicy)
    invalid_witness_stop: tuple[str, str] | None = None


def increment_first(values, name, modulus, *, empty_value='1'):
    """Change one known field coordinate without changing its input type."""
    result = deepcopy(values)
    parent, key = result, name
    while isinstance(parent[key], list) and parent[key]:
        parent, key = parent[key], 0
    if isinstance(parent[key], list):
        parent[key] = [empty_value]
    else:
        text = parent[key]
        parent[key] = hex(int(text, 16) ^ 1) if text.startswith('0x') else str((int(text) + 1) % modulus)
    return result


HEADER = '''module example;
use zkc::vector::{Vector};
use zkc::vector as v;
use zkc::finite as finite;
use zkc::indices as idx;
domain F = field("FIELD");
'''


def local(field, parameters, body, inputs, *, root=None):
    source = HEADER.replace('FIELD', field) + f'''
fn compute({parameters})->bool {{ {body} }}
protocol Work roles(P)({parameters.replace(', ', ' @P, ')} @P)->(accepted:bool @P) {{
  return compute({', '.join(p.strip().split(':')[0] for p in parameters.split(','))});
}}
entry fn Demo(inputs: Work::Inputs) {{ return Work::run(inputs); }}
'''
    oracle = a.FieldOracle(field, root=root)
    return Program(source, [{'P': inputs}], support=oracle.support,
                   incorrect={'P': increment_first(inputs, 'expected', oracle.modulus,
                                                   empty_value=oracle.encode(oracle.one))})


def finite(shape):
    field, n, form = shape['field'], shape['elements'], shape['form']
    modulus = a.P if field == 'koala-bear' else a.FR
    values = [x[0] for x in a.dense(n, seed=21, modulus=modulus)]
    bodies = {
        'reduce': 'finite::sum(xs, fn(x)=>x*x+x)',
        'collect': 'v::sum(v::collect(xs, fn(x)=>x*x+x))',
        'bulk': 'v::sum(v::add(v::hadamard(xs,xs),xs))',
        'total-collect-fold': 'total::fold(v::elements(collect(v::elements(xs),fn(x)=>x*x+x)),seed,fn(s,x)=>s+x)',
        'total-fold': 'total::fold(v::elements(xs),seed,fn(s,x)=>s+x*x+x)',
    }
    seed = 'let seed:F=0; ' if form.startswith('total-') else ''
    program = local(field, 'xs:Vector<F>, expected:F',
                    f'{seed}return {bodies[form]} == expected;',
                    {'xs': list(map(str, values)), 'expected': str(sum(x*x+x for x in values) % modulus)})
    if form.startswith('total-'):
        program.source = program.source.replace('fn compute(', '''use zkc::finite_math as total;
math fn collect<I:Type+Copy+Drop>(rows:domain<I>,body:math fn(item:I)->F where item_from(item,rows))->Vector<F>
  = finite("math.collect.vector");
math fn compute(''')
    return program


def scan(shape):
    n, form = shape['elements'], shape['form']
    xs = [x[0] for x in a.dense(n, seed=31)]
    total, ys = 0, []
    for x in xs:
        total = (total + x) % a.P
        ys.append(str(total))
    body = ('let out=v::prefix_sum(xs);' if form == 'bulk' else '''
      let mut out=v::empty<F>(); let mut acc:F=0;
      for i in 0..v::length(xs) { acc=acc+v::get(xs,i); out=v::append(out,acc); }
    ''')
    return local('koala-bear', 'xs:Vector<F>, expected:Vector<F>', body+'return v::equal(out,expected);',
                 {'xs': list(map(str, xs)), 'expected': ys})


def numerical(shape):
    """Matched column/capture expressions with vector and scalar destinations."""
    field, n, form, sink = (shape[k] for k in ('field', 'elements', 'form', 'sink'))
    degree = 8 if field == 'koala-bear.ext8-binomial3' else 1
    modulus = a.FR if field == 'bls12-381.fr' else a.P
    xs, ys = (a.dense(n, degree, seed, modulus) for seed in (61, 62))
    capture = a.dense(1, degree, 63, modulus)[0]
    zero, one = (0,) * degree, (1,) + (0,) * (degree - 1)
    def add(x, y):
        return tuple((u + v) % modulus for u, v in zip(x, y, strict=True))
    def mul(x, y):
        return a.mul(x, y) if degree == 8 else (x[0] * y[0] % modulus,)
    invariant = add(mul(capture, capture), one)
    rows = [add(add(mul(x, y), mul(capture, add(x, y))), invariant)
            for x, y in zip(xs, ys, strict=True)]
    expected = rows
    if sink != 'map':
        expected = zero if sink == 'sum' else one
        combine = add if sink == 'sum' else mul
        for row in rows:
            expected = combine(expected, row)
    formula = 'x*y+c*(x+y)+(c*c+1)'
    domain = 'domains::zip(v::elements(xs),v::elements(ys))'
    if form == 'map':
        expression = 'map term(each xs, each ys, c)'
    elif form == 'collect':
        expression = f'v::collect({domain},fn((x,y))=>{formula})'
    elif form == 'bulk':
        expression = ('v::add(v::add(v::hadamard(xs,ys),v::scale(v::add(xs,ys),c)),'
                      'v::fill(c*c+1,v::length(xs)))')
    else:
        raise ValueError(f'unknown numerical source form: {form}')
    if sink != 'map':
        expression = f'v::{sink}({expression})'
    check = 'v::equal(out,expected)' if sink == 'map' else 'out == expected'
    parameters = 'xs:Vector<F>, ys:Vector<F>, c:F, expected:' + ('Vector<F>' if sink == 'map' else 'F')
    program = local(field, parameters, f'let out={expression}; return {check};',
                    {'xs': list(map(a.encode, xs)), 'ys': list(map(a.encode, ys)),
                     'c': a.encode(capture),
                     'expected': list(map(a.encode, expected)) if sink == 'map' else a.encode(expected)})
    program.source = program.source.replace('fn compute(', f'''use zkc::finite_domain as domains;
math fn term(x:F,y:F,c:F)->F {{ return {formula}; }}
fn compute(''')
    return program


def control(shape):
    rows, columns = shape['rows'], shape['columns']
    xs = [x[0] for x in a.dense(rows * columns, seed=41)]
    state = 0
    for r in range(rows):
        for c in range(columns):
            x = xs[r * columns + c]
            state = (state * 7 + x if (r+c) % 3 == 0 else state + x*x) % a.P
    return local('koala-bear', 'xs:Vector<F>, rows:index, columns:index, expected:F', '''
      let mut state:F=0;
      for r in 0..rows {
        for c in 0..columns {
          let x=v::get(xs,r*columns+c);
          state=if idx::remainder(r+c,3)==0 {state*7+x} else {state+x*x};
        }
      }
      return state==expected;
    ''', {'xs': list(map(str, xs)), 'rows': str(rows), 'columns': str(columns), 'expected': str(state)})


def polynomial(shape):
    n, degree = shape['elements'], shape['extension_degree']
    coefficients = a.dense(n//2, degree, seed=51)
    shift = (3,) if degree == 1 else (3, 1, 0, 0, 0, 0, 0, 0)
    expected = a.coset(coefficients, shift, n)
    # Polynomial coefficients are normalized by removing trailing zeroes.
    recovered = coefficients
    return local('koala-bear' + ('.ext8-binomial3' if degree == 8 else ''),
                 'cs:Vector<F>, shift:F, n:index, expected:Vector<F>, recovered:Vector<F>', '''
      let poly=kernel<F>("poly.from_coefficients",cs);
      let values=kernel<F>("poly.coset_evaluate",poly,shift,n);
      let back=kernel<F>("poly.coset_interpolate",values,shift);
      return v::equal(values,expected) && v::equal(kernel<F>("poly.coefficients",back),recovered);
    ''', {'cs': list(map(a.encode, coefficients)), 'shift': a.encode(shift), 'n': str(n),
          'expected': list(map(a.encode, expected)), 'recovered': list(map(a.encode, recovered))})


def extension(shape):
    n = shape['elements']
    xs, ys = a.dense(n, 8, 61), a.dense(n, 8, 62)
    expected = [a.mul(x, y) for x, y in zip(xs, ys, strict=True)]
    return local('koala-bear.ext8-binomial3', 'xs:Vector<F>, ys:Vector<F>, expected:Vector<F>',
                 'return v::equal(v::hadamard(xs,ys),expected);',
                 {'xs': list(map(a.encode, xs)), 'ys': list(map(a.encode, ys)), 'expected': list(map(a.encode, expected))})


def matrix(shape):
    rows, columns, stride = shape['rows'], shape['columns'], shape['stride']
    xs = [x[0] for x in a.dense(columns, seed=65, modulus=a.FR)]
    values = [x[0] for x in a.dense(rows*columns, seed=66, modulus=a.FR)]
    entries, expected = [], []
    for r in range(rows):
        total = 0
        for c in range(columns):
            if (r+c) % stride == 0:
                value = values[r*columns+c]
                entries.append([str(r), str(c), str(value)])
                total += value*xs[c]
        expected.append(str(total % a.FR))
    source = HEADER.replace('FIELD', 'bls12-381.fr') + '''
use zkc::matrix::{Matrix}; use zkc::matrix as mat;
protocol Work roles(P)(matrix:Matrix<F>@P,xs:Vector<F>@P,expected:Vector<F>@P)->(accepted:bool@P){
 let actual=mat::multiply(matrix,xs);
 return v::equal(actual,expected);
}
entry fn Demo(inputs: Work::Inputs) { return Work::run(inputs); }
'''
    inputs = {'matrix': {'rows': str(rows), 'columns': str(columns), 'entries': entries},
              'xs': list(map(str, xs)), 'expected': expected}
    return Program(source, [{'P': inputs}], incorrect={'P': increment_first(inputs, 'expected', a.FR)})


def curve(shape):
    n = shape['elements']
    xs = [x[0] for x in a.dense(n, seed=71, modulus=a.FR)]
    weights = [x[0] for x in a.dense(n, seed=72, modulus=a.FR)]
    source = HEADER.replace('FIELD', 'bls12-381.fr') + '''
use zkc::curve as curve;
domain G=group("bls12-381.g1");
fn work(xs:Vector<F>, weights:Vector<F>, scale:F, expected:F)->bool {
  let generator=curve::generator<G>();
  let points=curve::collect(xs,fn(x)=>generator*x);
  let scaled=curve::scale(points,scale);
  return curve::msm(weights,scaled)==generator*expected;
}
protocol Work roles(P)(xs:Vector<F>@P,weights:Vector<F>@P,scale:F@P,expected:F@P)->(accepted:bool@P){
 return work(xs,weights,scale,expected);
}
entry fn Demo(inputs: Work::Inputs) { return Work::run(inputs); }
'''
    scale = a.dense(1, seed=73, modulus=a.FR)[0][0]
    expected = sum(x*y*scale for x, y in zip(xs, weights, strict=True)) % a.FR
    inputs = {'xs': list(map(str, xs)), 'weights': list(map(str, weights)),
              'scale': str(scale), 'expected': str(expected)}
    return Program(source, [{'P': inputs}], dependencies=('core.algebra',), incorrect={'P': increment_first(inputs, 'expected', a.FR)},
                   oracle='Python scalar identity plus group law; shares native group kernels, not an independent curve implementation')


def pairing(shape):
    n = shape['pairs']
    source = '''module example;
use zkc::curve as curve;
use zkc::scalar as scalar;
domain F=field("bn254.fr");
domain G1=group("bn254.g1"); domain G2=group("bn254.g2"); domain GT=group("bn254.gt");
fn pair(a:G1,b:G2)->GT {return kernel<F>("pairing.apply",a,b);}
fn work(n:index,r:F,expected:F)->bool {
 let a=curve::generator<G1>();let b=curve::generator<G2>();let mut accepted=true;
 for i in 0..n {let x=r+scalar::from_index<F>(i+1);accepted=accepted && pair(a*x,b)==pair(a,b*(expected+scalar::from_index<F>(i+1)));}
 return accepted;
}
protocol Work roles(P)(n:index@P,r:F@P,expected:F@P)->(accepted:bool@P){return work(n,r,expected);}
entry fn Demo(inputs: Work::Inputs) { return Work::run(inputs); }
'''
    modulus = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    r = a.dense(1, seed=75, modulus=modulus)[0][0]
    inputs = {'n': str(n//2), 'r': str(r), 'expected': str(r)}
    return Program(source, [{'P': inputs}], dependencies=('core.algebra',), incorrect={'P': increment_first(inputs, 'expected', modulus)},
                   oracle='bilinearity consistency control; shares native pairing implementation')


def transcript(shape):
    rounds, payload = shape['rounds'], shape['elements']
    source = HEADER.replace('FIELD', 'bls12-381.fr') + '''
protocol Work roles(P,V)(n:index@(P,V),payload:Vector<F>@P,claim:F@V,coins:Random<F>@V)->(accepted:bool@V){
 let mut stateP:F@P=0;
 let mut stateV:F@V=0;
 let mut accepted@V=true;
 for _ in 0..n roles(P,V) max 256 {
  let received=send P->V(payload);
  let actual=send P->V(stateP);
  let received_sum=v::sum(received);
  accepted=accepted && received_sum==claim && actual==stateV;
  let challenge=coins.draw();
  let delivered=send V->P(challenge);
  stateP=stateP+delivered; stateV=stateV+challenge;
 }
 return accepted;
}
proof Proof=Work {prover P;verifier V;public {n,claim};accept accepted;
 construction fiat_shamir("merlin3.bls12-381.fr64be/0",coins);}
'''
    xs = [x[0] for x in a.dense(payload, seed=81+shape.get('statement', 0), modulus=a.FR)]
    public = {'n': str(rounds), 'claim': str(sum(xs) % a.FR)}
    return Program(source, [{'public': public, 'witness': {'payload': list(map(str, xs))}}],
                   entry='example::Proof', proof=True, invalid_witness=increment_first({'payload': list(map(str, xs))}, 'payload', a.FR), changed=public | {'claim': str((sum(xs)+1) % a.FR)},
                   oracle='Python payload sum and ordered challenge recurrence; same-stack proof verification')
