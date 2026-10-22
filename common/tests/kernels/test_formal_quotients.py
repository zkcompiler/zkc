"""Formal quotient values preserve source meaning through managed execution."""
import pytest

from entry import Entry
from source_modules import library_modules

MODULES = library_modules('core/polynomial')


def project(values, q, n):
    return [sum((-1)**(i//n) * a for i, a in enumerate(values) if i % n == j) % q
            for j in range(n)]


def multiply(a, b, q):
    n = len(a)
    full = [sum(a[i]*b[k-i] for i in range(n) if 0 <= k-i < n)
            for k in range(2*n-1)]
    return project(full, q, n)


@pytest.mark.parametrize('q,n', [(2, 1), (16, 3), (17, 2), (17, 4), (2**64-1, 4),
                              (12289, 512), (8380417, 256), (3329, 256)])
@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage'), ('--no-calculation-batching',)])
def test_compound_formal_quotients(toolchain, journal, directory, q, n, flags):
    source = f'''module sample;
    use zkc::indices::{{Indices}}; use zkc::quotient_math as ring;
    math fn compound(a:ring::Element<{q},{n}>,b:ring::Element<{q},{n}>)
      ->ring::Element<{q},{n}>{{return (a+b)*(a-b);}}
    math fn calculate(a:Indices,b:Indices)->Indices{{
      let left=ring::project<{q},{n}>(a); let right=ring::project<{q},{n}>(b);
      return ring::coefficients(compound(left,right));
    }}
    fn ordered(a:Indices,b:Indices)->Indices{{return calculate(a,b);}}
    protocol Run roles(P)(a:Indices@P,b:Indices@P)->(direct:Indices@P,ordered:Indices@P){{
      return(direct=calculate(a,b),ordered=ordered(a,b));
    }}entry fn Demo(inputs:Run::Inputs){{return Run::run(inputs);}}'''
    entry = Entry(toolchain, journal, directory, source, (*MODULES, *flags))
    cases = [([], []), ([q-1]*n, [1]*n),
             ([2**64-1]+list(range(2*n+3)), [q, q-1, 0, 3])]
    if (q, n) == (17, 2):
        cases.append(([4, 0], [0, 1]))  # Nonzero factors multiply to zero.
    for number, (a, b) in enumerate(cases):
        aa, bb = project(a, q, n), project(b, q, n)
        expected = list(map(str, multiply([(x+y) % q for x, y in zip(aa, bb)],
                                         [(x-y) % q for x, y in zip(aa, bb)], q)))
        assert entry.run(f'case-{number}', {'a': a, 'b': b}) == {
            'direct': expected, 'ordered': expected}


@pytest.mark.parametrize('flags', [(), ('--no-simplify',), ('--no-calculation-batching',)])
def test_quotient_observations_across_actions(toolchain, journal, directory, flags):
    source = '''module sample;
    use zkc::indices::{Indices}; use zkc::quotient_math as ring;
    math fn project(a:Indices)->Indices{return ring::coefficients(ring::project<17,4>(a));}
    math fn square(a:Indices)->Indices{
      let x=ring::project<17,4>(a);return ring::coefficients(ring::multiply(x,x));
    }
    protocol Run roles(P,V)(a:Indices@P)->(first:Indices@V,second:Indices@V){
      let first=send P -> V(project(a));
      let second=send P -> V(square(a));
      return(first=first,second=second);
    }entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}'''
    entry = Entry(toolchain, journal, directory, source, (*MODULES, *flags))
    a = [17, 18, 19, 20, 21]
    expected = project(a, 17, 4)
    assert entry.run_roles('two-actions', {'P': {'a': a}, 'V': {}})['V'] == {
        'first': list(map(str, expected)), 'second': list(map(str, multiply(expected, expected, 17)))}


@pytest.mark.parametrize('body,diagnostic', [
    ('type Bad=formal("quotient",1,4);', 'source.formal'),
    ('type Bad=formal("quotient",17,0);', 'source.formal'),
    ('math fn bad<Q:nat,N:nat>(a:Indices)->ring::Element<Q,N> where (){'
     'return intrinsic<Q,N>("quotient.value.project",a);}', 'source.bound'),
    ('math fn bad(a:ring::Element<17,4>,b:ring::Element<19,4>)->ring::Element<17,4>{'
     'return ring::add(a,b);}', 'source.type'),
    ('math fn bad(a:ring::Element<17,4>,b:ring::Element<17,8>)->ring::Element<17,4>{'
     'return ring::multiply(a,b);}', 'source.type'),
    ('protocol Run roles(P,V)(a:Indices@P)->(r:Indices@V){'
     'let x=send P -> V(ring::project<17,4>(a));return ring::coefficients(x);}', 'source.formal'),
    ('fn bad(a:Indices)->ring::Element<17,4>{return ring::project<17,4>(a);}', 'source.formal'),
])
def test_formal_parameter_and_boundary_refusals(toolchain, journal, directory, body, diagnostic):
    path = directory / 'invalid.zkc'
    path.write_text('module sample;use zkc::indices::{Indices};use zkc::quotient_math as ring;' + body)
    report = journal.json([toolchain.runtime, '--json', 'check', f'--compiler={toolchain.compiler}',
                           f'--module=sample={path}', *MODULES], refuses='source-compilation')
    assert report['diagnostics'].startswith(diagnostic), report


@pytest.mark.parametrize('q,n,rows,columns', [(12289, 512, 1, 4), (8380417, 256, 4, 4)])
def test_shared_input_module_products(toolchain, journal, directory, q, n, rows, columns):
    vector = ','.join(f'ring::project<{q},{n}>(v[{j}])' for j in range(columns))
    matrix = ','.join(f'ring::project<{q},{n}>(m[{i}])' for i in range(rows*columns))
    outputs = ','.join('ring::coefficients(' + '+'.join(
        f'a[{i*columns+j}]*b[{j}]' for j in range(columns)) + ')' for i in range(rows))
    source = f'''module sample;
    use zkc::indices::{{Indices}};use zkc::quotient_math as ring;
    math fn calculate(m:[Indices;{rows*columns}],v:[Indices;{columns}])->[Indices;{rows}]{{
      let a=[{matrix}];let b=[{vector}];return [{outputs}];
    }}
    protocol Run roles(P)(matrix:[Indices;{rows*columns}]@P,vector:[Indices;{columns}]@P)
      ->(result:[Indices;{rows}]@P){{return calculate(matrix,vector);}}
    entry fn Demo(inputs:Run::Inputs){{return Run::run(inputs);}}'''
    entry = Entry(toolchain, journal, directory, source, MODULES)
    a = [[(index*7+j*13+1) % q for j in range(n)] for index in range(rows*columns)]
    b = [[(index+j*j+3) % q for j in range(n)] for index in range(columns)]
    expected = []
    for row in range(rows):
        terms = [multiply(a[row*columns+j], b[j], q) for j in range(columns)]
        expected.append([str(sum(values) % q) for values in zip(*terms)])
    assert entry.run('module-product', {'matrix': a, 'vector': b})['result'] == expected


def test_mathematical_primitive_signature_roots(toolchain, journal, directory):
    source = '''module sample;
    type I=builtin("indices");type R<Q:nat,N:nat>=formal("quotient",Q,N);
    math fn project<Q:nat,N:nat>(data:I)->R<Q,N>=primitive("quotient.value.project");
    math fn observe<Q:nat,N:nat>(value:R<Q,N>)->I=primitive("quotient.value.coefficients");
    math fn product<Q:nat,N:nat>(a:R<Q,N>,b:R<Q,N>)->R<Q,N>=primitive("quotient.value.multiply");
    math fn calculate(a:I,b:I)->I{
      return observe(product(project<17,2>(a),project<17,2>(b)));
    }
    protocol Run roles(P)(a:I@P,b:I@P)->(result:I@P){return calculate(a,b);}
    entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}'''
    entry = Entry(toolchain, journal, directory, source)
    assert entry.run('zero-divisor', {'a': [13, 1], 'b': [4, 1]})['result'] == ['0', '0']
