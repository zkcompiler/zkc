"""Separately named SDK/run operation controls, including source validation."""
from functools import reduce

from . import algebra as a
from .programs import local


def host_vector(shape):
    """Matched large inputs with minimal length work or one linear reduction."""
    n, operation = shape['elements'], shape['operation']
    xs = [x[0] for x in a.dense(n, seed=281)]
    if operation == 'length':
        expected, result, result_type = n, 'v::length(xs)', 'index'
    elif operation == 'sum':
        expected, result, result_type = sum(xs) % a.P, 'v::sum(xs)', 'F'
    else:
        raise ValueError(f'unknown Host vector operation: {operation}')
    program = local('koala-bear', f'xs:Vector<F>, expected:{result_type}',
                    f'return {result}==expected;',
                    {'xs': list(map(str, xs)), 'expected': str(expected)})
    program.oracle = 'independent linear Python length/sum; identical vector across operations; existing JSON-to-native Host Run path, no transport-only or kernel-only timing'
    return program


def field_vector(shape, *, root=None):
    f = a.FieldOracle(shape['field'], root=root)
    n, operation = shape['elements'], shape['operation']
    xs, ys = f.dense(n, 241), f.dense(n, 242)
    c, = f.dense(1, 243)
    vector = operation in ('add', 'subtract', 'hadamard', 'scale')
    if operation in ('add', 'subtract', 'hadamard'):
        combine = {'add': f.add, 'subtract': f.sub, 'hadamard': f.mul}[operation]
        expected = [combine(x, y) for x, y in zip(xs, ys, strict=True)]
        parameters = 'xs:Vector<F>, ys:Vector<F>'
        inputs = {'xs': list(map(f.encode, xs)), 'ys': list(map(f.encode, ys))}
        result = f'v::{operation}(xs,ys)'
    elif operation == 'scale':
        expected = [f.mul(x, c) for x in xs]
        parameters = 'xs:Vector<F>, c:F'
        inputs = {'xs': list(map(f.encode, xs)), 'c': f.encode(c)}
        result = 'v::scale(xs,c)'
    elif operation in ('sum', 'product', 'dot'):
        values = [f.mul(x, y) for x, y in zip(xs, ys, strict=True)] if operation == 'dot' else xs
        expected = reduce(f.mul if operation == 'product' else f.add, values,
                          f.one if operation == 'product' else f.zero)
        parameters = 'xs:Vector<F>' + (', ys:Vector<F>' if operation == 'dot' else '')
        inputs = {'xs': list(map(f.encode, xs))}
        if operation == 'dot':
            inputs['ys'] = list(map(f.encode, ys))
        result = f'v::{operation}(xs' + (',ys)' if operation == 'dot' else ')')
    else:
        raise ValueError(f'unknown field vector operation: {operation}')
    parameters += ', expected:' + ('Vector<F>' if vector else 'F')
    inputs['expected'] = list(map(f.encode, expected)) if vector else f.encode(expected)
    check = 'v::equal(out,expected)' if vector else 'out==expected'
    return local(shape['field'], parameters, f'let out={result}; return {check};', inputs, root=root)


def transform(shape):
    """One transform direction per call; never a native roundtrip oracle."""
    degree, n, operation = shape['extension_degree'], shape['elements'], shape['operation']
    field = 'koala-bear' + (f'.ext{degree}-binomial3' if degree != 1 else '')
    coefficients = a.dense(n, degree, 251)
    shift = (1,) + (0,) * (degree-1)
    values = a.coset(coefficients, shift, n)
    if operation == 'dft':
        data, expected = coefficients, values
        body = '''let poly=kernel<F>("poly.from_coefficients",xs);
          let out=kernel<F>("poly.coset_evaluate",poly,shift,n);'''
    elif operation == 'interpolate':
        data, expected = values, coefficients
        body = '''let poly=kernel<F>("poly.coset_interpolate",xs,shift);
          let out=kernel<F>("poly.coefficients",poly);'''
    else:
        raise ValueError(f'unknown transform operation: {operation}')
    return local(field, 'xs:Vector<F>, shift:F, n:index, expected:Vector<F>',
                 body + 'return v::equal(out,expected);',
                 {'xs': list(map(a.encode, data)), 'shift': a.encode(shift), 'n': str(n),
                  'expected': list(map(a.encode, expected))})


def coset_batch(shape):
    """Matched authored columns and library batching, with explicit layout costs."""
    degree, height, width = shape['extension_degree'], shape['height'], shape['width']
    size, layout, form = shape['evaluation_size'], shape['layout'], shape['form']
    if layout not in ('columns', 'rows') or form not in ('columns', 'library'):
        raise ValueError('unknown coset batch layout or form')
    field = 'koala-bear' + (f'.ext{degree}-binomial3' if degree != 1 else '')
    f = a.FieldOracle(field)
    shift, = f.dense(1, 301)
    coefficients = [f.dense(height, 302+column) for column in range(width)]
    source = [a.coset(cs, f.one, height) for cs in coefficients]
    target = [a.coset(cs, shift, size) for cs in coefficients]

    def flatten(columns, rows):
        return ([value for column in columns for value in column] if layout == 'columns' else
                [columns[column][row] for row in range(rows) for column in range(width)])

    prefix = 'let columns=xs;' if layout == 'columns' else 'let columns=v::transpose(xs,height,width);'
    if form == 'library':
        body = 'let out=coset::extend_columns(columns,width,height,shift,size);'
    else:
        body = '''let mut out=v::empty<F>();
          for column in 0..width {
            let values=v::slice(columns,column*height,height);
            let p=coset::interpolate(coset::word(values,1));
            out=v::concat(out,coset::values(coset::evaluate_coset(p,shift,size)));
          }'''
    suffix = 'return v::equal(out,expected);' if layout == 'columns' else \
             'return v::equal(v::transpose(out,width,size),expected);'
    program = local(field, 'xs:Vector<F>, width:index, height:index, shift:F, size:index, expected:Vector<F>',
                    prefix+body+suffix,
                    {'xs': list(map(f.encode, flatten(source, height))), 'width': str(width),
                     'height': str(height), 'shift': f.encode(shift), 'size': str(size),
                     'expected': list(map(f.encode, flatten(target, size)))})
    program.source = program.source.replace('fn compute(', 'use zkc::coset as coset;\nfn compute(')
    program.dependencies = ('core.collections', 'core.polynomial')
    program.oracle = 'Independent integer radix-two evaluation of dense coefficients; every output and extension coordinate checked; no native roundtrip oracle'
    return program


def coset(shape):
    """Separate subgroup traversal and folding with arbitrary coset shifts."""
    degree, n, operation = shape['extension_degree'], shape['elements'], shape['operation']
    field = 'koala-bear' + (f'.ext{degree}-binomial3' if degree != 1 else '')
    f = a.FieldOracle(field)
    shift, beta = f.dense(2, 291)
    root = pow(1791270792, (1 << 24)//n, a.P)
    parameters = 'shift:F, n:index'
    inputs = {'shift': f.encode(shift), 'n': str(n)}
    if operation == 'points':
        expected = [tuple(c*pow(root, i, a.P) % a.P for c in shift) for i in range(n)]
        result = 'kernel<F>("poly.domain_points",shift,n)'
    elif operation == 'fold':
        values = f.dense(n, 292)
        inverse_shift = f.power(shift, a.P**degree-2)
        expected = []
        for i, (left, right) in enumerate(zip(values[:n//2], values[n//2:], strict=True)):
            inverse_twice_x = tuple(c*pow(2*pow(root, i, a.P), -1, a.P) % a.P
                                    for c in inverse_shift)
            half_sum = tuple(c*pow(2, -1, a.P) % a.P for c in f.add(left, right))
            expected.append(f.add(half_sum, f.mul(beta, f.mul(f.sub(left, right), inverse_twice_x))))
        parameters += ', xs:Vector<F>, beta:F'
        inputs |= {'xs': list(map(f.encode, values)), 'beta': f.encode(beta)}
        result = 'kernel<F>("poly.even_odd_fold",xs,shift,beta)'
    else:
        raise ValueError(f'unknown coset operation: {operation}')
    inputs['expected'] = list(map(f.encode, expected))
    return local(field, parameters+', expected:Vector<F>',
                 f'return v::equal({result},expected);', inputs)


def curve_operation(shape):
    """Group-law checks are weaker than independent curve coordinates.

    Each call includes point construction and validation. Scaling checks every
    point; MSM compares one scalar identity. No group kernel-only timing claim.
    """
    n, operation = shape['elements'], shape['operation']
    xs = [x[0] for x in a.dense(n, seed=261, modulus=a.FR)]
    weights = [x[0] for x in a.dense(n, seed=262, modulus=a.FR)]
    scale = a.dense(1, seed=263, modulus=a.FR)[0][0]
    setup = '''let generator=curve::generator<G>();
      let points=curve::collect(xs,fn(x)=>generator*x);'''
    if operation == 'msm':
        expected = sum(x*y for x, y in zip(xs, weights, strict=True)) % a.FR
        parameters = 'xs:Vector<F>, weights:Vector<F>, expected:F'
        inputs = {'xs': list(map(str, xs)), 'weights': list(map(str, weights)), 'expected': str(expected)}
        body = setup + 'return curve::msm(weights,points)==generator*expected;'
    elif operation in ('vector-scale', 'scale-each'):
        factors = [scale] * n if operation == 'vector-scale' else weights
        expected = [str(x*y % a.FR) for x, y in zip(xs, factors, strict=True)]
        parameters = 'xs:Vector<F>, ' + ('scale:F' if operation == 'vector-scale' else 'weights:Vector<F>')
        parameters += ', expected:Vector<F>'
        inputs = {'xs': list(map(str, xs)), 'expected': expected}
        if operation == 'vector-scale':
            inputs['scale'] = str(scale)
            body = setup + 'let out=curve::scale(points,scale);'
        else:
            inputs['weights'] = list(map(str, weights))
            body = setup + 'let out=curve::scale_each(weights,points);'
        body += '''let mut accepted=curve::length(out)==v::length(expected);
          for i in 0..v::length(xs) {
            accepted=accepted && curve::get(out,i)==generator*v::get(expected,i);
          }
          return accepted;'''
    else:
        raise ValueError(f'unknown curve operation: {operation}')
    program = local('bls12-381.fr', parameters, body, inputs)
    program.source = program.source.replace('fn compute(', '''use zkc::curve as curve;
domain G=group("bls12-381.g1");
fn compute(''')
    program.dependencies = ('core.algebra', 'core.collections')
    program.oracle = 'Python scalar expectations and per-point group-law checks; native group kernels shared, not independent curve arithmetic'
    return program
