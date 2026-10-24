"""Separately named SDK/run operation controls, including source validation."""
from functools import reduce

from . import algebra as a
from .programs import local


def literal(shape, *, root):
    """Repeated reached literal sites versus already decoded operands."""
    f = a.FieldOracle(shape['field'], root=root)
    trips, form = shape['trips'], shape['form']
    if trips < 0 or form not in ('constant', 'operand'):
        raise ValueError('invalid literal control')
    if 'elements' in shape:
        n = shape['elements']
        if n < 1 or f.degree != 1 or f.binary:
            raise ValueError('vector literal controls require a nonempty prime-field vector')
        values = f.dense(n, 482)
        attributes = ','.join(f'"{f.encode(value)}"' for value in values)
        expression = f'kernel<F>("vector.constant"; {attributes})' if form == 'constant' else 'value'
        expected = [f.encode(f.mul(value, (trips % f.modulus,))) for value in values]
        program = local(shape['field'], 'value:Vector<F>, trips:index, expected:Vector<F>',
                        f'''let mut total=v::fill<F>(0,v::length(value));
                          for i in 0..trips {{ total=v::add(total,{expression}); }}
                          return v::equal(total,expected);''',
                        {'value': list(map(f.encode, values)), 'trips': str(trips),
                         'expected': expected}, root=root)
        program.oracle = ('Independent prime-field repeated vector addition; every output checked; '
                          'identical decoded inputs across forms. Repeated-reach interpretation requires '
                          'vector.constant inside the exported loop and reached-site counts; compiler '
                          'invariant hoisting would invalidate it. SDK/run includes checking and Host costs')
        return program
    value = f.dense(1, 481)[0]
    # Decimal literals in prime extensions denote a base-field embedding.
    if not f.binary:
        value = (value[0],) + (0,)*(f.degree-1)
        attribute = str(value[0])
    else:
        attribute = a.binary_reference(f.support[0]).literal(list(value) if f.degree > 1 else value[0])
    expected = f.zero
    for _ in range(trips):
        expected = f.add(expected, value)
    expression = f'kernel<F>("field.constant"; "{attribute}")' if form == 'constant' else 'value'
    program = local(shape['field'], 'value:F, trips:index, expected:F',
                    f'''let mut total:F=0;
                      for i in 0..trips {{ total=total+{expression}; }}
                      return total==expected;''',
                    {'value': f.encode(value), 'trips': str(trips), 'expected': f.encode(expected)},
                    root=root)
    program.oracle = ('Independent finite-field repeated addition; same literal value and trip count '
                      'across source forms. Ordered Local loop; exported call counts must confirm '
                      'whether the compiler retained the literal site. New SDK calls reset reached-site '
                      'preparation; includes arithmetic, result checking and Host costs, not parse-only time')
    return program


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


def _bn254_coset(coefficients, shift, size):
    """Independent integer radix-two evaluation in natural coset order."""
    modulus = a.BN254
    values = [0] * size
    bits = size.bit_length() - 1
    power = 1
    for i, coefficient in enumerate(coefficients):
        index = int(f'{i:0{bits}b}'[::-1], 2) if bits else 0
        values[index] = coefficient * power % modulus
        power = power * shift % modulus
    width = 2
    while width <= size:
        root = pow(5, (modulus - 1) // width, modulus)
        for start in range(0, size, width):
            twiddle = 1
            for j in range(width // 2):
                left = values[start + j]
                right = values[start + j + width // 2] * twiddle % modulus
                values[start + j] = (left + right) % modulus
                values[start + j + width // 2] = (left - right) % modulus
                twiddle = twiddle * root % modulus
        width *= 2
    return values


def coefficient_batch(shape):
    """BN254 coefficient prefixes versus explicit padded per-column FFTs."""
    height, width, size = shape['height'], shape['width'], shape['evaluation_size']
    form, shift = shape['form'], shape['shift']
    if (type(height) is not int or type(width) is not int or type(size) is not int
            or height < 1 or width < 1 or height > size
            or size & (size - 1) or size > 1 << 28
            or type(shift) is not int or not 0 < shift < a.BN254
            or form not in ('batch', 'padded-columns')):
        raise ValueError('invalid BN254 coefficient batch control')
    columns = [[x[0] for x in a.dense(height, seed=351 + column, modulus=a.BN254)]
               for column in range(width)]
    expected = [value for column in columns for value in _bn254_coset(column, shift, size)]
    if form == 'batch':
        body = 'let out=coset::evaluate_batch(xs,width,height,shift,size);'
    else:
        # from_coefficients trims trailing zeros, so ordinary polynomial
        # evaluation would erase this control's explicit full-length padding.
        # Width-one evaluate_batch preserves the supplied coefficient extent.
        body = '''let padding=v::fill<F>(0,size-height);
          let mut out=v::empty<F>();
          for column in 0..width {
            let prefix=v::slice(xs,column*height,height);
            let padded=v::concat(prefix,padding);
            let values=coset::evaluate_batch(padded,1,size,shift,size);
            out=v::concat(out,values);
          }'''
    program = local('bn254.fr', 'xs:Vector<F>, width:index, height:index, shift:F, size:index, expected:Vector<F>',
                    body + 'return v::equal(out,expected);',
                    {'xs': [str(value) for column in columns for value in column],
                     'width': str(width), 'height': str(height), 'shift': str(shift),
                     'size': str(size), 'expected': list(map(str, expected))})
    program.source = program.source.replace('fn compute(', 'use zkc::coset as coset;\nfn compute(')
    program.dependencies = ('core.collections', 'core.polynomial')
    program.oracle = ('Independent modular Python radix-two evaluation of BN254 coefficient blocks; '
                      'every output checked in column-major order. Same input polynomial and output '
                      'across batch and explicitly padded width-one FFT controls; source padding, '
                      'slices, concatenation, equality and Host costs remain inside SDK/run. '
                      'Default capacities; no native roundtrip or kernel-only timing')
    return program


def coset_point(shape):
    """Matched point-major results for three explicit algorithm strategies.

    ``coefficients`` repeats interpolation for every point and column.
    ``reused-coefficients`` interpolates once per column, evaluates all points,
    and transposes its column-major results. Both use native Horner. The library
    form uses opening_claims, which delegates to evaluate_columns. All source
    forms start with the same evaluation words and include their own setup.
    """
    degree, height, width = shape['extension_degree'], shape['height'], shape['width']
    count, form, kind = shape['points'], shape['form'], shape['point_kind']
    if form not in ('coefficients', 'library', 'reused-coefficients'):
        raise ValueError(f'unknown coset point form: {form}')
    if kind not in ('off-domain', 'on-domain'):
        raise ValueError(f'unknown coset point kind: {kind}')
    field = 'koala-bear' + (f'.ext{degree}-binomial3' if degree != 1 else '')
    f = a.FieldOracle(field)
    shift, = f.dense(1, 311)
    coefficients = [f.dense(height, 312 + column) for column in range(width)]
    columns = [a.coset(cs, shift, height) for cs in coefficients]
    if kind == 'on-domain':
        if count > height:
            raise ValueError('on-domain point count exceeds height')
        root = pow(1791270792, (1 << 24) // height, a.P)
        points = [tuple(x * pow(root, row, a.P) % a.P for x in shift)
                  for row in range(count)]
    else:
        points = f.dense(count, 331)
        assert len(set(points)) == count
        assert all(f.power(point, height) != f.power(shift, height) for point in points)

    def horner(cs, point):
        result = f.zero
        for coefficient in reversed(cs):
            result = f.add(f.mul(result, point), coefficient)
        return result

    expected = [horner(cs, point) for point in points for cs in coefficients]
    interpolate = '''let values=v::slice(xs,column*height,height);
      let p=coset::interpolate(coset::word(values,shift));'''
    if form == 'library':
        body = '''let batch=coset::column_batch(coset::coset_domain(shift,height),width,xs);
          let mut out=v::empty<F>();
          for i in 0..v::length(points) {
            out=v::concat(out,opening::opening_claims(batch,v::get(points,i)));
          }'''
    elif form == 'coefficients':
        body = '''let mut out=v::empty<F>();
          for i in 0..v::length(points) {
            let point=v::get(points,i);
            for column in 0..width {''' + interpolate + '''
              out=v::append(out,polynomial::evaluate(p,point));
            }
          }'''
    else:
        body = '''let mut columns=v::empty<F>();
          for column in 0..width {''' + interpolate + '''
            for i in 0..v::length(points) {
              columns=v::append(columns,polynomial::evaluate(p,v::get(points,i)));
            }
          }
          let out=v::transpose(columns,width,v::length(points));'''
    program = local(field, 'xs:Vector<F>, width:index, height:index, shift:F, points:Vector<F>, expected:Vector<F>',
                    body + 'return v::equal(out,expected);',
                    {'xs': [f.encode(x) for column in columns for x in column],
                     'width': str(width), 'height': str(height), 'shift': f.encode(shift),
                     'points': list(map(f.encode, points)), 'expected': list(map(f.encode, expected))})
    program.source = program.source.replace('fn compute(',
        'use zkc::coset as coset;\nuse zkc::opening as opening;\n'
        'use zkc::polynomial as polynomial;\nfn compute(')
    program.dependencies = ('core.collections', 'core.polynomial')
    strategies = {
        'coefficients': 'repeated interpolation per point and column, then native Horner',
        'library': 'direct opening_claims per point on one checked batch',
        'reused-coefficients': 'one interpolation per column, many native Horner evaluations and output transpose',
    }
    program.oracle = ('Independent integer coefficients, coset inputs and Horner expectations; '
                      'every coordinate checked in point-major order; ' + strategies[form] +
                      '; SDK/run includes setup, validation, output construction and Host costs')
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
