"""Bounded public-library controls; all Python arithmetic is untimed.

No oracle data files or provider bindings are loaded here. The executing
harness captures this module and algebra.py; Program dependencies capture the
public libraries and their manifests from the selected --source root.
"""
from random import Random

from . import algebra as a
from .programs import local


CURVES = {
    'bls-g1': ('bls12-381.g1', 'bls12-381.fr'),
    'bls-g2': ('bls12-381.g2', 'bls12-381.fr'),
    'bn-g1': ('bn254.g1', 'bn254.fr'),
    'bn-g2': ('bn254.g2', 'bn254.fr'),
    'ristretto': ('ristretto255.group', 'ristretto255.scalar'),
    'edwards': ('edwards25519.prime', 'ristretto255.scalar'),
}


def _imports(program, text, dependencies):
    program.source = program.source.replace('fn compute(', text + '\nfn compute(')
    program.dependencies = dependencies
    return program


def _horner(f, coefficients, point):
    result = f.zero
    for coefficient in reversed(coefficients):
        result = f.add(f.mul(result, point), coefficient)
    return result


def _quotient_coefficients(f, coefficients, point):
    """Synthetic division by X-point, without evaluation-form denominators."""
    result = [f.zero] * (len(coefficients) - 1)
    carry = coefficients[-1]
    for i in range(len(coefficients) - 2, -1, -1):
        result[i] = carry
        carry = f.add(coefficients[i], f.mul(point, carry))
    return result


def relation_rows(shape, *, root):
    """Actual table residuals, including nonzero and inactive assertion slots."""
    from . import stark

    height, width = shape['height'], shape['width']
    if height < 1 or width < 1 or shape['data'] not in ('valid', 'perturbed'):
        raise ValueError('invalid relation row control')
    bundle, initial, final, trace = stark.recurrence(root, shape)
    trace = trace.copy()
    if shape['data'] == 'perturbed':
        trace[(height//2)*width] = (trace[(height//2)*width]+1) % a.P
    expected = []
    for row in range(height):
        for col in range(width):
            current = trace[row*width+col]
            if row+1 < height:
                following = trace[(row+1)*width+col]
                if shape.get('constraint') == 'coupled':
                    neighbor = trace[row*width+(col+1) % width]
                    previous = trace[row*width+(col-1) % width]
                    transition = following-pow(current, shape['constraint_degree']-1, a.P)*neighbor-previous-col-1
                else:
                    transition = following-current*current-col-1
            else:
                transition = 0
            expected.extend(((current-initial[col]) % a.P if row == 0 else 0,
                             (current-final[col]) % a.P if row+1 == height else 0,
                             transition % a.P))
    program = local('koala-bear',
                    'trace:Vector<F>, public_data:Vector<F>, height:index, expected:Vector<F>',
                    '''let out=kernel<F,0>("relation.table_rows",trace,v::empty<F>(),public_data,height;Trace);
                      return v::equal(out,expected);''',
                    {'trace': list(map(str, trace)), 'public_data': list(map(str, initial+final)),
                     'height': str(height), 'expected': list(map(str, expected))}, root=root)
    _imports(program, 'domain Trace=bundle(asset trace);', ('core.collections',))
    program.assets = {'trace': bundle}
    program.support = (root/'compiler/adapters/ring_arena.py',)
    program.oracle = ('Independent complete row-major boundary/transition residuals from the input trace; '
                      'inactive slots are zero, perturbed traces retain nonzero residuals. Actual Bundle '
                      'table evaluator; includes admission, full result checking and Host, not a proof or kernel-only time')
    return program


def kzg(shape, *, root):
    """Actual generic KZG evaluation algebra, including its checked carriers."""
    field, n = shape['field'], shape['elements']
    operation, kind = shape['operation'], shape['point_kind']
    order = shape.get('order', 'natural')
    if operation not in ('evaluate', 'quotient') or kind not in ('on-domain', 'off-domain'):
        raise ValueError('unknown KZG operation or point kind')
    if order not in ('natural', 'bit-reversed'):
        raise ValueError('unknown KZG domain order')
    f = a.FieldOracle(field, root=root)
    if field not in ('bls12-381.fr', 'koala-bear') or n < 1 or n & (n-1):
        raise ValueError('KZG panel requires a supported prime field and power-of-two size')
    generator = pow(7, (a.FR-1)//n, a.FR) if field == 'bls12-381.fr' else \
                pow(1791270792, (1 << 24)//n, a.P)
    assert pow(generator, n, f.modulus) == 1
    assert n == 1 or pow(generator, n//2, f.modulus) != 1
    points = [(pow(generator, i, f.modulus),) for i in range(n)]
    if order == 'bit-reversed' and n > 1:
        bits = n.bit_length()-1
        points = [points[int(f'{i:0{bits}b}'[::-1], 2)] for i in range(n)]
    coefficients = f.dense(n, 401)
    at = points[n//2] if kind == 'on-domain' else (13,)
    assert (f.power(at, n) == f.one) == (kind == 'on-domain')
    values = [_horner(f, coefficients, x) for x in points]
    y = _horner(f, coefficients, at)
    # A singleton polynomial has the zero quotient, evaluated at its one root.
    quotient = _quotient_coefficients(f, coefficients, at)
    expected = [y] if operation == 'evaluate' else \
               [y] + [_horner(f, quotient, x) for x in points]
    constructor = 'two_adic' if order == 'natural' else 'two_adic_bit_reversed'
    setup = f'''let unity=evaluation::{constructor}(n,generator);
      let input=evaluation::evaluations(unity,values);'''
    body = ('let out=v::fill(kzg::evaluate(input,at),1);' if operation == 'evaluate' else
            '''let (quotient,value)=kzg::quotient(input,at);
              let out=v::concat(v::fill(value,1),quotient);''')
    program = local(field, 'values:Vector<F>, n:index, generator:F, at:F, expected:Vector<F>',
                    setup + body + 'return v::equal(out,expected);',
                    {'values': list(map(f.encode, values)), 'n': str(n),
                     'generator': str(generator), 'at': f.encode(at),
                     'expected': list(map(f.encode, expected))}, root=root)
    _imports(program, 'use kzg as kzg;\nuse zkc::evaluation_domain as evaluation;',
             ('commitments.kzg',))
    program.oracle = ('Independent integer coefficients, Horner and synthetic division; '
                      'every quotient entry including the on-domain derivative checked. '
                      'Actual generic commitments/kzg source and checked EvaluationDomain/Evaluations; '
                      f'{order} stored domain order; '
                      'no commitment, pairing, trusted setup or security claim')
    return program


def curve_family(shape, *, root):
    """Scalar expectations plus explicitly weaker shared-provider group laws."""
    group, field = CURVES[shape['curve']]
    n, form = shape['elements'], shape['form']
    f = a.FieldOracle(field, root=root)
    xs = [x[0] for x in f.dense(n, 411)]
    weights = [x[0] for x in f.dense(n, 412)]
    # Include identity and unit factors in the non-singleton panels.
    if n > 1:
        xs[:2], weights[:2] = [0, 1], [1, 0]
    scale = f.dense(1, 413)[0][0]
    setup = '''let generator=curve::generator<G>();'''
    if form == 'fixed-base':
        expected = weights
        body = 'let out=curve::collect(weights,fn(weight)=>generator*weight);'
    else:
        setup += 'let points=curve::collect(xs,fn(x)=>generator*x);'
        if form == 'shared-scalar':
            expected = [x*scale % f.modulus for x in xs]
            body = 'let out=curve::scale(points,scale);'
        elif form == 'per-point':
            expected = [x*w % f.modulus for x, w in zip(xs, weights, strict=True)]
            body = 'let out=curve::scale_each(weights,points);'
        elif form == 'msm':
            expected = [sum(x*w for x, w in zip(xs, weights, strict=True)) % f.modulus]
            body = 'let out=curve::append(curve::empty<G>(),curve::msm(weights,points));'
        else:
            raise ValueError(f'unknown curve form: {form}')
    # The fixed-base check also invokes addition, rather than repeating the
    # exact same multiplication on both sides. It still shares the provider.
    body += '''let mut accepted=curve::length(out)==v::length(expected);
      for i in 0..v::length(expected) {
        accepted=accepted && curve::get(out,i)+generator==generator*(v::get(expected,i)+1);
      }
      return accepted;'''
    program = local(field, 'xs:Vector<F>, weights:Vector<F>, scale:F, expected:Vector<F>',
                    setup + body,
                    {'xs': list(map(str, xs)), 'weights': list(map(str, weights)),
                     'scale': str(scale), 'expected': list(map(str, expected))}, root=root)
    _imports(program, f'use zkc::curve as curve;\ndomain G=group("{group}");',
             ('core.algebra', 'core.collections'))
    program.oracle = ('Python scalar expectations modulo the selected group order; '
                      'every output point checked by a shared-provider group-law self-consistency oracle, '
                      'not independent curve coordinates. Fixed-base means authored generator multiplication, '
                      'not a dedicated fixed-base kernel. SDK/run includes point construction and all checks; '
                      'no kernel-only timing, constant-time comparison or security claim')
    return program


def quotient_split(shape, *, root):
    """Coefficient blocks checked by an independent integer transform in Python."""
    degree, n, width, count = (shape[key] for key in
                              ('extension_degree', 'elements', 'block_width', 'blocks'))
    form = shape['form']
    if form not in ('library', 'reference'):
        raise ValueError('unknown quotient split form')
    if degree not in (1, 4, 8) or n < 1 or n & (n-1) or width < 0 or count < 0:
        raise ValueError('invalid quotient split shape')
    if width*count < n:
        raise ValueError('quotient split capacity')
    field = 'koala-bear' + (f'.ext{degree}-binomial3' if degree != 1 else '')
    f = a.FieldOracle(field, root=root)
    shift = f.dense(1, 471)[0]
    coefficients = f.dense(n, 472)
    values = a.coset(coefficients, shift, n)
    padded = coefficients + [f.zero] * (width*count-n)
    expected = [value for block in range(count)
                for value in a.coset(padded[block*width:(block+1)*width], shift, n)]
    if form == 'library':
        body = 'let out=air_poly::split_quotient(values,shift,n,width,count);'
    else:
        # Keep the original source form as an explicit dataflow control.
        body = '''let coefficients=polynomial::coefficients(coset::interpolate(coset::word(values,shift)));
          let capacity=width*count;
          require !(zkc::indices::less(capacity,v::length(coefficients)));
          let padded=v::concat(coefficients,v::fill<F>(0,capacity-v::length(coefficients)));
          let mut out=v::empty<F>();
          for block in 0..count {
            let p=polynomial::from_coefficients(v::slice(padded,block*width,width));
            out=v::concat(out,coset::values(coset::evaluate_coset(p,shift,n)));
          }'''
    program = local(field, 'values:Vector<F>, shift:F, n:index, width:index, count:index, expected:Vector<F>',
                    body+'return v::equal(out,expected);',
                    {'values': list(map(f.encode, values)), 'shift': f.encode(shift), 'n': str(n),
                     'width': str(width), 'count': str(count), 'expected': list(map(f.encode, expected))},
                    root=root)
    _imports(program, 'use air::polynomial as air_poly;\nuse zkc::coset as coset;\n'
             'use zkc::polynomial as polynomial;', ('relations.air',))
    program.oracle = ('Independent integer polynomial coefficients and coset transforms of each '
                      'coefficient block; every coordinate checked, including representation padding. '
                      'Current split_quotient versus authored per-block evaluation and growing concatenation. '
                      'SDK/run includes interpolation, adaptation, full result check and Host costs; '
                      'no quotient divisibility or degree proof')
    return program


def sparse_matrix(shape, *, root):
    """Exact nnz with balanced, clustered or deliberately empty-row patterns."""
    rows, columns, nnz = (shape[key] for key in ('rows', 'columns', 'nnz'))
    distribution, direction = shape['distribution'], shape['direction']
    if min(rows, columns) < 1 or not 0 <= nnz <= rows*columns:
        raise ValueError('invalid sparse dimensions or nnz')
    if distribution == 'uniform':
        coordinates = [(r, (7*r + layer) % columns)
                       for layer in range(columns) for r in range(rows)]
    elif distribution == 'clustered':
        hot_rows, hot_columns = max(1, rows//8), max(1, columns//4)
        coordinates = sorted(((r, c) for r in range(rows) for c in range(columns)),
                             key=lambda rc: (rc[0]//hot_rows, rc[1]//hot_columns, *rc))
    elif distribution == 'empty-rows':
        coordinates = [(r, (7*r + layer) % columns)
                       for layer in range(columns) for r in range(0, rows, 2)]
    else:
        raise ValueError(f'unknown sparse distribution: {distribution}')
    if nnz > len(coordinates):
        raise ValueError('nnz exceeds the selected distribution capacity')
    if direction not in ('forward', 'transpose', 'bilinear'):
        raise ValueError(f'unknown sparse direction: {direction}')
    field = shape.get('field', 'bls12-381.fr')
    f = a.FieldOracle(field, root=root)
    rng = Random(421)
    def coefficient():
        value = (rng.randrange(1, f.modulus),) + tuple(rng.randrange(f.modulus)
                                                     for _ in range(f.degree-1))
        return value
    entries = [(r, c, coefficient()) for r, c in sorted(coordinates[:nnz])]
    xs = f.dense(rows if direction == 'transpose' else columns, 422)
    expected = [f.zero] * (columns if direction == 'transpose' else rows)
    for r, c, value in entries:
        output, source = (c, r) if direction == 'transpose' else (r, c)
        expected[output] = f.add(expected[output], f.mul(value, xs[source]))
    inputs = {'matrix': {'rows': str(rows), 'columns': str(columns),
                         'entries': [[str(r), str(c), f.encode(value)] for r, c, value in entries]},
              'xs': list(map(f.encode, xs))}
    parameters = 'matrix:mat::Matrix<F>, xs:Vector<F>'
    if direction == 'bilinear':
        left = f.dense(rows, 423)
        total = f.zero
        for x, y in zip(left, expected, strict=True):
            total = f.add(total, f.mul(x, y))
        expected = [total]
        inputs['left'] = list(map(f.encode, left))
        parameters += ', left:Vector<F>'
        expression = 'v::fill(mat::bilinear(matrix,left,xs),1)'
    else:
        operation = 'multiply' if direction == 'forward' else 'transpose_multiply'
        expression = f'mat::{operation}(matrix,xs)'
    inputs['expected'] = list(map(f.encode, expected))
    program = local(field, parameters+', expected:Vector<F>',
                    f'let out={expression}; return v::equal(out,expected);', inputs, root=root)
    _imports(program, 'use zkc::matrix as mat;', ('core.collections',))
    program.oracle = ('Independent Python finite-field sparse contraction; exact dimensions and nonzero-entry count, '
                      'unique sorted coordinates, all output entries including empty rows/columns checked; '
                      'public matrix contraction with default capacities, not an R1CS proof')
    return program


def opening_quotient(shape, *, root):
    """Checked deep_columns and an explicit per-opening quotient/accumulate loop."""
    degree, height, width, count = (shape[key] for key in
                                   ('extension_degree', 'height', 'width', 'openings'))
    kind, form = shape['point_kind'], shape['form']
    if kind not in ('repeated', 'distinct', 'mixed') or form not in ('library', 'reference'):
        raise ValueError('unknown opening point kind or form')
    if count > height or width < 1 or count < 0:
        raise ValueError('invalid opening count or width')
    field = 'koala-bear' + (f'.ext{degree}-binomial3' if degree != 1 else '')
    f = a.FieldOracle(field, root=root)
    shift, zeta, ratio, first = f.dense(4, 431)
    assert shift != f.zero and ratio != f.zero and first != f.zero
    assert f.power(zeta, height) != f.power(shift, height)
    coefficients = [f.dense(height, 432+column) for column in range(width)]
    columns = [a.coset(cs, shift, height) for cs in coefficients]
    selected = [(3*i+width-1) % width for i in range(count)]
    pattern = (0, 0, 1, 0, 1, 1, 2, 2)
    rotations = [0 if kind == 'repeated' else pattern[i % len(pattern)] if kind == 'mixed' else i
                 for i in range(count)]
    omega = pow(1791270792, (1 << 24)//height, a.P)
    points = [tuple(x*pow(omega, rotation, a.P) % a.P for x in zeta) for rotation in rotations]
    claims = [_horner(f, coefficients[column], point)
              for column, point in zip(selected, points, strict=True)]
    initial = f.dense(height, 451)
    expected, weight = initial.copy(), first
    for column, point in zip(selected, points, strict=True):
        quotient = a.coset(_quotient_coefficients(f, coefficients[column], point), shift, height)
        expected = [f.add(value, f.mul(weight, q))
                    for value, q in zip(expected, quotient, strict=True)]
        weight = f.mul(weight, ratio)
    # Both source forms construct and validate the same public checked views.
    setup = '''let geometry=coset::coset_domain(shift,height);
      let batch=coset::column_batch(geometry,width,xs);
      let descriptors=claims::checked(selected,rotations,claimed);
      let bound=opening::bind_openings(geometry,width,height,zeta,descriptors);
      let accumulator=opening::vector_accumulator(geometry,ratio,initial,first);'''
    if form == 'library':
        body = '''let reduced=opening::deep_columns(batch,bound,accumulator);
          let out=opening::vector_values(reduced);
          let next=opening::vector_weight(reduced);'''
    else:
        body = '''let mut out=opening::vector_values(accumulator);
          let mut next=opening::vector_weight(accumulator);
          for i in 0..idx::length(selected) {
            let column=coset::batch_column(batch,idx::get(selected,i));
            let at=zeta*coset::point<F>(1,height,idx::get(rotations,i));
            let quotient=coset::opening_quotient(column,shift,at,v::get(claimed,i));
            out=v::accumulate(out,quotient,next);
            next=next*ratio;
          }'''
    program = local(field,
                    'xs:Vector<F>, width:index, height:index, shift:F, selected:idx::Indices, '
                    'rotations:idx::Indices, claimed:Vector<F>, zeta:F, ratio:F, initial:Vector<F>, '
                    'first:F, expected:Vector<F>',
                    setup + body + 'return v::equal(v::append(out,next),expected);',
                    {'xs': [f.encode(x) for column in columns for x in column],
                     'width': str(width), 'height': str(height), 'shift': f.encode(shift),
                     'selected': list(map(str, selected)), 'rotations': list(map(str, rotations)),
                     'claimed': list(map(f.encode, claims)), 'zeta': f.encode(zeta),
                     'ratio': f.encode(ratio), 'initial': list(map(f.encode, initial)),
                     'first': f.encode(first), 'expected': list(map(f.encode, expected+[weight]))}, root=root)
    _imports(program, 'use zkc::coset as coset;\nuse zkc::opening as opening;\n'
             'use zkc::opening_claims as claims;', ('core.collections', 'core.polynomial'))
    program.oracle = ('Independent dense coefficients, integer coset evaluations, Horner claims and '
                      'synthetic-division weighted quotient expectations; every coordinate and final weight '
                      'checked. Current deep_columns versus explicit quotient+accumulate, including checked '
                      'setup, validation and output construction inside SDK/run; '
                      'no commitment authentication, timing benefit or security claim')
    return program
