"""A fixed panel of authored Math functions and separate scalar expectations.

These definitions are source text, not an expression language. Shape roles are
fixed before measurements; validation-only shapes must stay out of tuning.
"""
from dataclasses import dataclass
from functools import reduce
from typing import Callable

from . import algebra as a
from .programs import local


def short_expected(f, row, c):
    x, = row
    # Expanded cubic, independently of the source's Horner order.
    return f.add(f.add(f.power(x, 3), f.mul(c[0], f.power(x, 2))),
                 f.add(f.mul(c[1], x), c[2]))


def deep_expected(f, row, c):
    x, = row
    return reduce(f.add, (f.mul(c[i % 2], f.power(x, 11-i)) for i in range(12)), f.power(x, 13))


def wide_expected(f, row, c):
    squares = [f.add(f.power(x, 2), k) for x, k in zip(row, c, strict=True)]
    return f.add(f.mul(squares[0], squares[1]), f.mul(squares[2], squares[3]))


def shared_expected(f, row, c):
    x, y = row
    t = f.add(f.mul(x, y), c[0])
    return reduce(f.add, (f.power(t, 3), f.mul(c[1], t), f.mul(f.power(t, 2), x),
                          f.mul(c[1], x), f.mul(t, y)), f.zero)


def captures_expected(f, row, c):
    x, = row
    return reduce(f.add, (f.mul(f.mul(c[0], c[1]), f.power(x, 2)),
                          f.mul(f.mul(c[2], c[3]), f.power(x, 2)),
                          f.mul(f.mul(c[4], c[5]), x), f.mul(f.mul(c[6], c[7]), x), c[0], c[7]), f.zero)


def inputs_expected(f, row, c):
    return reduce(f.add, (f.mul(row[i], row[j]) for i, j in ((0, 1), (2, 3), (4, 5), (6, 7), (0, 7))), f.zero)


def differences_expected(f, row, c):
    x, y = row
    # (x-y)^2 and (x+y)^2, expanded without the source's shared values.
    xx, yy, xy = f.power(x, 2), f.power(y, 2), f.mul(x, y)
    low = f.add(f.sub(f.add(xx, yy), f.add(xy, xy)), c[0])
    high = f.add(f.add(f.add(xx, yy), f.add(xy, xy)), c[1])
    return f.add(f.mul(low, high), f.sub(xx, yy))


def powers_expected(f, row, c):
    x, y = row
    return f.add(f.mul(f.add(f.power(x, 3), c[0]), f.add(f.power(y, 3), c[0])),
                 reduce(f.add, (f.power(x, 3), f.mul(f.power(x, 2), y),
                                f.mul(f.power(y, 2), x), f.power(y, 3)), f.zero))


@dataclass(frozen=True)
class Expression:
    columns: tuple
    captures: tuple
    body: str
    expected: Callable
    role: str = 'design'


EXPRESSIONS = {
    'short-horner': Expression(('x',), ('c0', 'c1', 'c2'),
                              'return ((x+c0)*x+c1)*x+c2;', short_expected),
    'deep-horner': Expression(('x',), ('c0', 'c1'),
                             'let h0=x; ' + ' '.join(f'let h{i+1}=h{i}*x+c{i % 2};' for i in range(12)) +
                             ' return h12;', deep_expected),
    'wide-independent': Expression(('x', 'y', 'z', 'w'), ('c0', 'c1', 'c2', 'c3'),
                                   'return (x*x+c0)*(y*y+c1)+(z*z+c2)*(w*w+c3);', wide_expected),
    'shared-subexpression': Expression(('x', 'y'), ('c0', 'c1'),
                                      'let t=x*y+c0; let u=t*t+c1; return u*t+u*x+t*y;', shared_expected),
    'capture-heavy': Expression(('x',), tuple(f'c{i}' for i in range(8)),
                                'return ((c0*c1+c2*c3)*x+(c4*c5+c6*c7))*x+c0+c7;', captures_expected),
    'input-heavy': Expression(tuple(f'x{i}' for i in range(8)), (),
                              'return x0*x1+x2*x3+x4*x5+x6*x7+x0*x7;', inputs_expected),
    'difference-products': Expression(('x', 'y'), ('c0', 'c1'),
                                      'let u=x-y; let t=x+y; return (u*u+c0)*(t*t+c1)+u*t;',
                                      differences_expected, 'validation-only'),
    'alternating-powers': Expression(('x', 'y'), ('c0',),
                                     'let a=x*x; let b=y*y; return (a*x+c0)*(b*y+c0)+(a+b)*(x+y);',
                                     powers_expected, 'validation-only'),
}


def expression(shape, *, root=None):
    definition = EXPRESSIONS[shape['expression']]
    f = a.FieldOracle(shape['field'], root=root)
    n, sink = shape['elements'], shape['sink']
    if sink not in ('map', 'sum', 'product'):
        raise ValueError(f'unknown expression sink: {sink}')
    columns = [f.dense(n, 201+i) for i in range(len(definition.columns))]
    captures = f.dense(len(definition.captures), 221)
    rows = [definition.expected(f, row, captures) for row in zip(*columns, strict=True)]
    expected = rows if sink == 'map' else reduce(f.add if sink == 'sum' else f.mul, rows,
                                                f.zero if sink == 'sum' else f.one)
    vectors = [name+'s' for name in definition.columns]
    parameters = ', '.join([*(name+':Vector<F>' for name in vectors),
                            *(name+':F' for name in definition.captures),
                            'expected:' + ('Vector<F>' if sink == 'map' else 'F')])
    arguments = ','.join([*('each '+name for name in vectors), *definition.captures])
    result = f'map term({arguments})'
    if sink != 'map':
        result = f'v::{sink}({result})'
    check = 'v::equal(out,expected)' if sink == 'map' else 'out==expected'
    inputs = {name: list(map(f.encode, values)) for name, values in zip(vectors, columns, strict=True)}
    inputs.update({name: f.encode(value) for name, value in zip(definition.captures, captures, strict=True)})
    inputs['expected'] = list(map(f.encode, expected)) if sink == 'map' else f.encode(expected)
    program = local(shape['field'], parameters, f'let out={result}; return {check};', inputs, root=root)
    formals = ','.join(name+':F' for name in (*definition.columns, *definition.captures))
    program.source = program.source.replace('fn compute(', f'math fn term({formals})->F {{ {definition.body} }}\nfn compute(')
    program.oracle = 'independent Python scalar formula in ' + shape['field'] + '; complete result checked in SDK call'
    return program
