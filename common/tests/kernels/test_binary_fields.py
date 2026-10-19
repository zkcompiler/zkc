"""Characteristic-two fields through source, IR and Host, with refusals.

The expected values come from shift-and-add arithmetic in
`binary_reference.py`; neither compiler operations nor Plonky3 compute them.
Operations that need a prime or odd characteristic are refused at
compilation: two-adic domains, folding by halving, Montgomery residues and
decimal constants above one.
"""
import random

import pytest

from binary_reference import (BASE, CUBIC, cubic_add, cubic_inverse, cubic_mul, inverse,
                              literal, mul, readable)
from entry import Entry
from source_modules import core_packages, library_modules

Y = [0, 1, 0]
Y2 = [0, 0, 1]

SOURCE = f'''module sample;
use zkc::encoding as encoding;
use zkc::bytes as bytes;
use zkc::bytes::{{Bytes}};
use zkc::indices as indices;
use zkc::indices::{{Indices}};
use zkc::vector::{{Vector}};
use zkc::matrix::{{Matrix}};
domain K = field("{BASE}");
domain E = field("{CUBIC}");
math fn square_plus_one<F: Field>(x:F) -> F {{ return x * x + 1; }}
fn base_work(a:K, b:K) -> (K,K,K,K,K,K) {{
  let generator = kernel<K>("field.constant"; "0x1b");
  let one: K = 1;
  return (a * b, a + b, a - b, kernel<K>("field.inverse", a), generator * a, one + one);
}}
fn cubic_work(a:E, b:E, k:K, xs:Vector<E>, m:Matrix<E>)
    -> (E,E,E,E,E,Vector<E>,E,Vector<E>,E,Vector<E>,E) {{
  let y = kernel<E>("field.constant"; "{literal(Y)}");
  let y2 = kernel<E>("field.constant"; "{literal(Y2)}");
  let scaled = kernel<E>("vector.scale", xs, b);
  return (a * b, a + b, kernel<E>("field.inverse", a), kernel<E>("field.embed", k), y * y2,
          scaled, kernel<E>("vector.dot", xs, scaled), kernel<E>("matrix.mul_vector", m, xs),
          kernel<E>("matrix.bilinear", m, xs, xs), map square_plus_one(each xs),
          square_plus_one(a));
}}
fn codec_work(x:E, octets:Indices) -> (Bytes,bool,E,bool,Vector<K>) {{
  let mut raw = bytes::empty();
  for i in 0..indices::length(octets) {{ raw = bytes::append(raw, indices::get(octets, i)); }}
  let (one, y) = encoding::field_from_le<E>(raw);
  let (many, ks) = encoding::fields_from_le<K>(raw);
  return (encoding::field_le(x), one, y, many, ks);
}}
protocol Run roles(P)(a:K@P, b:K@P, c:E@P, d:E@P, xs:Vector<E>@P, m:Matrix<E>@P, raw:Indices@P)
  -> (base:(K,K,K,K,K,K)@P, cubic:(E,E,E,E,E,Vector<E>,E,Vector<E>,E,Vector<E>,E)@P,
      codecs:(Bytes,bool,E,bool,Vector<K>)@P) {{
  let base @P = base_work(a, b);
  let cubic @P = cubic_work(c, d, a, xs, m);
  let codecs @P = codec_work(c, raw);
  return (base=base, cubic=cubic, codecs=codecs);
}}
run Demo = Run;
'''


def matrix(entries):
    return {'rows': '2', 'columns': '2',
            'entries': [[str(r), str(c), readable(a)] for r, c, a in entries]}


def little_endian(words):
    return b''.join(w.to_bytes(8, 'little') for w in words)


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_binary_kernels_match_carry_less_arithmetic(toolchain, journal, directory, flags):
    entry = Entry(toolchain, journal, directory, SOURCE, (*library_modules(*core_packages()), *flags))
    rng = random.Random(2063)

    def word():
        return rng.getrandbits(64) | 2

    def element():
        return [word(), rng.getrandbits(64), rng.getrandbits(64)]

    # x * x^63 wraps to x^4 + x^3 + x + 1; y * y^2 is y + 1.
    cases = [('wrap', 2, 1 << 63, Y, Y2)]
    cases += [(f'random{i}', word(), word(), element(), element()) for i in range(3)]
    for name, a, b, c, d in cases:
        xs = [element(), element()]
        entries = [(0, 1, element()), (1, 0, element())]
        raw = little_endian(c)
        result = entry.run(name, {'a': readable(a), 'b': readable(b), 'c': readable(c),
                                  'd': readable(d), 'xs': readable(xs),
                                  'm': matrix(entries), 'raw': list(raw)})
        assert result['base'] == readable([mul(a, b), a ^ b, a ^ b, inverse(a),
                                           mul(0x1b, a), 0])
        scaled = [cubic_mul(x, d) for x in xs]
        dot = cubic_add(cubic_mul(xs[0], scaled[0]), cubic_mul(xs[1], scaled[1]))
        mv = [cubic_mul(entries[0][2], xs[1]), cubic_mul(entries[1][2], xs[0])]
        bilinear = cubic_add(cubic_mul(xs[0], mv[0]), cubic_mul(xs[1], mv[1]))
        # A pointwise map and a Math function: x * x + 1 adds one to the constant coordinate.
        mapped = [cubic_add(cubic_mul(x, x), [1, 0, 0]) for x in xs]
        assert result['cubic'] == readable([cubic_mul(c, d), cubic_add(c, d), cubic_inverse(c),
                                            [a, 0, 0], [1, 1, 0], scaled, dot, mv, bilinear,
                                            mapped, cubic_add(cubic_mul(c, c), [1, 0, 0])])
        encoded, one, decoded, many, words = result['codecs']
        assert bytes(encoded) == raw
        assert (one, decoded) == (True, readable(c))
        assert (many, words) == (True, readable(c))
    # Every 24-byte pattern is an element; only the length can fail.
    inputs = {'a': '0x2', 'b': '0x3', 'c': readable(Y), 'd': readable(Y),
              'xs': readable([Y, Y2]), 'm': matrix([(0, 0, Y)]), 'raw': list(bytes(20))}
    _, one, decoded, many, words = entry.run('short', inputs)['codecs']
    assert (one, decoded, many, words) == (False, readable([0, 0, 0]), False, [])
    inputs['a'] = '0x0'
    report = entry.run('zero-inverse', inputs, refuses='entry-run-incomplete')
    assert 'zero-inverse' in str(report)
    # Readable values are bit patterns: decimals and noncanonical spellings refuse.
    for bad in ['3', '0x03', '0X3', '0x10000000000000000']:
        entry.run(f'noncanonical-{bad}', {**inputs, 'a': bad}, refuses=True)


REFUSED = '''module sample;
use zkc::encoding as encoding;
use zkc::bytes::{{Bytes}};
use zkc::vector::{{Vector}};
domain K = field("{field}");
fn body(a:K, xs:Vector<K>) -> {result} {{
  let p = kernel<K>("poly.from_coefficients", xs);
  {body}
}}
protocol Run roles(P)(a:K@P, xs:Vector<K>@P) -> (result:{result}@P) {{
  let result @P = body(a, xs);
  return (result=result);
}}
run Demo = Run;
'''


@pytest.mark.parametrize('field', [BASE, CUBIC])
@pytest.mark.parametrize('result, body, code', [
    ('Vector<K>', 'return kernel<K>("poly.even_odd_fold", xs, a, a);', 'TwoAdicField'),
    ('Vector<K>', 'return kernel<K>("poly.coset_evaluate", p, a, 4);', 'TwoAdicField'),
    ('K', 'return kernel<K>("poly.domain_root", 4);', 'TwoAdicField'),
    ('Bytes', 'return encoding::field_montgomery_le(a);', 'binding-implementation'),
    ('K', 'let (ok, x) = encoding::field_from_montgomery_le<K>(encoding::field_le(a)); return x;',
     'binding-implementation'),
    ('K', 'return kernel<K>("field.constant"; "2");', 'interactive-constant'),
    ('K', 'return kernel<K>("field.constant"; "0x1");', 'interactive-constant'),
    ('K', 'return kernel<K>("field.constant"; "0x01b");', 'interactive-constant'),
    ('K', 'let two: K = 2; return two;', 'interactive-constant'),
])
def test_prime_and_odd_characteristic_operations_refuse(toolchain, journal, directory,
                                                         field, result, body, code):
    path = directory / 'refused.zkc'
    path.write_text(REFUSED.format(field=field, result=result, body=body))
    journal.run([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                 f'--module=sample={path}', *library_modules(*core_packages()), 'sample::Demo',
                 f'--output={directory / "refused.zkpkg"}'], refuses=code)


def test_refusal_source_compiles_with_admitted_operations(toolchain, journal, directory):
    # The refusal fixture is otherwise well formed: an admitted body compiles.
    path = directory / 'admitted.zkc'
    path.write_text(REFUSED.format(field=CUBIC, result='K',
                                   body='return kernel<K>("field.constant"; "0x1b") * a;'))
    journal.run([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                 f'--module=sample={path}', *library_modules(*core_packages()), 'sample::Demo',
                 f'--output={directory / "admitted.zkpkg"}'])
