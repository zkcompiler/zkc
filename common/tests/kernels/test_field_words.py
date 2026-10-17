"""KoalaBear coordinate-word codecs through source, IR and Host.

The expected bytes come from integer arithmetic: canonical words are the
residues themselves, Montgomery words are x * 2^32 mod p, and extension
elements are their ascending coordinates. No native code computes them.
"""
import random

import pytest

from entry import Entry
from source_modules import library_modules

P = 2130706433
FIELDS = {'koala-bear': 1, 'koala-bear.ext8-binomial3': 8}


def words(value, montgomery):
    return b''.join((((x << 32) % P) if montgomery else x).to_bytes(4, 'little')
                    for x in value)


def wire(degree, element):
    return str(element[0]) if degree == 1 else [str(x) for x in element]


SOURCE = '''module sample;
use zkc::encoding as encoding;
use zkc::bytes as bytes;
use zkc::bytes::{{Bytes}};
use zkc::indices as indices;
use zkc::indices::{{Indices}};
use zkc::vector::{{Vector}};
domain F=field("{field}");
fn encode(x:F, xs:Vector<F>) -> (Bytes,Bytes,Bytes,Bytes) {{
  return (encoding::field_le(x), encoding::field_montgomery_le(x),
          encoding::fields_le(xs), encoding::fields_montgomery_le(xs));
}}
fn decode(octets:Indices) -> (bool,F,bool,F,bool,Vector<F>,bool,Vector<F>) {{
  let mut raw=bytes::empty();
  for i in 0..indices::length(octets) {{ raw=bytes::append(raw,indices::get(octets,i)); }}
  let (a,x)=encoding::field_from_le<F>(raw);
  let (b,y)=encoding::field_from_montgomery_le<F>(raw);
  let (c,xs)=encoding::fields_from_le<F>(raw);
  let (d,ys)=encoding::fields_from_montgomery_le<F>(raw);
  return (a,x,b,y,c,xs,d,ys);
}}
protocol Run roles(P)(x:F@P, xs:Vector<F>@P, raw:Indices@P)
  -> (encoded:(Bytes,Bytes,Bytes,Bytes)@P, decoded:(bool,F,bool,F,bool,Vector<F>,bool,Vector<F>)@P) {{
  let encoded @P=encode(x,xs);
  let decoded @P=decode(raw);
  return (encoded=encoded, decoded=decoded);
}}
run Demo=Run;
'''


@pytest.mark.parametrize('field', sorted(FIELDS))
@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_coordinate_words(toolchain, journal, directory, field, flags):
    degree = FIELDS[field]
    entry = Entry(toolchain, journal, directory, SOURCE.format(field=field),
                  (*library_modules('zkc'), *flags))
    rng = random.Random(4099 + degree)

    def element():
        return [rng.randrange(P) for _ in range(degree)]

    zero = [0] * degree
    x = element()
    xs = [element() for _ in range(3)] + [[P - 1] * degree, zero]
    for name, raw, montgomery in [('canonical', words(x, False), False),
                                  ('montgomery', words(x, True), True)]:
        result = entry.run(name, {'x': wire(degree, x), 'xs': [wire(degree, v) for v in xs],
                                  'raw': list(raw)})
        canonical, mont, many, many_mont = result['encoded']
        assert bytes(canonical) == words(x, False)
        assert bytes(mont) == words(x, True)
        assert bytes(many) == b''.join(words(v, False) for v in xs)
        assert bytes(many_mont) == b''.join(words(v, True) for v in xs)
        # One element's words decode under both readings; only the matching
        # reading returns the original element.
        a, first, b, second, c, list_first, d, list_second = result['decoded']
        assert (a, b, c, d) == (True, True, True, True)
        assert (second if montgomery else first) == wire(degree, x)
        assert (list_second if montgomery else list_first) == [wire(degree, x)]
    # Words at or above the modulus, and widths that are not whole elements.
    for name, raw in [('modulus', P.to_bytes(4, 'little') * degree),
                      ('high', (2**32 - 1).to_bytes(4, 'little') * degree),
                      ('short', bytes(4 * degree - 1)),
                      ('long', bytes(4 * degree + 1))]:
        result = entry.run(name, {'x': wire(degree, x), 'xs': [], 'raw': list(raw)})
        a, first, b, second, c, list_first, d, list_second = result['decoded']
        assert (a, b, c, d) == (False, False, False, False), name
        assert first == second == wire(degree, zero)
        assert list_first == list_second == []
    entry.run('noncanonical-input', {'x': wire(degree, [P] + [0] * (degree - 1)),
                                     'xs': [], 'raw': []}, refuses=True)
