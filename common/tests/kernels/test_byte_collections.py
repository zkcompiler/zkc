"""Ordered collection codecs and byte assembly through source, IR and Host."""
import pytest

from entry import Entry
from toolchain import ROOT


@pytest.mark.parametrize('field,codec,order', [
    ('bls12-381.fr', 'be', 'big'), ('ristretto255.scalar', 'le', 'little'),
])
@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_byte_collections(toolchain, journal, directory, field, codec, order, flags):
    source = f'''module sample;
use zkc::bytes as bytes;
use zkc::encoding as encoding;
use zkc::sequence as sequence;
use zkc::vector::{{Vector}};
domain F=field("{field}");
fn encode(values:Vector<F>,byte:index,count:index)->bytes::Bytes {{
  let mut parts=sequence::empty<bytes::Bytes>();
  parts=sequence::append(parts,bytes::repeat(byte,count));
  parts=sequence::append(parts,encoding::fields_{codec}(values));
  parts=sequence::append(parts,bytes::repeat(255,2));
  return bytes::join(parts);
}}
protocol Run roles(P)(values:Vector<F>@P,byte:index@P,count:index@P)
  ->(result:bytes::Bytes@P) {{ return encode(values,byte,count); }}
run Demo=Run;
'''
    modules = [f'--module=zkc::{path.stem}={path}'
               for path in (ROOT / 'libraries/zkc').glob('*.zkc')]
    entry = Entry(toolchain, journal, directory, source, (*flags, *modules))
    for n in (0, 1, 16, 256):
        values = [i * 19 + 5 for i in range(n)]
        expected = bytes([128] * n) + b''.join(v.to_bytes(32, order) for v in values) + b'\xff\xff'
        result = entry.run(f'encode-{n}', {'values': list(map(str, values)), 'byte': 128, 'count': n})
        assert result['result'] == list(expected)
    entry.run('invalid-byte', {'values': [], 'byte': 256, 'count': 0},
              refuses='refused:bytes-element')
    entry.run('oversized', {'values': [], 'byte': 0, 'count': 2**64 - 1},
              refuses='exhausted:wire-bytes')


@pytest.mark.parametrize('group', ['bls12-381.g1', 'edwards25519.prime'])
def test_group_collection_encoding(toolchain, journal, directory, group):
    source = f'''module sample;
use zkc::bytes as bytes;
use zkc::encoding as encoding;
use zkc::curve as curve;
domain G=group("{group}");
fn check()->bool {{
  let g=curve::generator<G>();
  let z=curve::identity<G>();
  let points=curve::append(curve::append(curve::empty<G>(),z),g);
  let expected=bytes::concat(encoding::group_compressed(z),encoding::group_compressed(g));
  require bytes::equal(expected,encoding::groups_compressed(points));
  require bytes::equal(bytes::empty(),encoding::groups_compressed(curve::empty<G>()));
  return true;
}}
protocol Run roles(P)()->(ok:bool@P) {{ let ok @P=check();return ok; }}
run Demo=Run;
'''
    modules = [f'--module=zkc::{path.stem}={path}'
               for path in (ROOT / 'libraries/zkc').glob('*.zkc')]
    entry = Entry(toolchain, journal, directory, source, modules)
    assert entry.run('groups', {})['ok'] is True
