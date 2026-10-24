"""Registered residue fields through source, native codecs and both relation readers.

Facts and expected values are independent integer arithmetic. Compiled source
uses the ordinary Entry Host; no backend value supplies its own expectation.
"""
from copy import deepcopy
from hashlib import sha256
import json

import pytest

from binomial_reference import Binomial, FIELDS, P, PLONKY3_FIELDS
from entry import Entry

NEW_FIELDS = ('baby-bear', 'baby-bear.ext4-binomial11',
              'goldilocks', 'goldilocks.ext2-binomial7')
FLAGS = ((), ('--no-simplify',), ('--release-storage',))
ROOTS = {'baby-bear': (440564289, 27), 'goldilocks': (1753635133440165772, 32)}


def wire(f, value):
    return str(value[0]) if f.degree == 1 else list(map(str, value))


def dense(f, seed):
    return [(f.modulus - seed * (i + 1)) % f.modulus for i in range(f.degree)]


@pytest.mark.parametrize('field', ('baby-bear.ext4-binomial11', 'goldilocks.ext2-binomial7'))
@pytest.mark.parametrize('flags', FLAGS)
def test_declared_base_embedding_and_pointwise_composition(
        toolchain, journal, directory, field, flags):
    f = PLONKY3_FIELDS[field]
    source = f'''module sample;
domain K=field("{field.split('.')[0]}");
domain F=field("{field}");
type Vector<E:Field>=builtin("vector",E);
math fn square_plus_one<E:Field>(x:E)->E {{ return x*x+1; }}
fn work(k:K,ks:Vector<K>,x:F,xs:Vector<F>)->(F,Vector<F>,F,Vector<F>,F) {{
  let embedded=kernel<F>("field.embed",k);
  let mapped=map square_plus_one(each xs);
  return(embedded,kernel<F>("vector.embed",ks),x*embedded,mapped,
         kernel<F>("vector.sum",mapped));
}}
protocol Run roles(P)(k:K@P,ks:Vector<K>@P,x:F@P,xs:Vector<F>@P)
    ->(result:(F,Vector<F>,F,Vector<F>,F)@P) {{ return work(k,ks,x,xs); }}
entry fn Demo(inputs:Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    k = f.modulus - 1
    x, y = dense(f, 3), dense(f, 7)
    mapped = [f.add(f.mul(v, v), f.ONE) for v in (x, y)]
    data = {'k': str(k), 'ks': ['0', str(k)], 'x': wire(f, x),
            'xs': [wire(f, x), wire(f, y)]}
    assert entry.run('embedding-and-map', data)['result'] == [
        wire(f, f.embed(k)), [wire(f, f.ZERO), wire(f, f.embed(k))],
        wire(f, f.mul(x, f.embed(k))), [wire(f, v) for v in mapped],
        wire(f, f.add(*mapped))]
    data['xs'] = []
    result = entry.run('empty-map-and-sum', data)['result']
    assert result[-2:] == [[], wire(f, f.ZERO)]


@pytest.mark.parametrize('field', NEW_FIELDS)
@pytest.mark.parametrize('flags', FLAGS)
def test_values_transport_canonical_words_and_full_width_literals(
        toolchain, journal, directory, field, flags):
    f = PLONKY3_FIELDS[field]
    # Direct numeric source literals, scalar/list attributes and natural casts
    # must all use the full characteristic, including above 2^53 and 2^63.
    high = f.modulus - 1
    source = f'''module sample;
domain F=field("{field}");
type Vector<E:Field>=builtin("vector",E);
type Matrix<E:Field>=builtin("matrix",E);
type Bytes=builtin("bytes");
fn inspect(x:F,xs:Vector<F>,m:Matrix<F>,raw:Bytes)
    ->(F,Vector<F>,Matrix<F>,Bytes,Bytes,bool,F,bool,Vector<F>,Vector<F>,F,F) {{
  let (ok,y)=kernel<F>("encoding.field_from_le",raw);
  let (many,ys)=kernel<F>("encoding.fields_from_le",raw);
  let literal:F={high};
  let constants=kernel<F>("vector.constant"; "0","1","{high}");
  let natural=kernel<F>("field.from_index",18446744073709551615);
  return(x,xs,m,kernel<F>("encoding.field_le",x),kernel<F>("encoding.fields_le",xs),
         ok,y,many,ys,constants,literal,natural);
}}
protocol Run roles(P,V)(x:F@P,xs:Vector<F>@P,m:Matrix<F>@P,raw:Bytes@P)
    ->(result:(F,Vector<F>,Matrix<F>,Bytes,Bytes,bool,F,bool,Vector<F>,Vector<F>,F,F)@V) {{
  let received=send P->V((x,xs,m,raw));
  let result @V=inspect(received.0,received.1,received.2,received.3);
  return(result=result);
}}
entry fn Demo(inputs:Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, flags)
    boundaries = [0, 1, 2**32, 2**53 + 1, 2**63, high]
    boundaries = [x for x in boundaries if x < f.modulus]
    xs = [f.embed(x) for x in boundaries] + [dense(f, 17)]
    m = {'rows': '2', 'columns': '2',
         'entries': [['0', '1', wire(f, dense(f, 11))],
                     ['1', '0', wire(f, dense(f, 13))]]}
    x = dense(f, 3)
    data = {'x': wire(f, x), 'xs': [wire(f, v) for v in xs], 'm': m}

    def run(name, raw, **changes):
        return entry.run_roles(name, {'P': data | {'raw': list(raw)} | changes, 'V': {}})

    result = run('nonbase-roundtrip', f.coordinates(x))
    assert result['P'] == {}
    out = result['V']['result']
    assert out == [data['x'], data['xs'], m, list(f.coordinates(x)),
                   list(b''.join(f.coordinates(v) for v in xs)),
                   True, wire(f, x), True, [wire(f, x)],
                   [wire(f, f.embed(v)) for v in [0, 1, high]], wire(f, f.embed(high)),
                   wire(f, f.embed(2**64 - 1))]
    packed = b''.join(f.coordinates(v) for v in xs)
    out = run('whole-vector', packed)['V']['result']
    assert out[5:9] == [False, wire(f, f.ZERO), True, data['xs']]
    out = run('empty-vector', b'')['V']['result']
    assert out[5:9] == [False, wire(f, f.ZERO), True, []]
    width = f.coordinate_bytes * f.degree
    malformed = [('modulus', f.modulus.to_bytes(f.coordinate_bytes, 'little') * f.degree),
                 ('all-ones', bytes([255]) * width), ('short', bytes(width - 1)),
                 ('trailing', bytes(width + 1))]
    for name, raw in malformed:
        out = run(name, raw)['V']['result']
        assert out[5:9] == [False, wire(f, f.ZERO), False, []]
    for i, bad in enumerate([str(f.modulus), '00', '-1', str(2**64)]):
        invalid = bad if f.degree == 1 else [bad] + ['0'] * (f.degree - 1)
        entry.run_roles(f'noncanonical-input-{i}',
                        {'P': data | {'x': invalid, 'raw': []}, 'V': {}}, refuses=True)
    if f.degree > 1:
        for n in (f.degree - 1, f.degree + 1):
            entry.run_roles(f'coordinate-count-{n}',
                            {'P': data | {'x': ['1'] * n, 'raw': []}, 'V': {}}, refuses=True)


@pytest.mark.parametrize('field', NEW_FIELDS)
def test_base_subgroup_roots_and_operational_limit(
        toolchain, journal, directory, field):
    f = PLONKY3_FIELDS[field]
    root, log = ROOTS[field.split('.')[0]]
    assert pow(root, 1 << log, f.modulus) == 1
    assert pow(root, 1 << (log - 1), f.modulus) == f.modulus - 1
    source = f'''module sample;
domain F=field("{field}");
fn root(n:index)->F {{ return kernel<F>("poly.domain_root",n); }}
protocol Run roles(P)(n:index@P)->(result:F@P) {{ return root(n); }}
entry fn Demo(inputs:Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source)
    # Native domain operations retain their operational element cap, including
    # scalar root requests. The C++ contract test checks the larger mathematical
    # maximum directly without allocating it.
    for bits in (0, 1, 3, 10):
        expected = pow(root, 1 << (log - bits), f.modulus)
        assert entry.run(f'root-{bits}', {'n': 1 << bits})['result'] == wire(f, f.embed(expected))
    for n in (0, 3, 1 << log, 1 << (log + 1)):
        entry.run(f'invalid-root-{n}', {'n': n}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('field', ('baby-bear', 'baby-bear.ext4-binomial11'))
def test_montgomery32_words_are_explicitly_installed(toolchain, journal, directory, field):
    f = PLONKY3_FIELDS[field]
    source = f'''module sample;
domain F=field("{field}");
type Bytes=builtin("bytes");
type Vector<E:Field>=builtin("vector",E);
fn words(x:F,xs:Vector<F>,raw:Bytes)->(Bytes,Bytes,bool,F,bool,Vector<F>) {{
  let (ok,y)=kernel<F>("encoding.field_from_montgomery_le",raw);
  let (many,ys)=kernel<F>("encoding.fields_from_montgomery_le",raw);
  return(kernel<F>("encoding.field_montgomery_le",x),
         kernel<F>("encoding.fields_montgomery_le",xs),ok,y,many,ys);
}}
protocol Run roles(P)(x:F@P,xs:Vector<F>@P,raw:Bytes@P)
    ->(result:(Bytes,Bytes,bool,F,bool,Vector<F>)@P) {{ return words(x,xs,raw); }}
entry fn Demo(inputs:Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source)
    x, y = dense(f, 3), dense(f, 5)

    def mont(value):
        return b''.join(((v << 32) % f.modulus).to_bytes(4, 'little') for v in value)

    data = {'x': wire(f, x), 'xs': [wire(f, x), wire(f, y)]}
    result = entry.run('montgomery', data | {'raw': list(mont(x))})['result']
    assert result == [list(mont(x)), list(mont(x) + mont(y)), True, wire(f, x),
                      True, [wire(f, x)]]
    raw = f.modulus.to_bytes(4, 'little') * f.degree
    result = entry.run('modulus', data | {'raw': list(raw)})['result']
    assert result[2:] == [False, wire(f, f.ZERO), False, []]


REFUSAL = '''module sample;
domain F=field("{field}");
domain K=field("{other}");
type Vector<E:Field>=builtin("vector",E);
type Bytes=builtin("bytes");
fn work(x:F,y:K,xs:Vector<F>,raw:Bytes)->{result} {{ {body} }}
protocol Run roles(P)(x:F@P,y:K@P,xs:Vector<F>@P,raw:Bytes@P)->(result:{result}@P) {{
  return work(x,y,xs,raw);
}}
entry fn Demo(inputs:Run::Inputs) {{ return Run::run(inputs); }}
'''


@pytest.mark.parametrize('field,other,result,body,code', [
    ('goldilocks', 'baby-bear', 'Bytes',
     'return kernel<F>("encoding.field_montgomery_le",x);', 'binding-implementation'),
    ('goldilocks.ext2-binomial7', 'baby-bear', '(bool,F)',
     'return kernel<F>("encoding.field_from_montgomery_le",raw);', 'binding-implementation'),
    ('goldilocks', 'baby-bear', 'Bytes',
     'return kernel<F>("encoding.fields_montgomery_le",xs);', 'binding-implementation'),
    ('goldilocks.ext2-binomial7', 'baby-bear', '(bool,Vector<F>)',
     'return kernel<F>("encoding.fields_from_montgomery_le",raw);', 'binding-implementation'),
    ('baby-bear.ext4-binomial11', 'koala-bear.ext4-binomial3', 'F',
     'return kernel<F>("field.embed",y);', 'source.type'),
    ('goldilocks.ext2-binomial7', 'baby-bear', 'F',
     'return kernel<F>("field.embed",y);', 'source.type'),
    ('baby-bear', 'goldilocks', 'F',
     'return kernel<F>("field.constant"; "2013265921");', 'interactive-constant'),
    ('goldilocks', 'baby-bear', 'F',
     'return kernel<F>("field.constant"; "18446744069414584321");', 'interactive-constant'),
    ('goldilocks.ext2-binomial7', 'baby-bear', 'Vector<F>',
     'return kernel<F>("vector.constant"; "1","18446744069414584321");',
     'interactive-constant'),
])
def test_unsupported_encodings_cross_family_embeddings_and_literals_refuse(
        toolchain, journal, directory, field, other, result, body, code):
    path = directory / 'refused.zkc'
    path.write_text(REFUSAL.format(field=field, other=other, result=result, body=body))
    journal.run([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                 f'--module=sample={path}', 'sample::Demo',
                 f'--output={directory / "refused.zkpkg"}'], refuses=code)


def test_independent_binomial_defaults_and_new_presentations():
    assert set(FIELDS) == {'koala-bear', 'koala-bear.ext4-binomial3', 'koala-bear.ext8-binomial3'}
    assert Binomial(4).modulus == P and Binomial(4).coordinate_bytes == 4
    for name in NEW_FIELDS:
        f = PLONKY3_FIELDS[name]
        if f.degree > 1:
            x, top = [0, 1] + [0] * (f.degree - 2), [0] * (f.degree - 1) + [1]
            assert f.mul(x, top) == f.embed(f.nonresidue)
            assert f.power(x, f.modulus**f.degree - 1) == f.ONE
        assert len(f.coordinates(dense(f, 3))) == f.coordinate_bytes * f.degree
        with pytest.raises(ValueError):
            f.coordinates([f.modulus] * f.degree)


def polynomial_assets(base):
    # x*y+(p-1), with a full-width prime-field constant even when substitution
    # carries nonbase values. The Bundle also exposes x and y as one record.
    p = PLONKY3_FIELDS[base].modulus
    nodes = [['input', 0], ['input', 1], ['mul', 0, 1],
             ['constant', base, str(p - 1)], ['add', 2, 3]]
    ring = ['zkc.ring/0', [base, base], nodes, [4]]
    arena = ['zkc.ring/0', [base, base], nodes, [4, 0, 1]]
    bundle = ['zkc.relation-bundle/0', [], [['balance', 'field-balance', [base], base]], [[
        'table', 'required', ['fixed', 2], 'finite', [['xy', 'witness', base, 2]],
        arena, [['read', 0, '0', 0], ['read', 0, '0', 1]], [[0, ['all']]],
        [['field-balance', 0, ['global'], ['all'], [1], 2, None]]]]]
    return ring, bundle


@pytest.mark.parametrize('field', NEW_FIELDS)
@pytest.mark.parametrize('flags', FLAGS)
def test_ring_and_relation_substitution_preserves_nonbase_and_high_constants(
        toolchain, journal, directory, field, flags):
    f = PLONKY3_FIELDS[field]
    ring, bundle = polynomial_assets(field.split('.')[0])
    ring_path, bundle_path = directory / 'expression.json', directory / 'table.json'
    ring_path.write_text(json.dumps(ring))
    bundle_path.write_text(json.dumps(bundle))
    # Dense row evaluation requires homogeneous stored groups. Point and record
    # substitution separately test promotion of the original base-field table.
    dense_path = directory / 'dense-table.json'
    dense_path.write_text(json.dumps(bundle).replace(
        json.dumps(field.split('.')[0]), json.dumps(field)))
    source = f'''module sample;
domain F=field("{field}");
domain R=ring(asset expression);
domain B=bundle(asset table);
domain D=bundle(asset dense);
type Vector<E:Field>=builtin("vector",E);
fn substitute(xs:Vector<F>,cs:Vector<F>,w:Vector<F>)
    ->(Vector<F>,Vector<F>,Vector<F>,Vector<F>,Vector<F>,Vector<F>,Vector<F>) {{
  let empty=kernel<F>("vector.empty");
  return(kernel<F>("ring.point",xs;R),kernel<F>("ring.rows",w,2;R),
         kernel<F>("ring.coefficients",cs,2;R),
         kernel<F,0>("relation.table_point",xs;B),
         kernel<F,0>("relation.table_points",w,2;B),
         kernel<F,0>("relation.table_rows",w,empty,empty,2;D),
         kernel<F,0>("relation.table_record_points",w,2;B));
}}
protocol Run roles(P)(xs:Vector<F>@P,cs:Vector<F>@P,w:Vector<F>@P)
    ->(result:(Vector<F>,Vector<F>,Vector<F>,Vector<F>,Vector<F>,Vector<F>,Vector<F>)@P) {{
  return substitute(xs,cs,w);
}}
entry fn Demo(inputs:Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source,
                  [f'--asset=expression=ring-json={ring_path}',
                   f'--asset=table=relation-bundle-json={bundle_path}',
                   f'--asset=dense=relation-bundle-json={dense_path}', *flags])
    a, b, c, d = [dense(f, n) for n in (3, 7, 11, 17)]
    constant = f.embed(f.modulus - 1)
    residuals = [f.add(f.mul(a, b), constant), f.add(f.mul(c, d), constant)]
    # Coefficients of (a+b*T)(c+d*T) + (p-1), in column-major input layout.
    coefficients = [f.add(f.mul(a, c), constant),
                    f.add(f.mul(a, d), f.mul(b, c)), f.mul(b, d)]
    def encode(values):
        return [wire(f, v) for v in values]
    data = {'xs': encode([a, b]), 'cs': encode([a, b, c, d]), 'w': encode([a, b, c, d])}
    result = entry.run('substitution', data)['result']
    assert result == [encode(residuals[:1]), encode(residuals), encode(coefficients),
                      encode(residuals[:1]), encode(residuals), encode(residuals),
                      encode([a, b, c, d])]
    changed = f.add(a, f.ONE)
    mutated = entry.run('changed-assignment', data | {'xs': encode([changed, b])})['result']
    expected = encode([f.add(f.mul(changed, b), constant)])
    assert mutated[0] == mutated[3] == expected and expected != result[0]
    entry.run('short-assignment', data | {'xs': encode([a])}, refuses='entry-host-run-failed')
    entry.run('short-rows', data | {'w': encode([a, b, c])}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('base,extension,nonresidue', [
    ('baby-bear', 'baby-bear.ext4-binomial11', 11),
    ('goldilocks', 'goldilocks.ext2-binomial7', 7),
])
def test_independent_relation_readers_agree_on_binomial_wrap_and_canonical_refusals(
        toolchain, journal, base, extension, nonresidue):
    f = PLONKY3_FIELDS[extension]
    # x * top = nonresidue. Base configuration is explicitly embedded.
    arena = ['zkc.ring/0', [extension, extension, base], [
        ['input', 0], ['input', 1], ['mul', 0, 1], ['input', 2],
        ['embed', extension, 3], ['neg', 4], ['add', 2, 5]], [6]]
    bundle = ['zkc.relation-bundle/0', [], [], [[
        'wrap', 'required', ['fixed', 1], 'finite',
        [['values', 'witness', extension, 2], ['nr', 'config', base, 1]], arena,
        [['read', 0, '0', 0], ['read', 0, '0', 1], ['read', 1, '0', 0]],
        [[0, ['all']]], []]]]
    identity = sha256(json.dumps(bundle, separators=(',', ':')).encode()).hexdigest()
    x, top = [0, 1] + [0] * (f.degree - 2), [0] * (f.degree - 1) + [1]
    witness = [wire(f, x), wire(f, top)]
    original = [bundle, ['zkc.relation-configuration/0', identity, [[None, [[str(nonresidue)]]]]],
                ['zkc.relation-instance/0', identity, [], [['present', None, []]]],
                ['zkc.relation-witness/0', identity, [[witness]]]]
    cases = [(original, True, True)]
    changed = deepcopy(original)
    changed[3][2][0][0][0][0] = '1'
    cases.append((changed, True, False))
    for invalid in (str(f.modulus), '00', '-1', str(2**64)):
        changed = deepcopy(original)
        changed[3][2][0][0][0][0] = invalid
        cases.append((changed, False, None))
    for count in (f.degree - 1, f.degree + 1):
        changed = deepcopy(original)
        changed[3][2][0][0][0] = ['1'] * count
        cases.append((changed, False, None))
    raw = ''.join(json.dumps(case, separators=(',', ':')) + '\n' for case, _, _ in cases)
    replies = []
    for executable in (toolchain.tool('compiler', 'test/zkc-relation_bundle_conformance-test'),
                       toolchain.driver('relation_bundle_conformance')):
        replies.append([json.loads(line) for line in journal.run([executable], stdin=raw).splitlines()])
    assert replies[0] == replies[1] and len(replies[0]) == len(cases)
    for answer, (_, admitted, satisfied) in zip(replies[0], cases, strict=True):
        assert answer['accepted'] == admitted
        if admitted:
            assert answer['result']['satisfied'] == satisfied
        else:
            assert answer['error'] == 'bundle-value'


@pytest.mark.parametrize('field,base', [
    ('baby-bear.ext4-binomial11', 'koala-bear'),
    ('goldilocks.ext2-binomial7', 'baby-bear'),
])
def test_cross_family_relation_and_ring_assets_refuse(toolchain, journal, directory, field, base):
    ring, bundle = polynomial_assets(base)
    for name, document, kind, domain, call in [
        ('expression', ring, 'ring-json', 'ring', 'kernel<F>("ring.point",xs;A)'),
        ('table', bundle, 'relation-bundle-json', 'bundle',
         'kernel<F,0>("relation.table_point",xs;A)'),
    ]:
        path = directory / f'{name}.json'
        path.write_text(json.dumps(document))
        source = f'''module sample;
domain F=field("{field}");
domain A={domain}(asset {name});
type Vector<E:Field>=builtin("vector",E);
fn work(xs:Vector<F>)->Vector<F> {{ return {call}; }}
protocol Run roles(P)(xs:Vector<F>@P)->(result:Vector<F>@P) {{ return work(xs); }}
entry fn Demo(inputs:Run::Inputs) {{ return Run::run(inputs); }}
'''
        source_path = directory / f'{name}.zkc'
        source_path.write_text(source)
        journal.run([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                     f'--module=sample={source_path}', f'--asset={name}={kind}={path}',
                     'sample::Demo', f'--output={directory / (name + ".zkpkg")}'],
                    refuses='source.asset-carrier')
