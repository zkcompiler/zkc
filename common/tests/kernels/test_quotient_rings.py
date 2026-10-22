"""Quotient-ring source, contract and native boundaries against Python integers."""
import pytest

from entry import Entry, joint_execution
from source_modules import library_modules


MODULES = library_modules('core/polynomial', 'relations/lattice')


def convolution(a, b, q):
    """Ordinary Z[X] multiplication, then reduction by X^n+1 and q."""
    n = len(a)
    full = [sum(a[i] * b[k-i] for i in range(n) if 0 <= k-i < n)
            for k in range(2*n-1)]
    return [(full[i] - (full[i+n] if i+n < len(full) else 0)) % q for i in range(n)]


def norm(a, b, q):
    def centered(x):
        return (x + q//2) % q - q//2
    return sum(centered(x)**2 for x in (*a, *b))


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
@pytest.mark.parametrize('q,n', [(17, 4), (16, 3), (2**64-1, 4), (12289, 512),
                              (12289, 1024), (8380417, 256), (3329, 256)])
def test_canonical_arithmetic_through_checked_source(toolchain, journal, directory, flags, q, n):
    source = f'''module sample;
    use zkc::indices::{{Indices}}; use zkc::quotient as qr;
    fn evaluate(a:Indices,b:Indices,bound:index) {{
      let left=qr::polynomial<{q},{n}>(a); let right=qr::polynomial<{q},{n}>(b);
      return (qr::coefficients(qr::add(left,right)),
        qr::coefficients(qr::subtract(left,right)),
        qr::coefficients(qr::multiply(left,right)),qr::norm_within(left,right,bound));
    }}
    protocol Run roles(P)(a:Indices@P,b:Indices@P,bound:index@P)
        ->(sum:Indices@P,difference:Indices@P,product:Indices@P,within:bool@P) {{
      let result=evaluate(a,b,bound);
      return(sum=result.0,difference=result.1,product=result.2,within=result.3);
    }} entry fn Demo(inputs:Run::Inputs) {{ return Run::run(inputs); }}
    '''
    entry = Entry(toolchain, journal, directory, source, (*flags, *MODULES))
    cases = [([(i*i+3*i+1) % q for i in range(n)], [(5*i+7) % q for i in range(n)])]
    if n <= 4:
        cases += [([q-1]*n, [q-1]*n), ([0]*n, [0]*n)]
    for i, (a, b) in enumerate(cases):
        bound = min(norm(a, b, q), 2**64-1)
        actual = entry.run(f'case-{i}', {'a': a, 'b': b, 'bound': bound})
        assert list(map(int, actual['sum'])) == [(x+y) % q for x, y in zip(a, b)]
        assert list(map(int, actual['difference'])) == [(x-y) % q for x, y in zip(a, b)]
        assert list(map(int, actual['product'])) == convolution(a, b, q)
        assert actual['within'] is (norm(a, b, q) <= bound)


def test_direct_native_admission_does_not_trust_source_wrappers(toolchain, journal, directory):
    source = '''module sample;
    use zkc::indices::{Indices}; use zkc::primitives::quotient as raw;
    protocol Run roles(P)(a:Indices@P,b:Indices@P,q:index@P)->(product:Indices@P){
      return raw::multiply(a,b,q);
    } entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
    '''
    entry = Entry(toolchain, journal, directory, source, MODULES)
    assert entry.run('positive', {'a': [1, 2], 'b': [3, 4], 'q': 17})['product'] == ['12', '10']
    for name, a, b, q, diagnostic in [
        ('zero-modulus', [0], [0], 0, 'quotient-modulus'),
        ('unit-modulus', [0], [0], 1, 'quotient-modulus'),
        ('zero-degree', [], [], 17, 'quotient-degree'),
        ('shape', [0], [], 17, 'quotient-shape'),
        ('left-residue', [17], [0], 17, 'quotient-residue'),
        ('right-residue', [0], [17], 17, 'quotient-residue'),
        ('word-residue', [2**64-1], [0], 17, 'quotient-residue'),
    ]:
        entry.run(name, {'a': a, 'b': b, 'q': q}, refuses='refused:' + diagnostic)


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
@pytest.mark.parametrize('operation', ['add', 'subtract', 'multiply', 'norm_within'])
def test_unused_partial_operations_remain_at_their_reached_branch(
        toolchain, journal, directory, flags, operation):
    arguments = 'a,b,q,0' if operation == 'norm_within' else 'a,b,q'
    source = f'''module sample;
    use zkc::indices::{{Indices}}; use zkc::primitives::quotient as raw;
    fn evaluate(a:Indices,b:Indices,q:index,go:bool)->bool effects(stop) {{
      return if go {{ let unused=raw::{operation}({arguments}); true }} else {{ false }};
    }}
    protocol Run roles(P)(a:Indices@P,b:Indices@P,q:index@P,go:bool@P)->(reached:bool@P){{
      return evaluate(a,b,q,go);
    }} entry fn Demo(inputs:Run::Inputs){{return Run::run(inputs);}}
    '''
    entry = Entry(toolchain, journal, directory, source, (*flags, *MODULES))
    malformed = {'a': [17], 'b': [0], 'q': 17, 'go': False}
    assert entry.run('unreached', malformed)['reached'] is False
    entry.run('unused-but-reached', malformed | {'go': True}, refuses='refused:quotient-residue')
    assert entry.run('reached-and-valid', malformed | {'a': [0], 'go': True})['reached'] is True


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_short_preimage_arithmetic_and_integer_norm_boundary(toolchain, journal, directory, flags):
    source = '''module sample;
    use zkc::indices::{Indices}; use zkc::quotient as qr; use lattice;
    protocol Run roles(P)(h:Indices@P,c:Indices@P,s:Indices@P,bound:index@P)->(valid:bool@P){
      return lattice::short_preimage(qr::polynomial<12289,512>(h),
        qr::polynomial<12289,512>(c),qr::polynomial<12289,512>(s),bound);
    } entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
    '''
    entry = Entry(toolchain, journal, directory, source, (*flags, *MODULES))
    q, n = 12289, 512
    h = [(i*i+1) % q for i in range(n)]
    s1 = [(i % 5-2) % q for i in range(n)]
    s2 = [(i % 3-1) % q for i in range(n)]
    c = [(x+y) % q for x, y in zip(convolution(h, s2, q), s1)]
    exact = norm(s1, s2, q)
    arguments = {'h': h, 'c': c, 's': s2, 'bound': exact}
    assert entry.run('exact', arguments)['valid'] is True
    assert entry.run('one-below', arguments | {'bound': exact-1})['valid'] is False
    assert entry.run('falcon-512-bound', arguments | {'bound': 34034726})['valid'] is True
    changed = c.copy(); changed[0] = (changed[0]+6144) % q
    assert entry.run('large-first-coordinate', arguments | {'c': changed, 'bound': 34034726})['valid'] is False
    for name, changes in [
        ('truncated', {'h': h[:-1]}), ('extra-zero', {'h': h+[0]}),
        ('noncanonical', {'s': [q]+s2[1:]}), ('empty', {'c': []}),
    ]:
        # Constructor guards are reached, not a later host parsing failure.
        report = entry.run(name, arguments | changes, refuses='entry-host-run-failed')
        cause = joint_execution(report)['failure_role']['after'][1]['cause']
        assert cause == ['explicit', {'omitted_bytes': 0, 'text': 'reject'}]


@pytest.mark.parametrize('case', ['private', 'modulus', 'degree', 'entry', 'message', 'small-q', 'zero-n'])
def test_nominal_ring_identity_and_constructor_authority(toolchain, journal, directory, case):
    prefix = 'module sample; use zkc::indices::{Indices}; use zkc::quotient as qr; '
    if case == 'private':
        body = 'fn bypass(a:Indices)->qr::Polynomial<17,4>{return qr::Polynomial<17,4>{data:a};}'
        diagnostic = 'source.private'
    elif case in ('modulus', 'degree'):
        other = '19,4' if case == 'modulus' else '17,8'
        body = f'fn mix(a:qr::Polynomial<17,4>,b:qr::Polynomial<{other}>)->qr::Polynomial<17,4>{{return qr::multiply(a,b);}}'
        diagnostic = 'source.type'
    elif case in ('small-q', 'zero-n'):
        params = '1,4' if case == 'small-q' else '17,0'
        body = f'fn invalid(a:Indices)->qr::Polynomial<{params}>{{return qr::polynomial<{params}>(a);}}'
        diagnostic = 'source.bound'
    elif case == 'entry':
        body = '''protocol Run roles(P)(a:qr::Polynomial<17,4>@P)->(result:Indices@P){return qr::coefficients(a);}
        entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}'''
        diagnostic = 'source.ingress'
    else:
        body = '''protocol Run roles(P,V)(a:Indices@P)->(result:Indices@V){
          let local=qr::polynomial<17,4>(a); let received=send P -> V(local);
          return qr::coefficients(received);
        }'''
        diagnostic = 'source.ingress'
    path = directory / 'invalid.zkc'; path.write_text(prefix + body)
    report = journal.json([toolchain.runtime, '--json', 'check', f'--compiler={toolchain.compiler}',
                           f'--module=sample={path}', *MODULES,
                           *(['sample::Demo'] if case == 'entry' else [])], refuses='source-compilation')
    assert report['diagnostics'].startswith(diagnostic), report
