"""Prepared exact RNS module products through actual source/native execution."""
import pytest

from entry import Entry
from source_modules import library_modules

MODULES = library_modules('core/polynomial')


def product(matrix, digits, q, n, rows, columns):
    """Independent arbitrary-precision negacyclic coefficient model."""
    result = []
    for row in range(rows):
        full = [0] * (2*n-1)
        for column in range(columns):
            a = matrix[(row*columns+column)*n:(row*columns+column+1)*n]
            b = digits[column*n:(column+1)*n]
            for i, x in enumerate(a):
                for j, y in enumerate(b):
                    full[i+j] += x*y
        result.extend((full[i] - (full[i+n] if i+n < len(full) else 0)) % q
                      for i in range(n))
    return result


SOURCE = '''module sample;
use zkc::indices::{Indices}; use zkc::quotient_matrix as matrix;
fn evaluate(a:Indices,b:Indices,c:Indices,q:index,n:index,r:index,k:index,bound:index) {
  let prepared=matrix::prepare(a,q,n,r,k,bound);
  return (matrix::multiply(prepared,b),matrix::multiply(prepared,c));
}
protocol Run roles(P)(a:Indices@P,b:Indices@P,c:Indices@P,q:index@P,n:index@P,
  r:index@P,k:index@P,bound:index@P)->(first:Indices@P,second:Indices@P,original:Indices@P){
  let outputs=evaluate(a,b,c,q,n,r,k,bound);
  return(first=outputs.0,second=outputs.1,original=a);
} entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
'''


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
@pytest.mark.parametrize('q,n,k,bound', [(16, 4, 3, 3), (17, 4, 3, 0), (17, 4, 3, 2**64-1),
                                      (12289, 512, 4, 8),
                                      (8380417, 256, 4, 128), (2**64-59, 256, 4, 128),
                                      (2**64-59, 4, 7, 10_000_000)])
def test_preparation_is_reused_for_independent_digit_vectors(
        toolchain, journal, directory, flags, q, n, k, bound):
    entry = Entry(toolchain, journal, directory, SOURCE, (*flags, *MODULES))
    r = 2
    a = [q//2 if i % 3 == 0 else (i*i+1) % q for i in range(r*k*n)]
    b = [(-bound if i % 2 else bound) % q for i in range(k*n)]
    c = [((-1 if i % 2 else 1)*(i % (bound+1))) % q for i in range(k*n)]
    result = entry.run('reused', dict(a=a, b=b, c=c, q=q, n=n, r=r, k=k, bound=bound))
    assert list(map(int, result['first'])) == product(a, b, q, n, r, k)
    assert list(map(int, result['second'])) == product(a, c, q, n, r, k)
    assert list(map(int, result['original'])) == a


def test_native_refusals_cover_actual_shapes_and_digit_bounds(toolchain, journal, directory):
    entry = Entry(toolchain, journal, directory, SOURCE, MODULES)
    valid = dict(a=[1, 2, 3, 4], b=[1, 16, 2, 15], c=[0]*4,
                 q=17, n=2, r=1, k=2, bound=2)
    for changes, code in [({'q': 1}, 'quotient-modulus'),
                          ({'a': [1]}, 'quotient-shape'),
                          ({'a': [17]*4}, 'quotient-residue'),
                          ({'r': 0}, 'quotient-shape'),
                          ({'n': 0}, 'quotient-degree'),
                          ({'n': 1}, 'quotient-shape'),
                          ({'n': 3, 'a': [0]*6}, 'quotient-transform-profile'),
                          ({'b': [0]}, 'quotient-shape'),
                          ({'b': [17]*4}, 'quotient-residue'),
                          ({'b': [3]*4}, 'quotient-digit-bound'),
                          ({'b': [14]*4}, 'quotient-digit-bound'),
                          ({'q': 2**64-1, 'a': [2**63]*4, 'bound': 2**64-1},
                           'quotient-rns-capacity')]:
        entry.run(code, valid | changes, refuses='refused:'+code)


@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_unused_preparation_keeps_its_ordered_refusal(toolchain, journal, directory, flags):
    source = '''module sample; use zkc::indices::{Indices};
    use zkc::quotient_matrix as matrix;
    fn evaluate(a:Indices,go:bool)->bool effects(stop) {
      return if go {let unused=matrix::prepare(a,17,2,1,1,1); true} else {false};
    }
    protocol Run roles(P)(a:Indices@P,go:bool@P)->(ok:bool@P){return evaluate(a,go);}
    entry fn Demo(inputs:Run::Inputs){return Run::run(inputs);}
    '''
    entry = Entry(toolchain, journal, directory, source, (*flags, *MODULES))
    assert entry.run('unreached', {'a': [17, 0], 'go': False})['ok'] is False
    entry.run('reached', {'a': [17, 0], 'go': True}, refuses='refused:quotient-residue')
    assert entry.run('valid', {'a': [1, 0], 'go': True})['ok'] is True
