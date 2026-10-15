"""Ordered linear expressions agree with dense arithmetic and preserve separate equations."""
import pytest

from entry import Entry
from source_modules import library_modules


@pytest.mark.parametrize('group', [
    'bls12-381.g1', 'ristretto255.group', 'edwards25519.prime', 'bn254.g1', 'bn254.g2',
])
@pytest.mark.parametrize('flags', [(), ('--no-simplify', '--release-storage')])
def test_linear_expressions(toolchain, journal, directory, group, flags):
    source = '''module sample;
use zkc::linear as linear;
use zkc::vector as vec;
use zkc::curve as curve;
use zkc::scalar as scalar;
domain G=group("GROUP");
fn check(n:index, malformed:bool)->bool {
  let g=curve::generator<G>();
  let identity=curve::identity<G>();
  let mut expression=linear::zero<G>();
  let mut dense=identity;
  for i in 0..n {
    // Identities, repeated and opposite points; coefficients may be zero/negative.
    let p=if i==0 {identity} else {if i==1 {curve::neg(g)} else {g}};
    let a=scalar::from_index<G::Scalar>(i)-3;
    expression=linear::append(expression,a,p);
    dense=dense+p*a;
  }
  require linear::evaluate(expression)==dense;
  require !linear::equal(expression,linear::term<G>(1,dense+g));
  require linear::equal(expression,linear::term<G>(1,dense));
  let scaled=linear::scale(expression,0-7);
  require linear::evaluate(scaled)==dense*(0-7);
  require linear::equal(linear::add(expression,scaled),linear::term<G>(0-6,dense));
  let points=curve::append(curve::append(curve::empty<G>(),g),g*2);
  let coefficients=if malformed {vec::empty<G::Scalar>()} else {vec::fill<G::Scalar>(3,2)};
  let packed=linear::from_terms(coefficients,points);
  require linear::evaluate(packed)==g*9;
  return linear::equal(linear::zero<G>(),linear::scale(expression,0));
}
protocol Run roles(P)(n:index@P,malformed:bool@P)->(ok:bool@P){return check(n,malformed);}
run Demo=Run;
'''.replace('GROUP', group)
    entry = Entry(toolchain, journal, directory, source, (*library_modules('zkc'), *flags))
    for n in (0, 1, 2, 9):
        assert entry.run(f'length-{n}', {'n': str(n), 'malformed': False})['ok'] is True
    entry.run('shape', {'n': '2', 'malformed': True}, refuses='entry-run-incomplete')


def test_linear_relation_rows_remain_independent(toolchain, journal, directory):
    # Two rows of a linear-relation Sigma verifier. Opposite errors would cancel
    # if an implementation incorrectly combined independent equations.
    source = '''module sample;
use zkc::linear as linear;
use zkc::curve as curve;
use zkc::vector as vec;
domain G=group("ristretto255.group");
domain F=field("ristretto255.scalar");
fn row(bases:curve::Groups<G>, responses:vec::Vector<F>, commitment:G, statement:G, challenge:F)->bool {
  let lhs=linear::from_terms(responses,bases);
  let rhs=linear::append(linear::term<G>(1,commitment),challenge,statement);
  return linear::equal(lhs,rhs);
}
fn check(error:F)->(bool,bool) {
  let g=curve::generator<G>();
  let bases=curve::append(curve::append(curve::empty<G>(),g),g*5);
  let challenge:F=11;
  // Witness (2,3), nonce (7,13), response (29,46).
  let response=vec::append(vec::append(vec::empty<F>(),29),46);
  let first=row(bases,response,g*(72+error),g*17,challenge);
  let second=row(bases,response,g*(72-error),g*17,challenge);
  return(first,second);
}
protocol Run roles(P)(error:F@P)->(checks:(bool,bool)@P){return check(error);}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, library_modules('zkc'))
    assert entry.run('valid', {'error': '0'})['checks'] == [True, True]
    assert entry.run('cancelling-errors', {'error': '1'})['checks'] == [False, False]


def test_linear_constructor_checks_before_composition(toolchain, journal, directory):
    # Without either constructor guard the concatenated pair has a valid shape,
    # so the final native MSM alone cannot enforce the source abstraction.
    source = """module sample;
use zkc::linear as linear;
use zkc::curve as curve;
use zkc::vector as vec;
domain G=group("ristretto255.group");
fn check(a:G::Scalar)->G {
  let left=linear::from_terms(vec::fill(a,1),curve::empty<G>());
  let right=linear::from_terms(vec::empty<G::Scalar>(),
    curve::append(curve::empty<G>(),curve::generator<G>()));
  return linear::evaluate(linear::add(left,right));
}
protocol Run roles(P)(a:G::Scalar@P)->(out:G@P){return check(a);}
run Demo=Run;
"""
    entry = Entry(toolchain, journal, directory, source, library_modules('zkc'))
    entry.run('invalid-parts', {'a': '7'}, refuses='entry-run-incomplete')
