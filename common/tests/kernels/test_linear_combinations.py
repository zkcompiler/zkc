"""Ordered linear expressions agree with dense arithmetic and preserve separate equations."""
import pytest

from entry import Entry, joint_execution
from source_modules import core_packages, library_modules


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
  let mut coordinate:G::Scalar=0;
  for i in 0..n {
    // Distinct coordinates make coefficient/point permutations observable.
    // These are algebra fixtures, not independent cryptographic generators.
    let k=if i==0 {0} else {if i==1 {0-1} else {scalar::from_index<G::Scalar>(i*i+7)}};
    let p=g*k;
    let a=scalar::from_index<G::Scalar>(i)-3;
    expression=linear::append(expression,a,p);
    dense=dense+p*a;
    coordinate=coordinate+a*k;
  }
  require linear::evaluate(expression)==dense;
  require linear::evaluate(expression)==g*coordinate;
  require !linear::equal(expression,linear::term<G>(1,dense+g));
  require linear::equal(expression,linear::term<G>(1,dense));
  let scaled=linear::scale(expression,0-7);
  require linear::evaluate(scaled)==dense*(0-7);
  require linear::equal(linear::add(expression,scaled),linear::term<G>(0-6,dense));
  let points=curve::append(curve::append(curve::empty<G>(),g),g*2);
  let coefficients=if malformed {vec::empty<G::Scalar>()} else {vec::append(vec::fill<G::Scalar>(3,1),5)};
  let packed=linear::from_terms(coefficients,points);
  require linear::evaluate(packed)==g*13;
  return linear::equal(linear::zero<G>(),linear::scale(expression,0));
}
protocol Run roles(P)(n:index@P,malformed:bool@P)->(ok:bool@P){return check(n,malformed);}
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''.replace('GROUP', group)
    entry = Entry(toolchain, journal, directory, source, (*library_modules(*core_packages()), *flags))
    for n in (0, 1, 2, 9):
        assert entry.run(f'length-{n}', {'n': str(n), 'malformed': False})['ok'] is True
    entry.run('shape', {'n': '2', 'malformed': True}, refuses='entry-host-run-failed')


@pytest.mark.parametrize('return_rows', [False, True])
def test_linear_relation_rows_remain_independent(toolchain, journal, directory, return_rows):
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
fn check(error:F)->(bool,bool,bool) {
  let g=curve::generator<G>();
  let bases=curve::append(curve::append(curve::empty<G>(),g),g*5);
  let challenge:F=11;
  // Witness (2,3), nonce (7,13), response (29,46).
  let response=vec::append(vec::append(vec::empty<F>(),29),46);
  let first=row(bases,response,g*(72+error),g*17,challenge);
  let second=row(bases,response,g*(72-error),g*17,challenge);
  return(first,second,first && second);
}
protocol Run roles(P)(error:F@P)->(checks:(bool,bool,bool)@P){return check(error);}
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    if not return_rows:
        source = source.replace('(bool,bool,bool)', 'bool')
        source = source.replace('return(first,second,first && second);', 'return first && second;')
    entry = Entry(toolchain, journal, directory, source, library_modules(*core_packages()))
    assert entry.run('valid', {'error': '0'})['checks'] == ([True, True, True] if return_rows else True)
    assert entry.run('cancelling-errors', {'error': '1'})['checks'] == ([False, False, False] if return_rows else False)


def test_linear_constructor_checks_before_composition(toolchain, journal, directory):
    # Without either constructor guard the concatenated pair has a valid shape,
    # so the final native MSM alone cannot enforce the source abstraction.
    source = """module sample;
use zkc::linear as linear;
use zkc::curve as curve;
use zkc::vector as vec;
domain G=group("ristretto255.group");
fn check(a:G::Scalar,reverse:bool,valid_left:bool)->G {
  let coefficients=vec::fill(a,1);
  let points=curve::append(curve::empty<G>(),curve::generator<G>());
  // Exchange which mismatch is encountered first; neither may be repaired by
  // concatenating it with an opposite mismatch.
  let left=linear::from_terms(if !valid_left && reverse {vec::empty<G::Scalar>()} else {coefficients},
    if valid_left || reverse {points} else {curve::empty<G>()});
  let right=linear::from_terms(if reverse {coefficients} else {vec::empty<G::Scalar>()},
    if reverse {curve::empty<G>()} else {points});
  return linear::evaluate(linear::add(left,right));
}
protocol Run roles(P)(a:G::Scalar@P,reverse:bool@P,valid_left:bool@P)->(out:G@P){return check(a,reverse,valid_left);}
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
"""
    entry = Entry(toolchain, journal, directory, source, library_modules(*core_packages()))
    for reverse in (False, True):
        for valid_left in (False, True):
            report = entry.run(f'invalid-parts-{reverse}-{valid_left}',
                               {'a': '7', 'reverse': reverse, 'valid_left': valid_left},
                               refuses='entry-host-run-failed')
            after = joint_execution(report)['roles'][0]['after']
            assert after[0] == 'stopped'
            assert after[1]['cause'] == ['explicit', {'text': 'reject', 'omitted_bytes': 0}]
