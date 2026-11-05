"""Ordinary source calls retain the ABI and execute checked Native preferences."""

import json

import pytest

from entry import Entry, joint_artifact
from source_modules import core_packages, library_modules

MODULES = library_modules(*core_packages())


def selected_program(entry):
    return json.loads(joint_artifact(json.loads(entry.package.read_text()))['candidate'])


@pytest.mark.parametrize('group', ['bls12-381.g1', 'bls12-381.g2'])
@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_source_curve_preferences(toolchain, journal, directory, group, flags):
    source = '''module sample;
use zkc::curve as curve;
use zkc::vector as vec;
domain G=group("GROUP");
fn scaled(point:G,s:G::Scalar)->G{return kernel<G>("curve.scale",point,s);}
fn multiples(point:G,n:index)->G{
 let mut result=curve::identity<G>();
 for i in 0..n {result=result+point;}
 return result;
}
fn work(xs:vec::Vector<G::Scalar>,s:G::Scalar,k:index,ok:bool,branch:bool,trips:index)
 ->(bool,vec::Vector<G::Scalar>){
 require ok;
 let g=curve::generator<G>();
 let points=curve::collect(vec::elements(xs),fn(_)=>g);
 let single=if branch {scaled(g,s)} else {kernel<G>("curve.scale",g,s)+g};
 let mut repeated=single;
 for i in 0..trips {repeated=scaled(repeated,s);}
 let per_point=curve::scale_each(xs,points);
 let shared=curve::scale(points,s);
 let initial=if branch {k} else {k+1};
 let mut factor=initial;
 for i in 0..trips {factor=factor*k;}
 let mut lanes=true;
 for i in 0..vec::length(xs) {
   lanes=lanes && curve::get(per_point,i)==multiples(g,i+2)
     && curve::get(shared,i)==multiples(g,k);
 }
 return(single==multiples(g,initial) && repeated==multiples(g,factor)
   && lanes && curve::length(per_point)==vec::length(xs)
   && curve::length(shared)==vec::length(xs),xs);
}
protocol Work roles(P)(xs:vec::Vector<G::Scalar>@P,s:G::Scalar@P,k:index@P,ok:bool@P,
 branch:bool@P,trips:index@P)
 ->(result:(bool,vec::Vector<G::Scalar>)@P){return work(xs,s,k,ok,branch,trips);}
entry fn Demo(inputs:Work::Inputs){return Work::run(inputs);}
'''.replace('GROUP', group)
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    program = selected_program(entry)
    expected = 'blst/resident/' if group.endswith('.g2') else 'arkworks/'
    selected = {binding[1]: binding[3] for binding in program[1]}
    for contract in ('curve.scale', 'curve.scale_each', 'curve.vector_scale'):
        assert selected[contract] == expected + contract
    # Input storage stays canonical even when the selected arithmetic is resident.
    assert all('@blst/' not in port[1]
               for participant in program[3] for port in participant[4])
    for n in (0, 1, 4):
        for scalar in (0, 2, 3):
            xs = [str(i + 2) for i in range(n)]
            assert entry.run(f'rows-{n}-scalar-{scalar}', {
                'xs': xs, 's': str(scalar), 'k': str(scalar), 'ok': True,
                'branch': n % 2 == 0, 'trips': str(min(n, 2)),
            }) == {'result': [True, xs]}
    entry.run('stopped', {'xs': ['2'], 's': '3', 'k': '3', 'ok': False,
                          'branch': True, 'trips': '1'},
              refuses='entry-host-run-failed')


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
def test_source_pairing_preference(toolchain, journal, directory, flags):
    source = '''module sample;
use zkc::curve as curve;
use zkc::pairing as pairing;
use zkc::finite_domain::{range};
domain F=field("bls12-381.fr");
fn work(n:index,m:index,cancel:bool)->bool{
 let a=curve::generator<F::PairingG1>();
 let b=curve::generator<F::PairingG2>();
 let left=curve::collect(range(0,n),fn(_)=>a);
 let right=curve::collect(range(0,m),fn(i)=>if cancel && i==1 {curve::neg(b)} else {b});
 return pairing::check<F>(left,right);
}
protocol Work roles(P)(n:index@P,m:index@P,cancel:bool@P)->(accepted:bool@P){
 return work(n,m,cancel);
}
entry fn Demo(inputs:Work::Inputs){return Work::run(inputs);}
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    program = selected_program(entry)
    assert any(binding[1:4] == ['pairing.check', ['bls12-381.fr'],
                               'blst/resident/pairing.check'] for binding in program[1])
    for n, cancel, expected in [(0, False, True), (1, False, False),
                                (2, False, False), (2, True, True)]:
        assert entry.run(f'pairs-{n}-{cancel}', {
            'n': str(n), 'm': str(n), 'cancel': cancel,
        }) == {'accepted': expected}
    entry.run('different-lengths', {'n': '1', 'm': '0', 'cancel': False},
              refuses='entry-host-run-failed')
