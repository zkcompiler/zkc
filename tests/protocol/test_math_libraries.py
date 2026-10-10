"""Shared source mathematics executes through the ordinary compiler and Host."""
from pathlib import Path

import pytest

from entry import Entry

ROOT = Path(__file__).resolve().parents[2]
MODULES = [f'--module=zkc::{name}={ROOT}/libraries/zkc/{name}.zkc'
           for name in ('vector', 'matrix', 'boolean', 'polynomial', 'symbolic')]


def scalar(n):
    return (b'ZKCV\0\x01' + n.to_bytes(32, 'little')).hex()


def vector(values):
    return (b'ZKCV\0\x42' + len(values).to_bytes(4, 'little')
            + b''.join(n.to_bytes(32, 'little') for n in values)).hex()


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
@pytest.mark.parametrize('notation', [False, True])
def test_shared_math_and_runtime_data(toolchain, journal, directory, flags, notation):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::matrix::{Matrix};
domain F=field("bls12-381.fr");
math fn symbolic(a:F,b:F,x:F) {
  let packed=zkc::symbolic::pack([a,b]);
  let linear=zkc::symbolic::from_coefficients(packed);
  let squared=zkc::symbolic::multiply(linear,linear);
  let coefficients=zkc::symbolic::coefficients<F,3>(squared);
  let leading=zkc::symbolic::get<F,3,2>(coefficients);
  let constant=zkc::symbolic::constant<F,1>(a);
  let shifted=zkc::symbolic::add(linear,constant);
  let mle=zkc::symbolic::mle<F,1>(packed);
  let table=zkc::symbolic::pack([a,b,a+b,a+b+b]);
  let multivariate=zkc::symbolic::mle<F,2>(table);
  let fixed=zkc::symbolic::fix_prefix<F,1,1>(multivariate,[x]);
  let summed=zkc::symbolic::sum_suffix<F,1,1>(multivariate);
  let fixed_table=zkc::symbolic::fix_table<F,1,1>(table,[x]);
  // This MLE is 4*u + 2*v + w; unequal arities detect swapped intrinsic roots.
  let wide=zkc::symbolic::pack<F,8>([0,1,2,3,4,5,6,7]);
  let wide_polynomial=zkc::symbolic::mle<F,3>(wide);
  let fixed_two=zkc::symbolic::fix_prefix<F,1,2>(wide_polynomial,[a,b]);
  let sum_one=zkc::symbolic::sum_suffix<F,2,1>(wide_polynomial);
  let table_two=zkc::symbolic::fix_table<F,1,2>(wide,[a,b]);
  return (leading,zkc::symbolic::evaluate(shifted,[x]),
          zkc::symbolic::evaluate(mle,[x]),zkc::symbolic::evaluate(fixed,[a+b]),
          zkc::symbolic::evaluate(summed,[x]),zkc::symbolic::get<F,2,1>(fixed_table),
          zkc::symbolic::evaluate(fixed_two,[x]),zkc::symbolic::evaluate(sum_one,[a,b]),
          zkc::symbolic::get<F,2,1>(table_two));
}
fn numerical(m:Matrix<F>,v:Vector<F>,a:F,x:F) {
  let folded=zkc::vector::fold(v,x);
  let repeated=zkc::vector::fill(a,2);
  let product=zkc::matrix::multiply(m,v);
  let transpose=zkc::matrix::transpose_multiply(m,v);
  let bilinear=zkc::matrix::bilinear(m,v,v);
  let polynomial=zkc::polynomial::from_coefficients(v);
  return (zkc::vector::get(folded,0),zkc::vector::sum(repeated),
          zkc::vector::dot(v,v),zkc::vector::has_length<F,2>(v),
          product,transpose,bilinear,zkc::matrix::rows(m),zkc::matrix::columns(m),
          zkc::polynomial::evaluate(polynomial,x),zkc::polynomial::boundary(polynomial),
          zkc::vector::add(v,zkc::vector::scale(v,a)));
}
protocol Run roles(P)(m:Matrix<F>@P,v:Vector<F>@P,a:F@P,b:F@P,x:F@P)
 ->(analytic:(F,F,F,F,F,F,F,F,F)@P,numeric:(F,F,F,bool,Vector<F>,Vector<F>,F,index,index,F,F,Vector<F>)@P,
    logic:(bool,bool,bool,bool)@P) {
  let computed=numerical(m,v,a,x);
  return (analytic=symbolic(a,b,x),numeric=computed,
    logic=(zkc::boolean::both(true,false),zkc::boolean::either(true,false),
      zkc::boolean::different(true,true),zkc::boolean::negate(false)));
}
run Demo=Run;
'''
    if notation:
        source = source.replace('module sample;', 'module sample;use zkc::vector;use zkc::matrix;use zkc::symbolic as algebra;')
        source = source.replace('zkc::symbolic::multiply(linear,linear)', 'linear*linear')
        source = source.replace('zkc::symbolic::add(linear,constant)', 'linear+constant')
        source = source.replace('zkc::matrix::multiply(m,v)', 'm*v')
        source = source.replace('zkc::vector::dot(v,v)', '⟪v,v⟫')
        source = source.replace('zkc::vector::add(v,zkc::vector::scale(v,a))', 'v+v*a')
    # [1 2; 0 3], independent native sparse-matrix encoding.
    entries = [(0, 0, 1), (0, 1, 2), (1, 1, 3)]
    matrix = (b'ZKCV\0\x17' + b''.join(n.to_bytes(4, 'little') for n in (2, 2, 3))
              + b''.join(r.to_bytes(4, 'little') + c.to_bytes(4, 'little')
                         + v.to_bytes(32, 'little') for r, c, v in entries)).hex()
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    inputs = {'m': matrix, 'v': vector([2, 3]), 'a': scalar(2), 'b': scalar(3), 'x': scalar(4)}
    result = entry.run('valid', inputs)
    assert result['analytic'] == [scalar(n) for n in (9, 16, 6, 59, 37, 23, 18, 29, 15)]
    assert result['numeric'] == [scalar(6), scalar(4), scalar(13), True,
        vector([8, 9]), vector([2, 13]), scalar(43), 2, 2, scalar(14), scalar(7), vector([6, 9])]
    assert result['logic'] == [False, True, False, True]
    report = entry.run('odd-table', inputs | {'v': vector([2, 3, 4])},
                       refuses='entry-run-incomplete')
    assert 'split' in str(report)
    report = entry.run('empty-table', inputs | {'v': vector([])},
                       refuses='entry-run-incomplete')
    assert 'split' in str(report)


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--release-storage']])
@pytest.mark.parametrize('helper,operator,skip', [('both', '&&', False), ('either', '||', True)])
def test_boolean_library_calls_remain_eager(toolchain, journal, directory, flags,
                                          helper, operator, skip):
    source = f'''module sample;
fn checked(ok:bool){{require ok;return ok;}}
fn evaluate(go:bool,ok:bool,eager:bool){{
  return if eager{{zkc::boolean::{helper}(left=go,right=checked(ok))}}
         else{{go {operator} checked(ok)}};
}}
protocol Run roles(P)(go:bool@P,ok:bool@P,eager:bool@P)->(result:bool@P){{
  return evaluate(go,ok,eager);
}}
run Demo=Run;
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    assert entry.run('skipped', {'go': skip, 'ok': False, 'eager': False}) == {'result': skip}
    entry.run('evaluated', {'go': skip, 'ok': False, 'eager': True},
              refuses='entry-run-incomplete')
    assert entry.run('accepted', {'go': skip, 'ok': True, 'eager': True}) == {'result': skip}


def test_formal_contract_and_execution_modes_refuse(toolchain, journal, directory):
    prefix = '''module sample;
 domain F=field("bls12-381.fr");
 protocol Run roles(P)(a:F@P)->(out:F@P){return a;} run Demo=Run;
'''
    for name, definition, code in [
        ('index-bound', 'math fn bad(a:F)->F {return zkc::symbolic::get<F,1,1>(zkc::symbolic::pack([a]));}', 'source.bound'),
        ('ordered-math', 'math fn bad(a:F)->F {return zkc::vector::sum(zkc::vector::fill(a,1));}', 'source.mode'),
    ]:
        path = directory / f'{name}.zkc'
        path.write_text(prefix + definition)
        journal.run([toolchain.compiler, 'language-check', '--source-format=zkc',
                     '--entry=sample::Demo', f'--module=sample={path}', *MODULES], refuses=code)
