"""Shared source mathematics executes through the ordinary compiler and Host."""
from pathlib import Path

import pytest

from entry import Entry, joint_execution
from source_modules import core_packages, library_modules

ROOT = Path(__file__).resolve().parents[3]
MODULES = library_modules(*core_packages())


def scalar(n):
    return str(n)


def vector(values):
    return [str(n) for n in values]


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
  let table=zkc::multilinear::table(v,1,1);
  let folded=zkc::multilinear::values(zkc::multilinear::fix_first(table,x));
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
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    if notation:
        source = source.replace('module sample;', 'module sample;use zkc::vector;use zkc::matrix;use zkc::symbolic as algebra;')
        source = source.replace('zkc::symbolic::multiply(linear,linear)', 'linear*linear')
        source = source.replace('zkc::symbolic::add(linear,constant)', 'linear+constant')
        source = source.replace('zkc::matrix::multiply(m,v)', 'm*v')
        source = source.replace('zkc::vector::dot(v,v)', '⟪v,v⟫')
        source = source.replace('zkc::vector::add(v,zkc::vector::scale(v,a))', 'v+v*a')
    # [1 2; 0 3], sparse entries in row-major order.
    matrix = {'rows': '2', 'columns': '2', 'entries': [
        ['0', '0', '1'], ['0', '1', '2'], ['1', '1', '3']]}
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    inputs = {'m': matrix, 'v': vector([2, 3]), 'a': scalar(2), 'b': scalar(3), 'x': scalar(4)}
    result = entry.run('valid', inputs)
    assert result['analytic'] == [scalar(n) for n in (9, 16, 6, 59, 37, 23, 18, 29, 15)]
    assert result['numeric'] == [scalar(6), scalar(4), scalar(13), True,
        vector([8, 9]), vector([2, 13]), scalar(43), '2', '2', scalar(14), scalar(7), vector([6, 9])]
    assert result['logic'] == [False, True, False, True]
    report = entry.run('odd-table', inputs | {'v': vector([2, 3, 4])},
                       refuses='entry-host-run-failed')
    after = joint_execution(report)['roles'][0]['after']
    assert after[0] == 'stopped' and after[1]['cause'][0] == 'explicit'
    report = entry.run('empty-table', inputs | {'v': vector([])},
                       refuses='entry-host-run-failed')
    after = joint_execution(report)['roles'][0]['after']
    assert after[0] == 'stopped' and after[1]['cause'][0] == 'explicit'


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
entry fn Demo(inputs: Run::Inputs) {{ return Run::run(inputs); }}
'''
    entry = Entry(toolchain, journal, directory, source, [*MODULES, *flags])
    assert entry.run('skipped', {'go': skip, 'ok': False, 'eager': False}) == {'result': skip}
    entry.run('evaluated', {'go': skip, 'ok': False, 'eager': True},
              refuses='entry-host-run-failed')
    assert entry.run('accepted', {'go': skip, 'ok': True, 'eager': True}) == {'result': skip}


def test_formal_contract_and_execution_modes_refuse(toolchain, journal, directory):
    prefix = '''module sample;
 domain F=field("bls12-381.fr");
 protocol Run roles(P)(a:F@P)->(out:F@P){return a;} entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''
    for name, definition, code in [
        ('index-bound', 'math fn bad(a:F)->F {return zkc::symbolic::get<F,1,1>(zkc::symbolic::pack([a]));}', 'source.bound'),
        ('ordered-math', 'math fn bad(a:F)->F {return zkc::vector::sum(zkc::vector::fill(a,1));}', 'source.mode'),
        ('checked-matrix', 'math fn bad(m:zkc::matrix::Matrix<F>,r:index,c:index)->F {return zkc::matrix::get(m,r,c);}', 'source.mode'),
        ('checked-array', 'math fn bad(a:zkc::field_array::Array<F,2>,i:index)->F {return zkc::field_array::get(a,i);}', 'source.mode'),
    ]:
        path = directory / f'{name}.zkc'
        path.write_text(prefix + definition)
        journal.run([toolchain.compiler, 'language-check', '--source-format=zkc',
                     '--entry=sample::Demo', f'--module=sample={path}', *MODULES], refuses=code)


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_two_adic_height_bound_covers_the_index_carrier(toolchain, journal, directory, flags):
    source = '''module sample;
use zkc::indices::{two_adic};
protocol Check roles(P)(height:index@P)->(small:bool@P,full:bool@P,empty:bool@P) {
  return (small=two_adic<4>(height),full=two_adic<63>(height),empty=two_adic<0>(height));
}
entry fn Demo(inputs: Check::Inputs) { return Check::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, [*library_modules(*core_packages()), *flags])
    for height in [0, 1, 2, 3, 16, 32, (1 << 63) - 1, 1 << 63, (1 << 64) - 1]:
        is_power = height >= 2 and height & (height - 1) == 0
        assert entry.run(f'height-{height}', {'height': str(height)}) == {
            'small': is_power and height <= 16, 'full': is_power, 'empty': False}


@pytest.mark.parametrize('flags', [[], ['--no-simplify']])
def test_batched_opening_equations_match_independent_rotated_polynomials(
        toolchain, journal, directory, flags):
    source = '''module sample;
use zkc::vector::{Vector};
use zkc::indices::{Indices};
use zkc::opening as opening;
domain F=field("koala-bear");
protocol Check roles(P)(columns:Vector<F>@P,selected:Indices@P,rotations:Indices@P,
 values:Vector<F>@P,initial:Vector<F>@P,row:Vector<F>@P,position:index@P,initial_at:F@P)
 ->(word:Vector<F>@P,weight:F@P,value:F@P,row_weight:F@P) {
 let geometry=zkc::coset::coset_domain<F>(3,8);
 let input=opening::bind_openings(geometry,2,4,7,zkc::opening_claims::checked(selected, rotations, values));
 let whole=opening::deep_columns(zkc::coset::column_batch(geometry,2,columns),input,
   opening::vector_accumulator(geometry,11,initial,5));
 let at=opening::deep_row(opening::query_row(geometry,2,position,row),input,
   opening::scalar_accumulator(geometry,position,11,initial_at,5));
 return (word=opening::vector_values(whole),weight=opening::vector_weight(whole),
   value=opening::scalar_value(at),row_weight=opening::scalar_weight(at));
}
entry fn Demo(inputs: Check::Inputs) { return Check::run(inputs); }
'''
    entry = Entry(toolchain, journal, directory, source, [*library_modules(*core_packages()), *flags])
    p = 2130706433
    root = pow(1791270792, (1 << 24) // 8, p)
    assert pow(root, 8, p) == 1 and pow(root, 4, p) == p - 1
    points = [3 * pow(root, i, p) % p for i in range(8)]
    polynomials = [[2, 3, 1], [7, 0, 4]]

    def evaluate(coefficients, x):
        return sum(coefficient * pow(x, i, p) for i, coefficient in enumerate(coefficients)) % p

    tables = [[evaluate(coefficients, x) for x in points] for coefficients in polynomials]
    selected, rotations = [1, 0, 1], [0, 1, 3]
    opening_points = [7 * pow(root, 2 * r, p) % p for r in rotations]
    values = [evaluate(polynomials[column], at) for column, at in zip(selected, opening_points)]
    initial = [(x + 9) % p for x in points]
    expected = [(initial[i] + sum(5 * pow(11, j, p) * (tables[column][i] - value)
                * pow((x - at) % p, -1, p)
                for j, (column, at, value) in enumerate(zip(selected, opening_points, values)))) % p
                for i, x in enumerate(points)]
    base = {'columns': sum(tables, []), 'selected': selected, 'rotations': rotations,
            'values': values, 'initial': initial}
    for i, x in enumerate(points):
        inputs = base | {'row': [table[i] for table in tables], 'position': i, 'initial_at': initial[i]}
        assert entry.run(f'row-{i}', inputs) == {
            'word': vector(expected), 'weight': str(5 * 11**3),
            'value': str(expected[i]), 'row_weight': str(5 * 11**3)}
    empty = inputs | {'selected': [], 'rotations': [], 'values': []}
    assert entry.run('empty', empty) == {
        'word': vector(initial), 'weight': '5', 'value': str(initial[-1]), 'row_weight': '5'}
    for name, changed in [('rotation-count', {'rotations': [0]}),
                          ('claim-count', {'values': values[:-1]}),
                          ('column-index', {'selected': [2, 0, 1]}),
                          ('row-width', {'row': [0]}),
                          ('accumulator', {'initial': initial[:-1]})]:
        entry.run(name, inputs | changed, refuses='entry-host-run-failed')
    entry.run('empty-accumulator', empty | {'initial': []}, refuses='entry-host-run-failed')
