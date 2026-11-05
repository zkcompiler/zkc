"""Layout data premises reach native preparation and the ordinary Rust Host."""
import hashlib
import json
from pathlib import Path

import pytest

from entry import joint_package

FIXTURE = (Path(__file__).resolve().parents[3] /
           'compiler/test/fixtures/layout/data-requirements/helpers.zkc')


@pytest.mark.parametrize('predicate', [
    'same(xs, ys)',
    'apply(xs, ys, fn(left, right) => same(left, right))',
    'apply(xs, ys, same_fixed)',
    'apply(xs, ys, same<2, 2>)',
])
@pytest.mark.parametrize('flags', [(), ('--no-simplify',)])
def test_layout_data_premises_execute(toolchain, journal, directory, predicate, flags):
    source = directory / 'premises.zkc'
    source.write_text(FIXTURE.read_text() + f'''
pub protocol Run roles(P)(xs: Array<2> @P, ys: Array<2> @P) -> (bool, F) @P:
    return ({predicate}, total(xs, ys))
entry def Main(inputs: Run::Inputs):
    outputs <- Run::run(inputs)
    return outputs
''')
    encoded = journal.run([
        toolchain.compiler, 'language-package', '--source-format=zkc-layout',
        '--entry=m::Main', f'--module=m={source}', *flags,
    ])
    original = joint_package(json.loads(encoded))['original']
    assert '"data.finite_fold"' in original
    package = directory / 'premises.zkpkg'
    package.write_text(encoded)
    pin = hashlib.sha256(package.read_bytes()).hexdigest()
    inputs = journal.write('inputs.json', {'inputs': {'P': {
        'xs': ['2', '3'], 'ys': ['5', '7'],
    }}})
    output = directory / 'outputs.json'
    result = journal.json([
        toolchain.runtime, '--json', 'run', f'--package={package}',
        f'--sha256={pin}', f'--input={inputs}', f'--results={output}',
    ])
    assert result['status'] == 'executed'
    assert json.loads(output.read_text())['value']['P']['result'] == [True, '14']
    invalid = journal.write('invalid.json', {'inputs': {'P': {
        'xs': ['2', '3'], 'ys': ['5'],
    }}})
    refused_output = directory / 'invalid-outputs.json'
    journal.json([
        toolchain.runtime, '--json', 'run', f'--package={package}',
        f'--sha256={pin}', f'--input={invalid}', f'--results={refused_output}',
    ], refuses='entry-input-shape')
    assert not refused_output.exists()


@pytest.mark.parametrize('declaration', [
    'def bad(xs: Array<2>, ys: Array<3>) -> bool:\n    return same(xs, ys)\n',
    'def bad(xs: Array<2>, i: index) -> F:\n    return bounded_unit(xs, i)\n',
])
def test_layout_unproved_constraints_are_refused(toolchain, journal, directory, declaration):
    source = directory / 'invalid.zkc'
    source.write_text(FIXTURE.read_text() + declaration)
    journal.run([
        toolchain.compiler, 'language-check', '--source-format=zkc-layout',
        f'--module=m={source}',
    ], refuses='source.data-bound')


@pytest.mark.parametrize('flags', [(), ('--no-simplify',)])
def test_layout_symbolic_projection_callbacks_execute(toolchain, journal, directory, flags):
    source = directory / 'projections.zkc'
    source.write_text(FIXTURE.with_name('projections.zkc').read_text())
    package = directory / 'projections.zkpkg'
    package.write_text(journal.run([
        toolchain.compiler, 'language-package', '--source-format=zkc-layout',
        '--entry=m::Main', f'--module=m={source}', *flags,
    ]))
    pin = hashlib.sha256(package.read_bytes()).hexdigest()
    inputs = journal.write('inputs.json', {'inputs': {'P': {'xs': ['1', '2', '3', '4']}}})
    output = directory / 'outputs.json'
    result = journal.json([
        toolchain.runtime, '--json', 'run', f'--package={package}',
        f'--sha256={pin}', f'--input={inputs}', f'--results={output}',
    ])
    assert result['status'] == 'executed'
    assert json.loads(output.read_text())['value']['P']['result'] == [True] * 7
    invalid = journal.write('invalid.json', {'inputs': {'P': {'xs': ['1', '2', '3']}}})
    refused_output = directory / 'invalid-outputs.json'
    journal.json([
        toolchain.runtime, '--json', 'run', f'--package={package}',
        f'--sha256={pin}', f'--input={invalid}', f'--results={refused_output}',
    ], refuses='entry-input-shape')
    assert not refused_output.exists()
