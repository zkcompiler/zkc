"""Immutable table metadata and reached polynomial execution through source and Host.

These are ordinary supported Bundle declarations: optional fixed/configured
heights and finite windows. Metadata does not admit supplied data or claim
whole-Bundle satisfaction; the separate admission tests own those obligations.
"""
import json

import pytest

from test_relation_table_polynomial import (
    BUNDLE, Client, base, frame, points, reference, stopped, unframe,
)

SOURCE = '''
module polynomial_view;
domain Base = field("koala-bear");
domain Extension = field("koala-bear.ext8-binomial3");
domain Recurrence = bundle(asset recurrence);
type Vector<F: Field> = builtin("vector", F);

fn widths<F: Field, B: Bundle>() -> (index, index, index) {
  return kernel<F,0>("relation.table_widths"; B);
}
fn active<F: Field, B: Bundle>(present: bool, height: index) -> index {
  return if present {
    let value = kernel<F,0>("CONTRACT", OPERANDS; B);
    value.0
  } else { 0 };
}
fn point<F: Field, B: Bundle>(assignment: Vector<F>) -> Vector<F> {
  return kernel<F,0>("relation.table_point", assignment; B);
}
fn batch<F: Field, B: Bundle>(assignment: Vector<F>) -> Vector<F> {
  return kernel<F,0>("relation.table_points", assignment, 1; B);
}
protocol View roles(Evaluator)
    (present: bool @Evaluator, height: index @Evaluator,
     assignment: Vector<Extension> @Evaluator)
    -> (base_widths: (index, index, index) @Evaluator,
        extension_widths: (index, index, index) @Evaluator,
        active: index @Evaluator, point: Vector<Extension> @Evaluator,
        batch: Vector<Extension> @Evaluator) {
  let b @Evaluator = widths<Base,Recurrence>();
  let e @Evaluator = widths<Extension,Recurrence>();
  let a @Evaluator = active<Extension,Recurrence>(present, height);
  let p @Evaluator = point<Extension,Recurrence>(assignment);
  let q @Evaluator = batch<Extension,Recurrence>(assignment);
  return (base_widths = b, extension_widths = e, active = a, point = p, batch = q);
}
run Polynomial = View;
'''


@pytest.mark.parametrize('contract,operands', [
    ('relation.table_shape', 'height'),
    ('relation.table_input', 'height, 0'),
    ('relation.table_scope', 'height, 0'),
])
@pytest.mark.parametrize('policy,height,window,code', [
    (['fixed', 1], 1, False, 'bundle-polynomial-two-adic'),
    (['fixed', 3], 3, False, 'bundle-polynomial-two-adic'),
    (['config', 3, 3, False], 3, False, 'bundle-polynomial-two-adic'),
    (['config', 1, 8, False], 2, True, 'bundle-window'),
])
def test_metadata_and_substitution_admit_untaken_polynomial_references(
        toolchain, journal, directory, contract, operands, policy, height, window, code):
    document = json.loads(BUNDLE)
    table = document[3][0]
    table[1] = 'optional'
    table[2] = policy
    # Additional unused groups still count in immutable metadata.
    table[4] += [['w', 'witness', 'koala-bear', 2],
                 ['c', 'config', 'koala-bear', 3],
                 ['p', 'public', 'koala-bear', 2]]
    if window:
        table[3] = 'finite'
        # This window is valid at height 3 but reaches a missing next row at
        # height 2. Unlike a next-row read on the last row at every height,
        # the declaration itself is well formed.
        for assertion in table[7]:
            assertion[1] = ['interval', 0, 2]
    source = SOURCE.replace('CONTRACT', contract).replace('OPERANDS', operands)
    client = Client(toolchain, journal, directory, source, document)
    assignment = points(701, 11)
    request = {'present': False, 'height': height,
               'assignment': frame(assignment, extension=True)}
    result = client.run('absent-branch', request)
    assert result['base_widths'] == result['extension_widths'] == ['6', '4', '2']
    assert result['active'] == '0'
    assert unframe(result['point'], extension=True) == reference(assignment)
    assert result['point'] == result['batch']
    failed = client.run('reached-height', request | {'present': True},
                        refuses='entry-run-incomplete')
    assert stopped(failed) == f'refused:{code}'
    if policy[0] == 'fixed':
        failed = client.run('substituted-height', request | {'present': True, 'height': 8},
                            refuses='entry-run-incomplete')
        assert stopped(failed) == 'refused:bundle-height'


def test_widths_keep_extension_elements_and_static_carrier_checks(
        toolchain, journal, directory):
    document = json.loads(BUNDLE.replace('"koala-bear"', '"koala-bear.ext8-binomial3"'))
    document[3][0][2] = ['fixed', 3]
    source = SOURCE.replace('CONTRACT', 'relation.table_shape').replace('OPERANDS', 'height')
    source = source.replace('widths<Base,', 'widths<Extension,')
    client = Client(toolchain, journal, directory, source, document)
    result = client.run('extension-elements', {
        'present': False, 'height': 3, 'assignment': frame([base(0)] * 11, extension=True),
    })
    assert result['extension_widths'] == ['4', '1', '0']
    # Width-only static references also reject narrowing and unknown indices.
    width_only = '''
module polynomial_view;
domain Base = field("koala-bear");
domain Recurrence = bundle(asset recurrence);
fn widths<B: Bundle>() -> (index, index, index) {
  return kernel<Base,0>("relation.table_widths"; B);
}
protocol View roles(Evaluator)(unused: index @Evaluator)
    -> (widths: (index, index, index) @Evaluator) {
  let w @Evaluator = widths<Recurrence>();
  return (widths = w);
}
run Polynomial = View;
'''
    Client(toolchain, journal, directory, width_only, document, refuses='source.asset-carrier')
    Client(toolchain, journal, directory, width_only.replace('kernel<Base,0>', 'kernel<Base,1>'),
           json.loads(BUNDLE), refuses='source.asset-table')
