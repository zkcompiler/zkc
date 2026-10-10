"""The verifier's known columns and scalars bind the statement at the OOD point."""
import pytest

from test_air_stark import P, scalar, vector
from test_air_stark_adversarial import build, prove, rejected, verify


# w_i = configuration_{i+1} + public_column_i + x0 on [2,6).
# The second, deliberately nonzero assertion has an empty interval. Cyclic
# reads, a rotated configuration column and a public group all reach the
# source argument's known-slot and scoped-quotient paths.
BUNDLE = ['zkc.relation-bundle/0', [['x0', 'koala-bear']], [], [[
    'scoped', 'required', ['fixed', 8], 'cyclic',
    [['trace', 'witness', 'koala-bear', 1],
     ['configuration', 'config', 'koala-bear', 1],
     ['public-column', 'public', 'koala-bear', 1]],
    ['zkc.ring/0', ['koala-bear'] * 4,
     [['input', 0], ['input', 1], ['input', 2], ['input', 3],
      ['neg', 1], ['add', 0, 4], ['neg', 2], ['add', 5, 6],
      ['neg', 3], ['add', 7, 8]], [9, 0]],
    [['read', 0, '0', 0], ['read', 1, '1', 0],
     ['read', 2, '0', 0], ['public', 0]],
    [[0, ['interval', 2, 6]], [1, ['interval', 3, 3]]], []]]]

SOURCE = '''module air_stark_example;
use air_stark::{Base, Extension, Statement, TableArgument};
use air_polynomial::{Vector};
domain Scoped = bundle(asset scoped);

relation ScopedRelation(statement x0: Base, witness trace: Vector<Base>,
    parameter configuration: Vector<Base>, statement public_columns: Vector<Base>)
  = bundle(asset scoped);

fn statement(configuration: Vector<Base>, public_columns: Vector<Base>,
    x0: Base, shift: Base) -> Statement {
  let public_data = kernel<Base>("vector.fill", x0, 1);
  return Statement { configuration, public_columns, public_data, shift };
}

protocol ScopedProof roles(P,V)
    (trace: Vector<Base> @P, private_configuration: Vector<Base> @P,
     private_columns: Vector<Base> @P, private_x0: Base @P,
     configuration: Vector<Base> @(P,V), public_columns: Vector<Base> @(P,V),
     x0: Base @(P,V), shift: Base @(P,V), round_count: index @(P,V),
     query_count: index @(P,V), attempt_count: index @(P,V),
     coins: Random<Extension> @V) -> (accepted: bool @V)
    spec {
      target constraints = ScopedRelation(in.x0@V, in.trace,
        in.configuration@V, in.public_columns@V) accept out.accepted;
    } {
  let statementP @P = statement(private_configuration, private_columns, private_x0, shift);
  let statementV @V = statement(configuration, public_columns, x0, shift);
  let accepted = TableArgument<0,Scoped,3,5,8,8>(trace, statementP,
    statementV, round_count, query_count, attempt_count, coins);
  return (accepted = accepted);
}

proof Proof = ScopedProof {
  prover P;
  verifier V;
  public { configuration, public_columns, x0, shift,
    round_count, query_count, attempt_count };
  accept accepted;
  target constraints;
  construction fiat_shamir("merlin3.koala-bear.ext8-binomial3.rejection31le/0", coins);
}
'''


def witness(configuration, columns, x0):
    # Deliberately arbitrary outside the active interval: enforcing the
    # assertion on all rows or on the empty interval would reject this trace.
    trace = [(columns[i] + configuration[(i + 1) % 8] + x0) % P
             if 2 <= i < 6 else 100 + i for i in range(8)]
    return {'trace': vector(trace), 'private_configuration': vector(configuration),
            'private_columns': vector(columns), 'private_x0': scalar(x0)}


@pytest.mark.parametrize('authority', ['configuration', 'public_columns', 'public_scalar'])
def test_private_prover_statement_cannot_replace_verifier_inputs(
        toolchain, journal, directory, authority):
    configuration = [2 * i + 7 for i in range(8)]
    columns = [i * i + 3 for i in range(8)]
    x0 = 5
    public = {'configuration': vector(configuration), 'public_columns': vector(columns),
              'x0': scalar(x0), 'shift': scalar(3), 'round_count': 3,
              'query_count': 8, 'attempt_count': 8}
    bundle = journal.write('scoped.json', BUNDLE)
    variant = build(toolchain, journal, directory, 'scoped', main=SOURCE,
                    asset=('scoped', bundle))
    honest = prove(toolchain, journal, variant, 'honest', public,
                   witness(configuration, columns, x0))
    assert verify(toolchain, journal, variant, 'honest', public, honest)['status'] == 'accepted'

    # The prover supplies a valid trace and quotient for its OWN data, while
    # the public statement and transcript root still name the verifier's data.
    # Thus neither an honest-prover refusal nor header replay can catch this.
    if authority == 'configuration':
        configuration[4] += 1
    elif authority == 'public_columns':
        columns[3] += 1
    else:
        x0 += 1
    false_private = witness(configuration, columns, x0)
    proof = prove(toolchain, journal, variant, 'foreign', public, false_private)
    checked = verify(toolchain, journal, variant, 'foreign', public, proof,
                     refuses='artifact-stopped')
    assert rejected(checked, variant.guards) == ('identity', [])

    # Isolate the known-slot equality from the quotient equation: weakening
    # precisely that equality accepts the same false statement. Production
    # library sources are never changed by this control.
    unchecked = build(toolchain, journal, directory, 'unchecked', main=SOURCE,
                      asset=('scoped', bundle), edits=[('air_table',
                      '      known = both(known, get(assignments, slot) == expected);',
                      '      known = both(known, true);')])
    forged = prove(toolchain, journal, unchecked, 'foreign', public, false_private)
    assert verify(toolchain, journal, unchecked, 'foreign', public, forged)['status'] == 'accepted'
