"""Prover-only cheating against the imported AIR argument, stopped at exact guards.

Each case changes only what the prover computes or commits, so the resulting
proof has its own consistent commitments, folds and transcript, and rejection
has to come from the verifier obligation under test. Guard sites are read from
each variant's own emitted program. These are regression controls for specific
obligations, not a soundness bound.
"""
import json
from pathlib import Path
import re
from typing import NamedTuple

import pytest

from test_air_stark import (EXAMPLE, FIXTURE, P, ROOT, STARK, TABLE, frames, inputs,
                            request, scalar, unpack, vector)

POLYNOMIAL = ROOT / 'libraries/air/polynomial.zkc'
FRI = ROOT / 'libraries/fri/lib.zkc'
# The guards of TableArgument and of LowDegree in source order, each named by
# its owner and the number of loops around it, as the FRI tests name theirs.
TABLE_GUARDS = [('profile', 'V', 0), ('prover_profile', 'P', 0), ('identity', 'V', 0),
                ('fri', 'V', 0), ('trace', 'V', 1), ('quotient', 'V', 1), ('deep', 'V', 1)]
FRI_GUARDS = [('schedule', 'V', 0), ('input', 'P', 0), ('final_degree', 'V', 0),
              ('low', 'V', 2), ('high', 'V', 2), ('chain', 'V', 2), ('terminal', 'V', 1)]
GUARD = re.compile(r'"protocol\.guard"\(%\d+(?:#\d+)?\) <\{owner = "(\w+)", site = "(s\d+)"\}>')
APPLY = re.compile(r'"protocol\.apply"\(.*\) <\{callee = @(\w+), roles = \[[^\]]*\], site = "(s\d+)"\}>')
FUNCTION = re.compile(r'"(protocol|local)\.func"\(\) <\{.*sym_name = "(\w+)"')
ORIGIN = re.compile(r'^\}\) \{logical_origin = \["(\w+)", \[\]\]\}')


class Variant(NamedTuple):
    package: Path
    pin: str
    guards: dict  # guard name -> source-site chain from the entry's apply
    functions: dict  # local function origin -> generated symbol


def emitted_sites(emitted):
    """The guard chains of TableArgument and LowDegree, read from the emitted program.

    A verifier stop names the chain of source sites from the entry's apply of
    TableArgument down to the guard, so each guard is keyed by that chain.
    Both protocols must keep the library's guard shape, which also shows that
    a prover-only variant left the verifier's checks in place.
    """
    functions, symbols, regions, current, symbol = {}, {}, [], None, None
    for line in emitted.splitlines():
        text = line.strip()
        header = FUNCTION.search(text)
        if header:
            symbol = header.group(2)
            if header.group(1) == 'protocol':
                current = functions[symbol] = {'guards': [], 'applies': []}
        origin = ORIGIN.match(text)
        if origin:
            symbols[origin.group(1)] = symbol
        guard = GUARD.search(text)
        if guard:
            current['guards'].append((guard.group(1), guard.group(2), regions.count('repeat')))
        applied = APPLY.search(text)
        if applied:
            current['applies'].append(applied.groups())
        if text.endswith('({'):
            regions.append('repeat' if '"protocol.repeat"' in text else 'other')
        elif text.startswith('})'):
            regions.pop()
    assert not regions

    def shaped(callee, expected):
        return ([(owner, depth) for owner, _, depth in functions[callee]['guards']]
                == [(owner, depth) for _, owner, depth in expected])
    (entry,) = [f for f in functions.values() if not f['guards'] and len(f['applies']) == 1]
    ((table, table_site),) = entry['applies']
    assert shaped(table, TABLE_GUARDS)
    ((fri, fri_site),) = [a for a in functions[table]['applies'] if shaped(a[0], FRI_GUARDS)]
    guards = {name: f'{table_site}_{site}' for (name, _, _), (_, site, _)
              in zip(TABLE_GUARDS, functions[table]['guards'], strict=True)}
    guards.update({'fri.' + name: f'{table_site}_{fri_site}_{site}' for (name, _, _), (_, site, _)
                   in zip(FRI_GUARDS, functions[fri]['guards'], strict=True)})
    return guards, symbols


def local_symbol(variant, module, name):
    """The generated symbol of one source function, by its retained origin."""
    (symbol,) = [symbol for origin, symbol in variant.functions.items()
                 if re.search(rf'{module}\d+_{name}$', origin)]
    return symbol


def rejected(report, guards):
    """The guard at which V stopped, 'name' or 'fri.name', and the loop iterations around it."""
    stop = report['execution']['stop']
    assert report['status'] == 'refused' and stop['role'] == 'V', stop
    assert stop['kind'] == 'Explicit("reject")', stop
    path = stop['origin'][4]
    assert path[-1] == ['if', 'guard_control', 'else'], path
    chain = re.fullmatch(r'(?:apply_\d+_)+((?:s\d+_)*s\d+)', stop['site']).group(1)
    names = {chain: name for name, chain in guards.items()}
    return names[chain], [frame[2] for frame in path if frame[0] == 'loop']


def build(toolchain, journal, directory, name, *, main=None, asset=None, edits=(), appended=()):
    """One package from the example and the libraries, and its guard chains.

    Exact single-hit substitutions and appended helper text are the variant's
    only difference from the shipped sources, so a drifted library fails here
    rather than building something else.
    """
    where = directory / name
    where.mkdir()
    texts = {'air_stark_example': EXAMPLE.read_text() if main is None else main,
             'air_stark': STARK.read_text(), 'air_table': TABLE.read_text(),
             'air_polynomial': POLYNOMIAL.read_text(), 'fri': FRI.read_text()}
    for module, old, new in edits:
        assert texts[module].count(old) == 1, (module, old)
        texts[module] = texts[module].replace(old, new)
    for module, extra in appended:
        texts[module] += '\n' + extra
    arguments = []
    for module, text in texts.items():
        path = where / f'{module}.zkc'
        path.write_text(text)
        arguments.append(f'--module={module}={path}')
    label, bundle = asset or ('recurrence', FIXTURE / 'bundle.json')
    arguments.append(f'--asset={label}=relation-bundle-json={bundle}')
    package = where / 'Proof.zkpkg'
    report = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                           *arguments, 'air_stark_example::Proof', f'--output={package}'])
    emitted = journal.run([toolchain.compiler, 'language-emit', '--source-format=zkc',
                           '--entry=air_stark_example::Proof', *arguments])
    return Variant(package, report['package_sha256'], *emitted_sites(emitted))


def prove(toolchain, journal, variant, name, public, private):
    """A proof the variant's prover must produce, with the honest message count."""
    label = f'{variant.package.parent.name}-{name}'
    producer = request(journal, label + '-producer', public, private)
    proof = variant.package.with_name(name + '.bin')
    made = journal.json([toolchain.runtime, 'prove', f'--package={variant.package}', f'--sha256={variant.pin}', *producer, f'--output={proof}'])
    assert made['status'] == 'produced'
    assert len(frames(proof.read_bytes())) == 8 + 16 * public['query_count']
    return proof


def verify(toolchain, journal, variant, name, public, proof, *, refuses=None):
    label = f'{variant.package.parent.name}-{name}'
    verifier = request(journal, label + '-verifier', public)
    return journal.json([toolchain.runtime, 'verify', f'--package={variant.package}', f'--sha256={variant.pin}', *verifier, f'--proof={proof}'],
                        refuses=refuses)


# The prover's own coefficient bound in split_quotient, replaced by silent
# truncation to the chunk capacity.
TRUNCATION = ('air_polynomial',
              '  require not(less(capacity, actual));\n'
              '  let padded = concat(coefficients, fill<F>(0, capacity - actual));',
              '  let padded = slice(concat(coefficients, fill<F>(0, capacity)), 0, capacity);')


def test_false_trace_with_truncated_quotient_stops_at_identity(toolchain, journal, directory):
    # A trace violating the relation has a quotient of too high a degree. The
    # shipped prover refuses it at its own coefficient bound, so no proof
    # exists and no verifier guard is reached. A prover that truncates the
    # coefficients instead commits to a wrong quotient; the identity at zeta
    # is the first verifier guard that can see a false statement.
    public, private = inputs()
    trace = unpack(private['trace'])
    trace[4 * 3 + 1] = (trace[4 * 3 + 1] + 1) % P
    false_private = {'trace': vector(trace)}
    shipped = build(toolchain, journal, directory, 'shipped')
    producer = request(journal, 'shipped-false-producer', public, false_private)
    refused = shipped.package.with_name('false.bin')
    made = journal.attempt([toolchain.runtime, 'prove', f'--package={shipped.package}', f'--sha256={shipped.pin}', *producer, f'--output={refused}'])
    assert made.returncode == 1 and not refused.exists()
    report = json.loads(made.stdout)
    assert report['status'] == 'refused' and report['code'].startswith('artifact-stopped:')
    stop = report['execution']['stop']
    assert stop['role'] == 'P' and stop['kind'] == 'Explicit("reject")', stop
    assert stop['local']['function'] == local_symbol(shipped, 'air_polynomial', 'split_quotient')

    truncating = build(toolchain, journal, directory, 'truncating', edits=[TRUNCATION])
    proof = prove(toolchain, journal, truncating, 'false', public, false_private)
    checked = verify(toolchain, journal, truncating, 'false', public, proof, refuses='artifact-stopped')
    assert rejected(checked, truncating.guards) == ('identity', [])
    # The honest quotient fits the capacity, so truncation changes nothing for
    # it: the rejection above is the false statement, not the changed prover.
    honest = prove(toolchain, journal, truncating, 'honest', public, private)
    assert verify(toolchain, journal, truncating, 'honest', public, honest)['status'] == 'accepted'


USE_TABLE = ('use air_table::{shape, claims, quotient_values, opening_claims, '
             'identity, deep_word, deep_value};')
CLAIMS = ('  let proposed @P = claims<Extension,Table,B>(trace_baseP, config_baseP, public_baseP,\n'
          '    dataP, heightP, zetaP);')
QUOTIENT_CLAIMS = ('  let proposed_quotient @P = opening_claims(chunks, factsP.chunks, '
                   'shiftP, sizeP, zetaP);')
# Prover-only helpers: a claim that lies about one witness opening, and the
# verifier's own combined value at zeta recomputed so that the difference can
# be moved into the first chunk claim, whose recombination weight is one.
COMPENSATION = '''
pub fn bump_slot<F: Field>(assignments: Vector<F>, slot: index) -> Vector<F> {
  let mut result = empty<F>();
  for i in 0..length(assignments) {
    let value = get(assignments, i);
    let next = if i == slot { value + 1 } else { value };
    result = append(result, next);
  }
  return result;
}
pub fn combined_value<F: Field, Table: nat, B: Bundle>(assignments: Vector<F>,
    height: index, zeta: F, alpha: F) -> F {
  let facts = shape<F,Table,B>(height);
  let residuals = kernel<F,Table>("relation.table_point", assignments; B);
  let mut combined: F = 0;
  let mut weight: F = 1;
  for assertion in 0..facts.assertions {
    let interval = scope<F,Table,B>(height, assertion);
    if less(interval.0, interval.1) {
      combined = combined + weight * get(residuals, assertion) *
        inverse(vanishing(height, interval.0, interval.1, zeta));
      weight = weight * alpha;
    }
  }
  return combined;
}
pub fn compensate<F: Field, Table: nat, B: Bundle>(quotient_claims: Vector<F>,
    honest: Vector<F>, altered: Vector<F>, height: index, zeta: F, alpha: F) -> Vector<F> {
  let delta = combined_value<F,Table,B>(altered, height, zeta, alpha)
    - combined_value<F,Table,B>(honest, height, zeta, alpha);
  let mut result = empty<F>();
  for i in 0..length(quotient_claims) {
    let value = get(quotient_claims, i);
    let next = if i == 0 { value + delta } else { value };
    result = append(result, next);
  }
  return result;
}
'''


@pytest.mark.parametrize('compensated', [False, True], ids=['bare', 'compensated'])
def test_witness_claim_lie_consistent_at_zeta_stops_at_fri_degree(toolchain, journal, directory,
                                                                  compensated):
    # Slot 0 of the recurrence table reads witness column 0 at rotation 0, a
    # value the verifier never sees directly. Claiming it plus one fails the
    # identity at zeta. Moving the same difference into the first chunk claim
    # keeps that identity balanced, so the lie survives until the DEEP
    # quotient of the committed column against the wrong claim is no longer
    # a polynomial of low degree: FRI's terminal degree check stops it.
    bundle = json.loads((FIXTURE / 'bundle.json').read_text())
    assert bundle[3][0][6][0] == ['read', 0, '0', 0]
    helpers = 'bump_slot, compensate' if compensated else 'bump_slot'
    edits = [('air_stark', USE_TABLE, USE_TABLE.replace('deep_value}', f'deep_value, {helpers}}}')),
             ('air_stark', CLAIMS, CLAIMS.replace('let proposed @P', 'let honest @P')
              + '\n  let proposed @P = bump_slot(honest, natural<0>());')]
    if compensated:
        edits.append(('air_stark', QUOTIENT_CLAIMS,
                      QUOTIENT_CLAIMS.replace('let proposed_quotient @P', 'let honest_quotient @P')
                      + '\n  let proposed_quotient @P = compensate<Extension,Table,B>('
                      'honest_quotient, honest, proposed, heightP, zetaP, alphaP);'))
    variant = build(toolchain, journal, directory, 'lying', edits=edits,
                    appended=[('air_table', COMPENSATION)])
    public, private = inputs()
    proof = prove(toolchain, journal, variant, 'lying', public, private)
    checked = verify(toolchain, journal, variant, 'lying', public, proof, refuses='artifact-stopped')
    expected = ('fri.final_degree', []) if compensated else ('identity', [])
    assert rejected(checked, variant.guards) == expected


# One cyclic table of height 8 with a single witness column w and a public
# scalar x0, asserting w(gX) - w(X) on the interior and w(X) - x0 on the first
# row. Every honest column is the constant x0.
COLUMN_BUNDLE = ['zkc.relation-bundle/0', [['x0', 'koala-bear']], [], [[
    'main', 'required', ['fixed', 8], 'cyclic', [['main', 'witness', 'koala-bear', 1]],
    ['zkc.ring/0', ['koala-bear'] * 3,
     [['input', 0], ['input', 1], ['neg', 0], ['add', 1, 2], ['input', 2], ['neg', 4], ['add', 0, 5]],
     [3, 6]],
    [['read', 0, '0', 0], ['read', 0, '1', 0], ['public', 0]],
    [[0, ['interior', 0, 1]], [1, ['first']]], []]]]
COLUMN_MAIN = '''module air_stark_example;
use air_stark::{Base, Extension, Statement, TableArgument};
use air_polynomial::{Vector};
domain Column = bundle(asset column);

relation ConstantColumn(statement x0: Base, witness trace: Vector<Base>)
  = bundle(asset column);

fn statement(x0: Base, shift: Base) -> Statement {
  let public_data = kernel<Base>("vector.fill", x0, 1);
  let zero: Base = 0;
  let configuration = kernel<Base>("vector.fill", zero, 0);
  let public_columns = kernel<Base>("vector.fill", zero, 0);
  return Statement { configuration, public_columns, public_data, shift };
}

protocol ColumnProof roles(P,V)
    (trace: Vector<Base> @P, x0: Base @(P,V), shift: Base @(P,V), round_count: index @(P,V),
     query_count: index @(P,V), attempt_count: index @(P,V),
     coins: Random<Extension> @V) -> (accepted: bool @V)
    where Column::Tables <= 1, Column::Channels <= 0
    spec {
      target constraints = ConstantColumn(in.x0@V, in.trace) accept out.accepted;
    } {
  let statementP @P = statement(x0, shift);
  let statementV @V = statement(x0, shift);
  let accepted = TableArgument<0,Column,3,5,8,8>(trace, statementP,
    statementV, round_count, query_count, attempt_count, coins);
  return (accepted = accepted);
}

proof Proof = ColumnProof {
  prover P;
  verifier V;
  public { x0, shift, round_count, query_count, attempt_count };
  accept accepted;
  target constraints;
  construction fiat_shamir("merlin3.koala-bear.ext8-binomial3.rejection31le/0", coins);
}
'''
# Prover-only helpers: Z_H added to the one extended column raises its degree
# to exactly the height while leaving every row of H unchanged, and witness
# claims interpolated from that committed extension rather than from the
# trace, so the lifted column is claimed consistently at every opening point.
LIFT = '''
pub fn lift<F: Field>(values: Vector<F>, height: index, shift: F, size: index) -> Vector<F> {
  return add(values, vanishing_values(height, 0, height, shift, size));
}
'''
CLAIMS_FROM_EXTENSION = '''
pub fn claims_lde<F: Field, Table: nat, B: Bundle>(witness: Vector<F>,
    public_data: Vector<F>, height: index, shift: F, size: index, zeta: F) -> Vector<F> {
  let facts = shape<F,Table,B>(height);
  let mut assignments = empty<F>();
  for slot in 0..facts.inputs {
    let binding = descriptor<F,Table,B>(height, slot);
    let x = shifted_point(height, binding.2, zeta);
    let value = if binding.0 == 0 { get(public_data, binding.1) }
      else { column_at(witness, binding.1, size, x, shift) };
    assignments = append(assignments, value);
  }
  return assignments;
}
'''
USE_POLYNOMIAL = ('use air_polynomial::{Vector, length, natural, yes, both, not, less,\n'
                  '  point, transpose, extend_columns, split_quotient, disjoint_coset, '
                  'outside_domains};')
EXTENSION = ('let trace_lde @P = extend_columns(trace_columns, factsP.witness, heightP, '
             'statementP.shift, sizeP);')
LIFTED = [('air_stark', USE_POLYNOMIAL, USE_POLYNOMIAL.replace('outside_domains}', 'outside_domains, lift}')),
          ('air_stark', USE_TABLE, USE_TABLE.replace('deep_value}', 'deep_value, claims_lde}')),
          ('air_stark', EXTENSION, EXTENSION.replace('= extend_columns(', '= lift(extend_columns(')
           .replace('sizeP);', 'sizeP), heightP, statementP.shift, sizeP);')),
          ('air_stark', CLAIMS, '  let proposed @P = claims_lde<Extension,Table,B>('
                                'trace_extension, dataP, heightP, shiftP, sizeP, zetaP);')]
# The (1 + eta X) degree adjustment removed from both the prover's DEEP word
# and the verifier's DEEP value.
UNADJUSTED = [('air_table', '  return multiply(result, add(fill<F>(1, size), scale(xs, adjustment)));',
               '  return result;'),
              ('air_table', '  return result * (1 + adjustment * x);', '  return result;')]


def test_degree_adjustment_rejects_committed_column_of_degree_height(toolchain, journal, directory):
    # The prover commits T' = T + Z_H for the honest constant column T. T'
    # agrees with T on H, so every assertion holds and the quotient is
    # honest for T'; the claims are T' at the opening points, so the identity
    # at zeta holds and every DEEP quotient is a polynomial. Only the degree
    # of T' is wrong: exactly the height rather than below it. The (1 + eta X)
    # factor is what makes FRI's bound strict there. Without it at both
    # roles the same proof is accepted, while the honest column is accepted
    # with and without it.
    bundle = journal.write('column-bundle.json', COLUMN_BUNDLE)
    public = {'x0': scalar(5), 'shift': scalar(3), 'round_count': 3, 'query_count': 8,
              'attempt_count': 8}
    private = {'trace': vector([5] * 8)}
    helpers = [('air_polynomial', LIFT), ('air_table', CLAIMS_FROM_EXTENSION)]
    roots = {}
    for name, edits in [('honest', []), ('lifted', LIFTED), ('lifted-unadjusted', LIFTED + UNADJUSTED),
                        ('honest-unadjusted', UNADJUSTED)]:
        variant = build(toolchain, journal, directory, name, main=COLUMN_MAIN, asset=('column', bundle),
                        edits=edits, appended=helpers if name.startswith('lifted') else [])
        proof = prove(toolchain, journal, variant, name, public, private)
        roots[name] = frames(proof.read_bytes())[0]
        if name == 'lifted':
            checked = verify(toolchain, journal, variant, name, public, proof, refuses='artifact-stopped')
            assert rejected(checked, variant.guards) == ('fri.final_degree', [])
        else:
            assert verify(toolchain, journal, variant, name, public, proof)['status'] == 'accepted'
    # The trace root is sent before any challenge, so it depends only on the
    # committed column: the lifted column is a different commitment, and the
    # removed factor changes nothing about what is committed.
    assert roots['honest'] == roots['honest-unadjusted']
    assert roots['lifted'] == roots['lifted-unadjusted']
    assert roots['honest'] != roots['lifted']
