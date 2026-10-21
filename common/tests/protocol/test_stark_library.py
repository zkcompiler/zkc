"""The parameterized single-table STARK library at its KoalaBear configuration.

`stark::single_table::TableArgument` is generic over a `stark::configurations::contract::
Configuration`; these tests run it with `stark::configurations::koala_bear_quartic::Poseidon2`
(KoalaBear trace, quartic extension, Poseidon2 Merkle trees with pruned
multi-openings, natural layout with both fold siblings in one FRI leaf,
challenges derived from the octic KoalaBear Merlin suite) and with a second,
bit-reversed configuration written here. The AIRs are relation Bundles exported
by the Plonky3 and Clean adapters and a generated quadratic recurrence.

Honest proofs are accepted; altered proofs, changed public inputs, wrong
openings and two dishonest provers are refused. These are execution and
rejection controls, not a soundness bound.
"""
import json
from pathlib import Path

import pytest

from input_files import input_files
from source_modules import library_modules

ROOT = Path(__file__).resolve().parents[3]
PROJECT = ROOT / 'examples/projects/stark'
EXISTING = ROOT / 'examples/projects/fibonacci'
LIBRARY = ROOT / 'libraries/arguments/stark'
RECURRENCE = ROOT / 'compiler/adapters/plonky3/fixtures/recurrence'
SUITE = 'merlin3.koala-bear.ext8-binomial3.rejection31le/0'
P = 2130706433

# ZKCV value-frame tags (docs/spec/formats/messages.md).
BASE_VECTOR, QUARTIC_VECTOR, ROOT_FRAME, PROOF_FRAME = 20, 22, 71, 72


def frames(proof):
    offset, result = 40, []
    while offset < len(proof):
        count = int.from_bytes(proof[offset:offset + 8], 'little')
        result.append(proof[offset + 8:offset + 8 + count])
        offset += count + 8
    assert offset == len(proof)
    return result


def replace_frame(proof, position, value):
    messages = frames(proof)
    messages[position] = value
    return proof[:40] + b''.join(len(m).to_bytes(8, 'little') + m for m in messages)


def tag(frame):
    assert frame[:5] == b'ZKCV\x00'
    return frame[5]


def altered(frame):
    """The frame with its first canonical word incremented modulo p, or None
    when it has no word (an empty pruned proof). Framing stays canonical."""
    start = {BASE_VECTOR: 10, QUARTIC_VECTOR: 10, ROOT_FRAME: 6, PROOF_FRAME: 10}[tag(frame)]
    if len(frame) < start + 4:
        return None
    word = int.from_bytes(frame[start:start + 4], 'little')
    return frame[:start] + ((word + 1) % P).to_bytes(4, 'little') + frame[start + 4:]


def edited(directory, source, edits, name):
    """A copy of one library file with exact single-hit substitutions."""
    text = source.read_text()
    for old, new in edits:
        assert text.count(old) == 1, old
        text = text.replace(old, new)
    path = directory / name
    path.write_text(text)
    return path


class Package:
    def __init__(self, toolchain, journal, directory, command, name):
        self.tools, self.journal, self.directory, self.name = toolchain, journal, directory, name
        self.path = directory / f'{name}.zkpkg'
        report = journal.json([toolchain.runtime, '--json', 'compile',
                               f'--compiler={toolchain.compiler}', *command,
                               f'--output={self.path}'])
        self.pin = report['package_sha256']
        self.runs = 0

    @classmethod
    def project(cls, toolchain, journal, directory, project, entry, flags=()):
        return cls(toolchain, journal, directory,
                   [f'--project={project}/zkc.toml', f'example::{entry}', *flags],
                   f'{project.name}-{entry}')

    @classmethod
    def source(cls, toolchain, journal, directory, source, assets, *, overrides=None,
               flags=(), name='variant'):
        path = directory / f'{name}.zkc'
        path.write_text(source)
        return cls(toolchain, journal, directory,
                   [f'--module=example={path}', *library_modules('arguments/stark/configurations/contract', 'arguments/stark/configurations/koala_bear_octic', 'arguments/stark/configurations/koala_bear_quartic', 'arguments/stark/sampling', 'arguments/stark/single_table', 'arguments/stark/single_table/koala_bear_octic', 'arguments/stark/whole_bundle', overrides=overrides),
                    *[f'--asset={k}=relation-bundle-json={v}' for k, v in assets.items()],
                    'example::Proof', *flags], name)

    def request(self, public, witness=None):
        self.runs += 1
        return input_files(self.journal, f'{self.name}-{self.runs}.json', public=public,
                           witness=witness or {})

    def prove(self, public, witness, *, refuses=None, capacity=None):
        proof = self.directory / f'{self.name}-{self.runs + 1}.proof'
        extra = [f'--capacity={capacity}'] if capacity else []
        report = self.journal.json([self.tools.runtime, '--json', 'prove', f'--package={self.path}',
                                    f'--sha256={self.pin}', *self.request(public, witness),
                                    f'--output={proof}', *extra], refuses=refuses)
        return report, proof

    def verify(self, public, proof, *, refuses=None, capacity=None):
        extra = [f'--capacity={capacity}'] if capacity else []
        return self.journal.json([self.tools.runtime, '--json', 'verify', f'--package={self.path}',
                                  f'--sha256={self.pin}', *self.request(public),
                                  f'--proof={proof}', *extra], refuses=refuses)

    def honest(self, public, witness, capacity=None):
        produced, proof = self.prove(public, witness, capacity=capacity)
        assert produced['status'] == 'produced'
        assert self.verify(public, proof, capacity=capacity)['status'] == 'accepted'
        return proof


def fibonacci_inputs(entry):
    folder = PROJECT / 'inputs' / f'example.{entry}'
    return (json.loads((folder / 'public.json').read_text()),
            json.loads((folder / 'witness.json').read_text()))


def rejected(report):
    """A verifier that ran and stopped at one of its own checks."""
    assert report['status'] == 'refused', report
    assert report['code'].startswith('artifact-stopped'), report
    stop = report['execution']['stop']
    assert stop['kind'] == 'Explicit("reject")', stop
    return stop


def expected_frames(rounds):
    # Trace and quotient roots, trace and quotient claims, one root per FRI
    # round and the final polynomial; then trace rows and proof, quotient rows
    # and proof, and one sibling vector and proof per round.
    return [ROOT_FRAME, ROOT_FRAME, QUARTIC_VECTOR, QUARTIC_VECTOR, *[ROOT_FRAME] * rounds,
            QUARTIC_VECTOR, BASE_VECTOR, PROOF_FRAME, QUARTIC_VECTOR, PROOF_FRAME,
            *[QUARTIC_VECTOR, PROOF_FRAME] * rounds]


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--no-finite-bulk'], ['--release-storage']])
@pytest.mark.parametrize('entry', ['Plonky3Proof', 'CleanProof'])
def test_example_entries_prove_and_verify(toolchain, journal, directory, entry, flags):
    package = Package.project(toolchain, journal, directory, PROJECT, entry, flags)
    public, witness = fibonacci_inputs(entry)
    proof = package.honest(public, witness)
    messages = frames(proof.read_bytes())
    assert [tag(m) for m in messages] == expected_frames(3)
    # Eight query positions open one row and one FRI pair per round each; the
    # trace rows carry the two Fibonacci columns and the final polynomial has
    # one coefficient.
    assert len(messages[7]) == 10 + 16
    assert int.from_bytes(messages[8][6:10], 'little') == 8 * 2


def quadratic_air(height, width):
    """The benchmark recurrence x' = x^2 + c + 1 per column, with first and
    last rows bound to public values, as a one-table Bundle."""
    import importlib.util
    spec = importlib.util.spec_from_file_location('ring_arena', ROOT / 'compiler/adapters/ring_arena.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    arena = module.Arena()
    outputs, assertions = [], []
    for col in range(width):
        current = arena.input('koala-bear', ['read', 0, '0', col])
        following = arena.input('koala-bear', ['read', 0, '1', col])
        initial = arena.input('koala-bear', ['public', col])
        final = arena.input('koala-bear', ['public', width + col])
        for value, selector in ((current - initial, ['first']), (current - final, ['last']),
                                (following - current * current - (col + 1), ['interior', 0, 1])):
            assertions.append([len(outputs), selector])
            outputs.append(value)
    ring, bindings = arena.finish(outputs)
    bundle = ['zkc.relation-bundle/0', [[f'public-{i}', 'koala-bear'] for i in range(2 * width)], [],
              [['trace', 'required', ['fixed', height], 'cyclic',
                [['trace', 'witness', 'koala-bear', width]], ring, bindings, assertions, []]]]
    current = [(7919 * (c + 3)) % P for c in range(width)]
    initial, trace = current, []
    for _ in range(height):
        trace.extend(current)
        final = current
        current = [(x * x + i + 1) % P for i, x in enumerate(current)]
    return bundle, [str(v) for v in initial + final], [str(v) for v in trace]


GENERATED = '''module example;
use stark::configurations::koala_bear_octic::{Base, Extension};
use stark::configurations::koala_bear_quartic::{Poseidon2};
use stark::single_table::{Statement, TableArgument};
use zkc::vector::{Vector};
use zkc::vector as v;
domain Trace = bundle(asset trace);
fn statement(public_data: Vector<Base>) -> Statement<Base> {
  return Statement<Base> { configuration: v::empty<Base>(), public_columns: v::empty<Base>(), public_data };
}
protocol Air roles(P,V)(trace: Vector<Base> @P, public_data: Vector<Base> @(P,V),
    coins: Random<Extension> @V) -> (accepted: bool @V) {
  let prover @P = statement(public_data);
  let verifier @V = statement(public_data);
  let accepted = TableArgument<CONFIGURATION, 0, Trace, LogFinal = FINAL, Rounds = ROUNDS,
    LogBlowup = BLOWUP, Queries = QUERIES>(trace, prover, verifier, coins);
  return accepted;
}
proof Proof = Air { prover P; verifier V; public { public_data }; accept accepted;
  construction fiat_shamir("SUITE", coins); }
'''


def generated(height, final, blowup, queries, configuration='Poseidon2', extra=''):
    rounds = height.bit_length() - 1 - final
    return (GENERATED.replace('CONFIGURATION', configuration).replace('FINAL', str(final))
            .replace('ROUNDS', str(rounds)).replace('BLOWUP', str(blowup))
            .replace('QUERIES', str(queries)).replace('SUITE', SUITE)
            .replace('domain Trace', extra + 'domain Trace'))


@pytest.mark.parametrize('height,width,final,blowup,queries', [
    (16, 2, 0, 1, 20), (64, 4, 2, 2, 8), (256, 1, 1, 1, 100)])
def test_generated_air_parameters(toolchain, journal, directory, height, width, final, blowup,
                                  queries):
    bundle, public_data, trace = quadratic_air(height, width)
    asset = journal.write('bundle.json', bundle)
    package = Package.source(toolchain, journal, directory, generated(height, final, blowup, queries),
                             {'trace': asset})
    proof = package.honest({'public_data': public_data}, {'trace': trace})
    rounds = height.bit_length() - 1 - final
    messages = frames(proof.read_bytes())
    assert [tag(m) for m in messages] == expected_frames(rounds)
    assert len(messages[4 + rounds]) == 10 + 16 * 2 ** final
    # A changed public value is refused by the prover, whose quotient is then
    # not of the declared degree. The proof header binds the statement, so an
    # honest proof is refused for it before execution.
    changed = [str((int(public_data[0]) + 1) % P), *public_data[1:]]
    package.prove({'public_data': changed}, {'trace': trace}, refuses='artifact-stopped')
    package.verify({'public_data': changed}, proof, refuses='proof-header')


RECURRENCE_SOURCE = '''module example;
use stark::configurations::koala_bear_octic::{Base, Extension};
use stark::configurations::koala_bear_quartic::{Poseidon2};
use stark::single_table::{Statement, TableArgument};
use zkc::vector::{Vector};
use zkc::vector as v;
domain Recurrence = bundle(asset recurrence);
fn statement(configuration: Vector<Base>, x0: Base, y0: Base, final_acc: Base) -> Statement<Base> {
  let public_data = v::append(v::append(v::fill(x0, 1), y0), final_acc);
  return Statement<Base> { configuration, public_columns: v::empty<Base>(), public_data };
}
protocol RecurrenceProof roles(P,V)(trace: Vector<Base> @P, configuration: Vector<Base> @(P,V),
    x0: Base @(P,V), y0: Base @(P,V), final_acc: Base @(P,V), coins: Random<Extension> @V)
    -> (accepted: bool @V) {
  let statementP @P = statement(configuration, x0, y0, final_acc);
  let statementV @V = statement(configuration, x0, y0, final_acc);
  let accepted = TableArgument<Poseidon2, 0, Recurrence, LogFinal = 1, Rounds = 2, LogBlowup = 2,
    Queries = 12>(trace, statementP, statementV, coins);
  return (accepted = accepted);
}
proof Proof = RecurrenceProof { prover P; verifier V;
  public { configuration, x0, y0, final_acc }; accept accepted;
  construction fiat_shamir("merlin3.koala-bear.ext8-binomial3.rejection31le/0", coins); }
'''


def recurrence_inputs():
    data = json.loads((RECURRENCE / 'source-trace-honest.json').read_text())
    x0, y0, final = data['public_data']
    return ({'configuration': data['configuration'], 'x0': x0, 'y0': y0, 'final_acc': final},
            {'trace': data['trace']})


def test_statement_configuration_and_public_inputs(toolchain, journal, directory):
    package = Package.source(toolchain, journal, directory, RECURRENCE_SOURCE,
                             {'recurrence': RECURRENCE / 'bundle.json'})
    public, witness = recurrence_inputs()
    proof = package.honest(public, witness)
    configuration = [int(x) for x in public['configuration']]
    changes = {
        'x0': {'x0': '17'},
        'final': {'final_acc': '17'},
        'configuration': {'configuration': [str(configuration[0] + 1), *public['configuration'][1:]]},
    }
    for name, change in changes.items():
        changed = public | change
        package.verify(changed, proof, refuses='proof-header')
        package.prove(changed, witness, refuses='artifact-stopped')
    # A configuration of the wrong length is refused before any commitment.
    short = public | {'configuration': public['configuration'][:-1]}
    package.verify(short, proof, refuses='proof-header')
    package.prove(short, witness, refuses='artifact-stopped')
    trace = [int(x) for x in witness['trace']]
    trace[7] = (trace[7] + 1) % P
    package.prove(public, {'trace': [str(x) for x in trace]}, refuses='artifact-stopped')


def test_every_altered_message_is_refused(toolchain, journal, directory):
    package = Package.project(toolchain, journal, directory, PROJECT, 'Plonky3Proof')
    public, witness = fibonacci_inputs('Plonky3Proof')
    proof = package.honest(public, witness)
    original = proof.read_bytes()
    messages = frames(original)
    changed = 0
    for position, frame in enumerate(messages):
        value = altered(frame)
        if value is None:
            continue
        candidate = directory / f'altered-{position}.proof'
        candidate.write_bytes(replace_frame(original, position, value))
        rejected(package.verify(public, candidate, refuses=True))
        changed += 1
    assert changed >= len(messages) - 1
    for name, value, code in [('truncated', original[:-1], 'proof-truncated'),
                              ('trailing', original + b'\x00', 'proof-trailing')]:
        candidate = directory / f'{name}.proof'
        candidate.write_bytes(value)
        package.verify(public, candidate, refuses=code)


def dishonest(toolchain, journal, directory, name, overrides):
    source = (PROJECT / 'main.zkc').read_text().replace('proof CleanProof', 'proof Unused')
    source = source.replace('proof Plonky3Proof', 'proof Proof')
    return Package.source(toolchain, journal, directory, source,
                          {'clean': ROOT / 'compiler/adapters/clean/fixtures/fibonacci/bundle.json',
                           'plonky3': ROOT / 'compiler/adapters/plonky3/fixtures/fibonacci/bundle.json'},
                          overrides=overrides, name=name)


SHIFTED = '''
fn shifted(positions: Indices, size: index) -> Indices {
  let mut result = zkc::indices::empty();
  for query in 0..zkc::indices::length(positions) {
    let next = zkc::indices::remainder(zkc::indices::get(positions, query) + 1, size);
    result = zkc::indices::append(result, next);
  }
  return result;
}
'''


@pytest.mark.parametrize('variant', ['trace-rows', 'quotient-rows', 'fri-siblings'])
def test_wrong_openings_are_refused(toolchain, journal, directory, variant):
    """The prover opens its own commitments, but not where the verifier asked."""
    if variant == 'fri-siblings':
        path = edited(directory, LIBRARY / 'single_table/low_degree.zkc', [(
            'let proposed @P = sibling_values(opened.0, atP, nextP);',
            'let proposed @P = sibling_values(opened.0, pair_indices(atP, 1), nextP);')],
            'low_degree.zkc')
        overrides = {'stark::single_table::low_degree': path}
    else:
        target = {'trace-rows': 'K::open_base(trace_tree.1, positionsP, sizeP)',
                  'quotient-rows': 'K::open_extension(quotient_tree.1, positionsP, sizeP)'}[variant]
        path = edited(directory, LIBRARY / 'single_table/lib.zkc', [
            (target, target.replace('positionsP', 'shifted(positionsP, sizeP)')),
            ('fn deep_values<', SHIFTED + 'fn deep_values<')], 'argument.zkc')
        overrides = {'stark::single_table': path}
    package = dishonest(toolchain, journal, directory, variant, overrides)
    public, witness = fibonacci_inputs('Plonky3Proof')
    produced, proof = package.prove(public, witness)
    assert produced['status'] == 'produced'
    rejected(package.verify(public, proof, refuses=True))


COMPENSATED = '''
fn compensated<F: Field, Table: nat, B: Bundle>(honest: Vector<F>, assignments: Vector<F>,
    height: index, zeta: F, alpha: F) -> Vector<F> {
  let residuals = kernel<F,Table>("relation.table_point", assignments; B);
  let scopes = air::table::assertion_scopes<F,Table,B>(height);
  let combined = air::table::combine_scopes(residuals, scopes.0, scopes.1, height, zeta, alpha);
  let difference = combined - air::polynomial::recombine(honest, height, zeta);
  let mut result = empty<F>();
  for chunk in 0..length(honest) {
    result = append(result, if chunk == 0 { get(honest, 0) + difference } else { get(honest, chunk) });
  }
  return result;
}
'''


def test_dishonest_quotients_are_refused(toolchain, journal, directory):
    """A false trace whose quotient is truncated to the declared degree fails
    the out-of-domain identity. Choosing the quotient claim so that the
    identity holds instead makes the DEEP word fail the low-degree test, even
    when the prover also truncates its final polynomial."""
    public, witness = fibonacci_inputs('Plonky3Proof')
    trace = [int(x) for x in witness['trace']]
    trace[5] = (trace[5] + 1) % P
    false = {'trace': [str(x) for x in trace]}
    truncate = edited(directory, ROOT / 'libraries/relations/air/polynomial.zkc', [(
        '  require boolean::negate(less(capacity, actual));\n'
        '  let padded = concat(coefficients, fill<F>(0, capacity - actual));',
        '  let padded = if less(capacity, actual) { zkc::vector::slice(coefficients, 0, capacity) }\n'
        '    else { concat(coefficients, fill<F>(0, capacity - actual)) };')],
        'polynomial.zkc')
    package = dishonest(toolchain, journal, directory, 'truncated', {'air::polynomial': truncate})
    produced, proof = package.prove(public, false)
    assert produced['status'] == 'produced'
    identity = rejected(package.verify(public, proof, refuses=True))

    claims = edited(directory, LIBRARY / 'single_table/lib.zkc', [
        ('  let proposed_quotient @P = opening_claims(coset::column_batch(geometryP, factsP.chunks, chunks), zetaP);',
         '  let honest_quotient @P = opening_claims(coset::column_batch(geometryP, factsP.chunks, chunks), zetaP);\n'
         '  let proposed_quotient @P = compensated<K::Extension,Table,B>(honest_quotient, proposed,\n'
         '    heightP, zetaP, alphaP);'),
        ('fn deep_values<', COMPENSATED + 'fn deep_values<')], 'argument.zkc')
    final = edited(directory, LIBRARY / 'single_table/low_degree.zkc', [(
        '  require !less(count, length(coefficients));\n'
        '  return concat(coefficients, fill<F>(0, count - length(coefficients)));',
        '  return if less(count, length(coefficients)) { zkc::vector::slice(coefficients, 0, count) }\n'
        '    else { concat(coefficients, fill<F>(0, count - length(coefficients))) };')],
        'low_degree.zkc')
    package = dishonest(toolchain, journal, directory, 'compensated',
                        {'air::polynomial': truncate, 'stark::single_table': claims,
                         'stark::single_table::low_degree': final})
    produced, proof = package.prove(public, false)
    assert produced['status'] == 'produced'
    terminal = rejected(package.verify(public, proof, refuses=True))
    # The two provers are stopped by different verifier checks.
    assert identity['site'] != terminal['site']


CONFIGURATIONS = '''
use stark::configurations::contract::{Configuration, reversed_rows, reversed_pairs, reverse_positions,
  pair_positions};
use stark::configurations::koala_bear_quartic::{Quartic, KoalaBearRows, QuarticRows};
use zkc::indices::{Indices};
use zkc::oracle as oracle;
use zkc::oracle::{Root, Path, State};
module Reversed: Configuration {
  type Base: Field = stark::configurations::koala_bear_octic::Base;
  type Extension: Field = Quartic;
  type Challenge: Field = stark::configurations::koala_bear_octic::Extension;
  type BaseRows: Commitment = KoalaBearRows;
  type ExtensionRows: Commitment = QuarticRows;
  fn challenge(draw: stark::configurations::koala_bear_octic::Extension) -> Quartic { return Poseidon2::challenge(draw); }
  fn embed(values: Vector<stark::configurations::koala_bear_octic::Base>) -> Vector<Quartic> { return Poseidon2::embed(values); }
  fn lift(value: stark::configurations::koala_bear_octic::Base) -> Quartic { return Poseidon2::lift(value); }
  fn shift() -> stark::configurations::koala_bear_octic::Base { return 3; }
  fn commit_base(rows: Vector<stark::configurations::koala_bear_octic::Base>, width: index) -> (Root<KoalaBearRows>, State<KoalaBearRows>) {
    return oracle::commit<KoalaBearRows>(reversed_rows(rows, width), width);
  }
  fn open_base(state: State<KoalaBearRows>, positions: Indices, height: index)
      -> (Vector<stark::configurations::koala_bear_octic::Base>, Path<KoalaBearRows>) {
    return oracle::open_many<KoalaBearRows>(state, reverse_positions(positions, height));
  }
  fn check_base(root: Root<KoalaBearRows>, width: index, height: index, positions: Indices,
      rows: Vector<stark::configurations::koala_bear_octic::Base>, proof: Path<KoalaBearRows>) -> bool {
    return oracle::check_many<KoalaBearRows>(root, width, height,
      reverse_positions(positions, height), rows, proof);
  }
  fn commit_extension(rows: Vector<Quartic>, width: index) -> (Root<QuarticRows>, State<QuarticRows>) {
    return oracle::commit<QuarticRows>(reversed_rows(rows, width), width);
  }
  fn open_extension(state: State<QuarticRows>, positions: Indices, height: index)
      -> (Vector<Quartic>, Path<QuarticRows>) {
    return oracle::open_many<QuarticRows>(state, reverse_positions(positions, height));
  }
  fn check_extension(root: Root<QuarticRows>, width: index, height: index, positions: Indices,
      rows: Vector<Quartic>, proof: Path<QuarticRows>) -> bool {
    return oracle::check_many<QuarticRows>(root, width, height,
      reverse_positions(positions, height), rows, proof);
  }
  fn commit_pairs(word: Vector<Quartic>) -> (Root<QuarticRows>, State<QuarticRows>) {
    return oracle::commit<QuarticRows>(reversed_pairs(word), 2);
  }
  fn open_pairs(state: State<QuarticRows>, pairs: Indices, half: index)
      -> (Vector<Quartic>, Path<QuarticRows>) {
    return oracle::open_many<QuarticRows>(state, reverse_positions(pairs, half));
  }
  fn check_pairs(root: Root<QuarticRows>, half: index, pairs: Indices, rows: Vector<Quartic>,
      proof: Path<QuarticRows>) -> bool {
    return oracle::check_many<QuarticRows>(root, 2, half, reverse_positions(pairs, half), rows, proof);
  }
}
module Separate: Configuration {
  type Base: Field = stark::configurations::koala_bear_octic::Base;
  type Extension: Field = Quartic;
  type Challenge: Field = stark::configurations::koala_bear_octic::Extension;
  type BaseRows: Commitment = KoalaBearRows;
  type ExtensionRows: Commitment = QuarticRows;
  fn challenge(draw: stark::configurations::koala_bear_octic::Extension) -> Quartic { return Poseidon2::challenge(draw); }
  fn embed(values: Vector<stark::configurations::koala_bear_octic::Base>) -> Vector<Quartic> { return Poseidon2::embed(values); }
  fn lift(value: stark::configurations::koala_bear_octic::Base) -> Quartic { return Poseidon2::lift(value); }
  fn shift() -> stark::configurations::koala_bear_octic::Base { return 3; }
  fn commit_base(rows: Vector<stark::configurations::koala_bear_octic::Base>, width: index) -> (Root<KoalaBearRows>, State<KoalaBearRows>) {
    return Poseidon2::commit_base(rows, width);
  }
  fn open_base(state: State<KoalaBearRows>, positions: Indices, height: index)
      -> (Vector<stark::configurations::koala_bear_octic::Base>, Path<KoalaBearRows>) {
    return Poseidon2::open_base(state, positions, height);
  }
  fn check_base(root: Root<KoalaBearRows>, width: index, height: index, positions: Indices,
      rows: Vector<stark::configurations::koala_bear_octic::Base>, proof: Path<KoalaBearRows>) -> bool {
    return Poseidon2::check_base(root, width, height, positions, rows, proof);
  }
  fn commit_extension(rows: Vector<Quartic>, width: index) -> (Root<QuarticRows>, State<QuarticRows>) {
    return Poseidon2::commit_extension(rows, width);
  }
  fn open_extension(state: State<QuarticRows>, positions: Indices, height: index)
      -> (Vector<Quartic>, Path<QuarticRows>) {
    return Poseidon2::open_extension(state, positions, height);
  }
  fn check_extension(root: Root<QuarticRows>, width: index, height: index, positions: Indices,
      rows: Vector<Quartic>, proof: Path<QuarticRows>) -> bool {
    return Poseidon2::check_extension(root, width, height, positions, rows, proof);
  }
  fn commit_pairs(word: Vector<Quartic>) -> (Root<QuarticRows>, State<QuarticRows>) {
    return oracle::commit<QuarticRows>(word, 1);
  }
  fn open_pairs(state: State<QuarticRows>, pairs: Indices, half: index)
      -> (Vector<Quartic>, Path<QuarticRows>) {
    return oracle::open_many<QuarticRows>(state, pair_positions(pairs, half));
  }
  fn check_pairs(root: Root<QuarticRows>, half: index, pairs: Indices, rows: Vector<Quartic>,
      proof: Path<QuarticRows>) -> bool {
    return oracle::check_many<QuarticRows>(root, 1, 2 * half, pair_positions(pairs, half), rows, proof);
  }
}
'''


def test_layout_and_leaf_grouping_are_configurations(toolchain, journal, directory):
    """The same protocol with two other configurations: rows and FRI pairs in
    bit-reversed order, and natural rows with one FRI value per leaf. All three
    verify with the same message sequence; the layout changes the trace root,
    and separate leaves need two authentication paths per pair."""
    height, final, blowup, queries = 32, 1, 2, 16
    bundle, public_data, trace = quadratic_air(height, 3)
    asset = journal.write('bundle.json', bundle)
    proofs = {}
    for configuration in ['Poseidon2', 'Reversed', 'Separate']:
        source = generated(height, final, blowup, queries, configuration, CONFIGURATIONS)
        package = Package.source(toolchain, journal, directory, source, {'trace': asset},
                                 name=configuration)
        proofs[configuration] = frames(package.honest({'public_data': public_data},
                                                      {'trace': trace}).read_bytes())
    natural, reversed_, separate = proofs['Poseidon2'], proofs['Reversed'], proofs['Separate']
    rounds = height.bit_length() - 1 - final
    assert [tag(m) for m in natural] == [tag(m) for m in reversed_] == [tag(m) for m in separate]
    # The trace root is committed before any challenge. The deployment differs
    # between configurations, so later challenges and roots differ anyway.
    assert natural[0] != reversed_[0] and natural[0] == separate[0]
    # Separate leaves k and k + half lie in the two equal halves of a tree of
    # 2*half leaves, so each layer proof holds the same boundary twice: an even
    # digest count, below a root whose both children are covered.
    layer_proofs = range(len(natural) - 2 * rounds + 1, len(natural), 2)
    assert all(int.from_bytes(separate[i][6:10], 'little') % 2 == 0 for i in layer_proofs)
    journal.write('sizes.json', {name: sum(map(len, value)) for name, value in proofs.items()})


DERIVATION = '''module sample;
use stark::configurations::koala_bear_octic::{Extension};
use stark::configurations::koala_bear_quartic::{Poseidon2, Quartic};
protocol Run roles(P)(draw: Extension @P) -> (challenge: Quartic @P) {
  let challenge @P = Poseidon2::challenge(draw);
  return (challenge = challenge);
}
run Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''


def test_quartic_challenges_are_octic_prefixes(toolchain, journal, directory):
    from entry import Entry
    entry = Entry(toolchain, journal, directory, DERIVATION, library_modules('arguments/stark/configurations/contract', 'arguments/stark/configurations/koala_bear_octic', 'arguments/stark/configurations/koala_bear_quartic', 'arguments/stark/sampling', 'arguments/stark/single_table', 'arguments/stark/single_table/koala_bear_octic', 'arguments/stark/whole_bundle'))
    for draw in ([1, 2, 3, 4, 5, 6, 7, 8], [P - 1] * 8, [0] * 7 + [9]):
        result = entry.run(f'draw-{draw[0]}-{draw[-1]}', {'draw': [str(x) for x in draw]})
        assert result['challenge'] == [str(x) for x in draw[:4]]


def test_comparison_with_existing_profile(toolchain, journal, directory):
    """The same Plonky3-exported Fibonacci AIR and the same small parameters
    (eight rows, 32 evaluation points, eight queries) through the existing
    KoalaBear profile and through this library. Both accept their honest
    proofs; sizes and frame counts are recorded beside the evidence."""
    public, witness = fibonacci_inputs('Plonky3Proof')
    for entry in ('CleanProof', 'Plonky3Proof'):
        for group in ('public', 'witness'):
            name = f'inputs/example.{entry}/{group}.json'
            assert (PROJECT / name).read_text() == (EXISTING / name).read_text()
    record = {}
    for project in (EXISTING, PROJECT):
        package = Package.project(toolchain, journal, directory, project, 'Plonky3Proof')
        proof = package.honest(public, witness)
        record[project.name] = {'bytes': proof.stat().st_size,
                                'messages': len(frames(proof.read_bytes()))}
    journal.write('comparison.json', record)
    assert record['stark']['bytes'] < record['fibonacci']['bytes']
