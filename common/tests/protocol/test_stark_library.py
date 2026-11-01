"""The parameterized single-table STARK library at its KoalaBear configuration.

`stark::single_table::ScalarTableArgument` is generic over a `stark::configurations::contract::
Configuration`; these tests run it with `stark::configurations::koala_bear_quartic::Poseidon2`
(KoalaBear trace, quartic extension, Poseidon2 Merkle trees with pruned
multi-openings for natural outer rows,
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
from message_frames import children, replace_child, tag, with_children
from oracle_deployment import table_realization
from source_modules import library_modules

ROOT = Path(__file__).resolve().parents[3]
PROJECT = ROOT / 'examples/projects/stark'
EXISTING = ROOT / 'examples/projects/fibonacci'
LIBRARY = ROOT / 'libraries/arguments/stark'
FRI = ROOT / 'libraries/protocols/polynomial/fri/lib.zkc'
RECURRENCE = ROOT / 'compiler/adapters/plonky3/fixtures/recurrence'
SUITE = 'merlin3.koala-bear.ext8-binomial3.rejection31le/0'
P = 2130706433
QUARTIC_SCHEME = 'rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0'
OCTIC_SCHEME = 'rows.merkle-keccak256.koala-bear.ext8-binomial3/0'
QUARTIC_REALIZATION = table_realization(QUARTIC_SCHEME)
OCTIC_REALIZATION = table_realization(OCTIC_SCHEME)

# ZKCV value-frame tags (docs/spec/formats/messages.md).
BASE_VECTOR, QUARTIC_VECTOR, ROOT_FRAME, PROOF_FRAME = 20, 22, 71, 72
TABLE_GUARDS = [(name, role, 0) for name, role in (
    ('admissible_v', 'role00000001'), ('admissible_p', 'role00000000'),
    ('trace_length', 'role00000000'), ('outside_v', 'role00000001'),
    ('outside_p', 'role00000000'), ('claim_count', 'role00000001'),
    ('identity', 'role00000001'),
    ('trace_opening', 'role00000001'), ('quotient_opening', 'role00000001'))]


def frames(proof):
    assert proof[:8] == b'ZKCPRF00' and len(proof) >= 40
    offset, result = 40, []
    while offset < len(proof):
        assert offset + 8 <= len(proof)
        count = int.from_bytes(proof[offset:offset + 8], 'little')
        assert count >= 6 and offset + 8 + count <= len(proof)
        result.append(proof[offset + 8:offset + 8 + count])
        tag(result[-1])
        offset += count + 8
    assert offset == len(proof)
    return result


def replace_frame(proof, position, value):
    messages = frames(proof)
    messages[position] = value
    return proof[:40] + b''.join(len(m).to_bytes(8, 'little') + m for m in messages)


def frame_inventory(frame):
    """Describe observed canonical framing without inferring a query layout."""
    kind = tag(frame)
    result = {'tag': kind, 'bytes': len(frame)}
    if kind in (65, 69):
        result['alternative' if kind == 65 else 'count'] = int.from_bytes(frame[6:10], 'little')
        result['children'] = [frame_inventory(child) for child in children(frame)]
    elif kind in (BASE_VECTOR, QUARTIC_VECTOR, 27, 34, 36, 68, PROOF_FRAME):
        result['count'] = int.from_bytes(frame[6:10], 'little')
    return result


def wire_profile(proof):
    messages = frames(proof)
    payload_bytes = sum(map(len, messages))
    assert len(proof) == 40 + 8 * len(messages) + payload_bytes
    return {'bytes': len(proof), 'messages': len(messages), 'payload_bytes': payload_bytes,
            'header_bytes': 40, 'length_bytes': 8 * len(messages),
            'frames': [frame_inventory(frame) for frame in messages]}


def mutable_leaves(frame, path=()):
    """Visit every scalar-bearing leaf without assuming aggregate offsets."""
    if tag(frame) in (65, 69):
        for index, child in enumerate(children(frame)):
            yield from mutable_leaves(child, (*path, index))
    else:
        yield path, frame


def altered(frame):
    """Increment one canonical field word; empty pruned proofs have no word."""
    start = {BASE_VECTOR: 10, QUARTIC_VECTOR: 10, ROOT_FRAME: 6, PROOF_FRAME: 10}[tag(frame)]
    if len(frame) < start + 4:
        assert tag(frame) == PROOF_FRAME and vector_count(frame, PROOF_FRAME, 32) == 0
        return None
    word = int.from_bytes(frame[start:start + 4], 'little')
    assert word < P
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
    def __init__(self, toolchain, journal, directory, command, name, realization=None):
        self.tools, self.journal, self.directory, self.name = toolchain, journal, directory, name
        self.path = directory / f'{name}.zkpkg'
        report = journal.json([toolchain.runtime, '--json', 'compile',
                               f'--compiler={toolchain.compiler}', *command,
                               *([realization] if realization is not None else []),
                               f'--output={self.path}'])
        self.pin = report['package_sha256']
        self.runs = 0

    @classmethod
    def project(cls, toolchain, journal, directory, project, entry, flags=(), *,
                realization=QUARTIC_REALIZATION):
        return cls(toolchain, journal, directory,
                   [f'--project={project}/zkc.toml', f'example::{entry}', *flags],
                   f'{project.name}-{entry}', realization)

    @classmethod
    def source(cls, toolchain, journal, directory, source, assets, *, overrides=None,
               flags=(), name='variant', modules=(), realization=None):
        path = directory / f'{name}.zkc'
        path.write_text(source)
        return cls(toolchain, journal, directory,
                   [f'--module=example={path}', *library_modules('arguments/stark/configurations/contract', 'arguments/stark/configurations/koala_bear_octic', 'arguments/stark/configurations/koala_bear_quartic', 'arguments/stark/sampling', 'arguments/stark/single_table', 'arguments/stark/single_table/koala_bear_octic', 'arguments/stark/whole_bundle', *modules, overrides=overrides),
                    *[f'--asset={k}=relation-bundle-json={v}' for k, v in assets.items()],
                    'example::Proof', *flags], name, realization)

    def request(self, public, witness=None):
        self.runs += 1
        return input_files(self.journal, f'{self.name}-{self.runs}.json', public=public,
                           witness=witness or {})

    def prove(self, public, witness, *, refuses=None, capacity=None, threads=1):
        proof = self.directory / f'{self.name}-{self.runs + 1}.proof'
        extra = [f'--threads={threads}', *([f'--capacity={capacity}'] if capacity else [])]
        report = self.journal.json([self.tools.runtime, '--json', 'prove', f'--package={self.path}',
                                    f'--sha256={self.pin}', *self.request(public, witness),
                                    f'--output={proof}', *extra], refuses=refuses)
        return report, proof

    def verify(self, public, proof, *, refuses=None, capacity=None, threads=1):
        extra = [f'--threads={threads}', *([f'--capacity={capacity}'] if capacity else [])]
        return self.journal.json([self.tools.runtime, '--json', 'verify', f'--package={self.path}',
                                  f'--sha256={self.pin}', *self.request(public),
                                  f'--proof={proof}', *extra], refuses=refuses)

    def honest(self, public, witness, capacity=None):
        produced, proof = self.prove(public, witness, capacity=capacity)
        assert produced['status'] == 'produced'
        assert self.verify(public, proof, capacity=capacity)['status'] == 'accepted'
        self.journal.write(f'{self.name}-{self.runs}-wire.json', wire_profile(proof.read_bytes()))
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
    assert stop['role'] == 'role00000001', stop
    assert stop['kind'] == 'Explicit("reject")', stop
    return stop


def source_guards(package):
    """Resolve the caller and shared FRI checks from this exact package."""
    from test_fri import CHECK_GUARDS, COMMIT_GUARDS, emitted_guard_sites
    emitted = json.loads(package.path.read_text())['original']
    return (emitted_guard_sites(emitted, {
        'table.': TABLE_GUARDS[:-2], 'commit.': COMMIT_GUARDS, 'check.': CHECK_GUARDS}) |
        emitted_guard_sites(emitted, {'table.': TABLE_GUARDS[-2:]}))


def refused_at(report, package, name, iterations):
    from test_fri import stop_guard
    stop = rejected(report)
    assert stop_guard(stop, source_guards(package)) == (name, iterations)
    return stop


def vector_count(frame, kind, width):
    assert tag(frame) == kind and len(frame) >= 10
    count = int.from_bytes(frame[6:10], 'little')
    assert len(frame) == 10 + width * count
    return count


def assert_quartic_frames(messages, *, log_size, final, rounds, queries, width, chunks, claims):
    """Observed Poseidon2 individual-leaf deployment, with batched outer rows.

    Each selected actual layer has one response; each virtual fold has both
    children, including the repeated initial value. This physical inventory
    belongs to this explicit deployment, not to the logical FRI interface.
    """
    prefix = [ROOT_FRAME, ROOT_FRAME, QUARTIC_VECTOR, QUARTIC_VECTOR,
              *[ROOT_FRAME] * rounds, QUARTIC_VECTOR,
              BASE_VECTOR, PROOF_FRAME, QUARTIC_VECTOR, PROOF_FRAME]
    assert [tag(frame) for frame in messages] == prefix + [69] * (2 * rounds * queries)
    assert all(len(messages[i]) == 38 for i in [0, 1, *range(4, 4 + rounds)])
    assert vector_count(messages[2], QUARTIC_VECTOR, 16) == claims
    assert vector_count(messages[3], QUARTIC_VECTOR, 16) == chunks
    assert vector_count(messages[4 + rounds], QUARTIC_VECTOR, 16) == 1 << final
    outer = 5 + rounds
    assert vector_count(messages[outer], BASE_VECTOR, 4) == width * queries
    assert vector_count(messages[outer + 2], QUARTIC_VECTOR, 16) == chunks * queries
    sibling_counts = [vector_count(messages[index], PROOF_FRAME, 32)
                      for index in (outer + 1, outer + 3)]
    # Both trees open the same positions with the same geometry. The number
    # of shared siblings depends on the sampled positions, not row contents.
    assert sibling_counts[0] == sibling_counts[1]
    assert 0 <= sibling_counts[0] <= log_size * queries
    packets = len(prefix)
    for query in range(queries):
        for layer in range(rounds):
            for fold in (False, True):
                packet = messages[packets + 2 * (query * rounds + layer) + fold]
                answers = children(packet)
                assert len(answers) == (2 if fold else 1)
                for answer in answers:
                    assert tag(answer) == 65 and answer[6:10] == bytes(4)
                    row, path = children(answer)
                    assert vector_count(row, QUARTIC_VECTOR, 16) == 1
                    assert vector_count(path, PROOF_FRAME, 32) == log_size - layer


@pytest.mark.parametrize('flags', [[], ['--no-simplify'], ['--no-finite-bulk'], ['--release-storage']])
@pytest.mark.parametrize('entry', ['Plonky3Proof', 'CleanProof'])
def test_example_entries_prove_and_verify(toolchain, journal, directory, entry, flags):
    package = Package.project(toolchain, journal, directory, PROJECT, entry, flags)
    public, witness = fibonacci_inputs(entry)
    proof = package.honest(public, witness)
    messages = frames(proof.read_bytes())
    assert_quartic_frames(messages, log_size=5, final=0, rounds=3, queries=8,
                          width=2, chunks=1, claims=8)


def quadratic_air(height, width, *, field='koala-bear', modulus=P):
    """The benchmark recurrence x' = x^2 + c + 1 per column, with first and
    last rows bound to public values, as a one-table Bundle."""
    import importlib.util
    spec = importlib.util.spec_from_file_location('ring_arena', ROOT / 'compiler/adapters/ring_arena.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    arena = module.Arena()
    outputs, assertions = [], []
    for col in range(width):
        current = arena.input(field, ['read', 0, '0', col])
        following = arena.input(field, ['read', 0, '1', col])
        initial = arena.input(field, ['public', col])
        final = arena.input(field, ['public', width + col])
        for value, selector in ((current - initial, ['first']), (current - final, ['last']),
                                (following - current * current - (col + 1), ['interior', 0, 1])):
            assertions.append([len(outputs), selector])
            outputs.append(value)
    ring, bindings = arena.finish(outputs)
    bundle = ['zkc.relation-bundle/0', [[f'public-{i}', field] for i in range(2 * width)], [],
              [['trace', 'required', ['fixed', height], 'cyclic',
                [['trace', 'witness', field, width]], ring, bindings, assertions, []]]]
    current = [(7919 * (c + 3)) % modulus for c in range(width)]
    initial, trace = current, []
    for _ in range(height):
        trace.extend(current)
        final = current
        current = [(x * x + i + 1) % modulus for i, x in enumerate(current)]
    return bundle, [str(v) for v in initial + final], [str(v) for v in trace]


GENERATED = '''module example;
use stark::configurations::koala_bear_octic::{Base, Extension};
use stark::configurations::koala_bear_quartic::{Poseidon2};
use stark::single_table::{Statement, ScalarTableArgument};
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
  let accepted = ScalarTableArgument<CONFIGURATION, 0, Trace, LogFinal = FINAL, Rounds = ROUNDS,
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


@pytest.mark.parametrize(('sampling', 'difficulty', 'height', 'final', 'blowup', 'queries'), [
    ('Scalar', None, 8, 0, 2, 4), ('Block', None, 8, 0, 2, 4),
    ('Block', 0, 8, 0, 2, 4), ('Block', 4, 8, 0, 2, 4),
    ('Block', 4, 256, 1, 1, 100),
])
def test_direct_quartic_keccak_sampling(toolchain, journal, directory, sampling, difficulty,
                                      height, final, blowup, queries):
    bundle, public, trace = quadratic_air(height, 1)
    asset = journal.write(f'{sampling}-air.json', bundle)
    source = generated(height, final, blowup, queries, configuration='Keccak256')
    source = (source.replace(
        'use stark::configurations::koala_bear_octic::{Base, Extension};',
        'use stark::configurations::koala_bear_quartic::{Base, Quartic};')
        .replace('::{Poseidon2}', '::{Keccak256}')
        .replace('Random<Extension>', 'Random<Quartic>')
        .replace('ScalarTableArgument', sampling + 'TableArgument')
        .replace(SUITE, 'hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0'))
    if difficulty is not None:
        source = source.replace('  let accepted = BlockTableArgument',
                                '  #[site(argument)] let accepted = BlockTableArgument')
        source = source.replace('coins); }',
                                f'coins); gate argument.fri_queries.positions bits {difficulty}; }}')
    package = Package.source(toolchain, journal, directory, source, {'trace': asset},
        name=f'quartic-keccak-{sampling.lower()}',
        realization=table_realization('rows.merkle-keccak256.koala-bear.ext4-binomial3/0'))
    published = json.loads(package.path.read_text())
    gates = json.loads(published['interface'])['job']['gates']
    assert gates == ([] if difficulty is None else [
        {'path': ['argument', 'fri_queries', 'positions'], 'bits': difficulty}])
    public_inputs = {'public_data': public}
    produced, proof = package.prove(public_inputs, {'trace': trace})
    assert produced['status'] == 'produced'
    accepted = package.verify(public_inputs, proof)
    assert accepted['status'] == 'accepted'
    if difficulty == 0:
        messages = frames(proof.read_bytes())
        witnesses = [i for i, value in enumerate(messages) if tag(value) == 31]
        assert len(witnesses) == 1
        slot = witnesses[0]
        assert messages[slot][6:] == bytes(8)
        changed_witness = messages[slot][:6] + (1).to_bytes(8, 'little')
        candidate = directory / 'noncanonical-zero-gate.proof'
        candidate.write_bytes(replace_frame(proof.read_bytes(), slot, changed_witness))
        assert package.verify(public_inputs, candidate, refuses=True)['status'] == 'refused'
    changed = list(public)
    changed[0] = str((int(changed[0]) + 1) % P)
    refused = package.verify({'public_data': changed}, proof, refuses=True)
    assert refused['status'] == 'refused'


def unread_column_case(journal):
    bundle, public, trace = quadratic_air(8, 1)
    # The arena still reads only column zero. Column one nevertheless belongs
    # to the committed witness layout and the advertised degree claim.
    bundle[3][0][4][0][3] = 2
    asset = journal.write('unread-column.json', bundle)
    witness = [entry for value in trace for entry in (value, '7')]
    return asset, {'public_data': public}, {'trace': witness}


def test_unread_witness_column_claims(toolchain, journal, directory):
    asset, public, witness = unread_column_case(journal)
    package = Package.source(toolchain, journal, directory, generated(8, 0, 1, 8),
                             {'trace': asset}, realization=QUARTIC_REALIZATION)
    proof = package.honest(public, witness)
    messages = frames(proof.read_bytes())
    assert_quartic_frames(messages, log_size=4, final=0, rounds=3, queries=8,
                          width=2, chunks=1, claims=5)
    claims = messages[2]
    # Omitting the appended claim must fail the exact inventory check before
    # any later challenge or opening can supply a different interpretation.
    missing = claims[:6] + (4).to_bytes(4, 'little') + claims[10:-16]
    candidate = directory / 'missing-unread-claim.proof'
    candidate.write_bytes(replace_frame(proof.read_bytes(), 2, missing))
    refused_at(package.verify(public, candidate, refuses=True), package,
               'table.claim_count', [])


def test_degree_boundary_on_unread_column(toolchain, journal, directory):
    """The old <n quotient subcheck accepts a degree-n committed column.

    This is a degree-claim control, not a false-AIR statement: the AIR does not
    constrain the extra column. The corrected verifier rejects after the
    dishonest prover truncates its otherwise inadmissible terminal polynomial.
    """
    asset, public, witness = unread_column_case(journal)
    helper = '''
fn high_column<F: Field>(values: Vector<F>, shift: F, size: index, height: index)
    -> Vector<F> {
  let mut result = zkc::vector::slice(values, 0, size);
  for row in 0..size {
    result = append(result, zkc::scalar::power(coset::point(shift, size, row), height));
  }
  return result;
}
'''
    substitutions = [
        ('fn deep_values<', helper + 'fn deep_values<'),
        ('  let trace_lde @P = extend_columns(trace_columns, factsP.witness, heightP, shiftP, sizeP);',
         '  let honest_lde @P = extend_columns(trace_columns, factsP.witness, heightP, shiftP, sizeP);\n'
         '  let trace_lde @P = high_column(honest_lde, shiftP, sizeP, heightP);'),
        ('  let proposed @P = input_values(slotsP, K::embed(trace_columns), K::embed(configP),\n'
         '    K::embed(publicP), dataP, heightP, zetaP);',
         '  let honest_claims @P = input_values(slotsP, K::embed(trace_columns), K::embed(configP),\n'
         '    K::embed(publicP), dataP, heightP, zetaP);\n'
         '  let proposed @P = append(zkc::vector::slice(honest_claims, 0, length(honest_claims)-1),\n'
         '    zkc::scalar::power(zetaP, heightP));'),
    ]
    unadjusted = edited(directory, LIBRARY / 'single_table/lib.zkc', [*substitutions,
        ('let adjustmentV @V = K::challenge(adjustmentDraw);', 'let adjustmentV: K::Extension @V = 0;'),
        ('let adjustmentP @P = K::challenge(adjustmentSent);', 'let adjustmentP: K::Extension @P = 0;')],
        'unadjusted-library.zkc')
    package = Package.source(toolchain, journal, directory, generated(8, 0, 1, 16),
                             {'trace': asset}, overrides={'stark::single_table': unadjusted},
                             name='unadjusted', realization=QUARTIC_REALIZATION)
    package.honest(public, witness)

    adjusted = edited(directory, LIBRARY / 'single_table/lib.zkc', substitutions,
                      'adjusted-library.zkc')
    truncated = edited(directory, FRI, [(
        '  require !less(count, length(coefficients));\n'
        '  return concat(coefficients, fill<F>(0, count - length(coefficients)));',
        '  return if less(count, length(coefficients)) { zkc::vector::slice(coefficients, 0, count) }\n'
        '    else { concat(coefficients, fill<F>(0, count - length(coefficients))) };')],
        'truncated.zkc')
    package = Package.source(toolchain, journal, directory, generated(8, 0, 1, 16),
                             {'trace': asset}, overrides={'stark::single_table': adjusted,
                                                         'fri': truncated},
                             name='adjusted', realization=QUARTIC_REALIZATION)
    produced, proof = package.prove(public, witness)
    assert produced['status'] == 'produced'
    refused_at(package.verify(public, proof, refuses=True), package, 'check.terminal', ['0'])


@pytest.mark.parametrize('height,width,final,blowup,queries', [
    (16, 2, 0, 1, 20), (64, 4, 2, 2, 8), (256, 1, 1, 1, 100)])
def test_generated_air_parameters(toolchain, journal, directory, height, width, final, blowup,
                                  queries):
    bundle, public_data, trace = quadratic_air(height, width)
    asset = journal.write('bundle.json', bundle)
    package = Package.source(toolchain, journal, directory, generated(height, final, blowup, queries),
                             {'trace': asset}, realization=QUARTIC_REALIZATION)
    proof = package.honest({'public_data': public_data}, {'trace': trace})
    rounds = height.bit_length() - 1 - final
    messages = frames(proof.read_bytes())
    assert_quartic_frames(messages, log_size=height.bit_length() - 1 + blowup,
                          final=final, rounds=rounds, queries=queries, width=width,
                          chunks=1, claims=4 * width)
    # A changed public value is refused by the prover, whose quotient is then
    # not of the declared degree. The proof header binds the statement, so an
    # honest proof is refused for it before execution.
    changed = [str((int(public_data[0]) + 1) % P), *public_data[1:]]
    package.prove({'public_data': changed}, {'trace': trace}, refuses='artifact-stopped')
    package.verify({'public_data': changed}, proof, refuses='proof-header')


RECURRENCE_SOURCE = '''module example;
use stark::configurations::koala_bear_octic::{Base, Extension};
use stark::configurations::koala_bear_quartic::{Poseidon2};
use stark::single_table::{Statement, ScalarTableArgument};
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
  let accepted = ScalarTableArgument<Poseidon2, 0, Recurrence, LogFinal = 1, Rounds = 2, LogBlowup = 2,
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
                             {'recurrence': RECURRENCE / 'bundle.json'},
                             realization=QUARTIC_REALIZATION)
    public, witness = recurrence_inputs()
    proof = package.honest(public, witness)
    assert_quartic_frames(frames(proof.read_bytes()), log_size=5, final=1, rounds=2,
                          queries=12, width=4, chunks=2, claims=11)
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
    from test_fri import authentication_rejection
    package = Package.project(toolchain, journal, directory, PROJECT, 'Plonky3Proof')
    public, witness = fibonacci_inputs('Plonky3Proof')
    proof = package.honest(public, witness)
    original = proof.read_bytes()
    messages = frames(original)
    assert_quartic_frames(messages, log_size=5, final=0, rounds=3, queries=8,
                          width=2, chunks=1, claims=8)
    descriptor = json.loads(json.loads(package.path.read_text())['artifact'])[2]
    evidence, empty = [], []

    def reject(name, position, value, reason=True):
        candidate = directory / f'{name}.proof'
        candidate.write_bytes(replace_frame(original, position, value))
        report = package.verify(public, candidate, refuses=reason)
        evidence.append({'name': name, 'message': position, 'code': report['code'],
                         'stop': report.get('execution', {}).get('stop')})
        journal.write('mutation-evidence.json', evidence)
        return report

    # The prefix determines later challenges/positions. Outer row/path failures
    # remain source checks; dynamic FRI responses fail generated authentication.
    for position, frame in enumerate(messages):
        for path, leaf in mutable_leaves(frame):
            value = altered(leaf)
            if value is None:
                empty.append((position, path))
                continue
            report = reject(f'altered-{position}-' + '-'.join(map(str, path)), position,
                            replace_child(frame, path, value))
            if position < 12:
                name = ('table.identity' if position < 4 else
                        'table.quotient_opening' if position in (10, 11) else
                        'table.trace_opening')
                refused_at(report, package, name, [])
            else:
                query, offset = divmod(position - 12, 6)
                layer, fold = divmod(offset, 2)
                assert authentication_rejection(report, descriptor) == (query, layer, bool(fold), path[0])
    # This concrete proof has no empty pruned component. Every row/path of
    # every packet was changed independently, including both children at q=7.
    assert empty == []
    assert len(evidence) == 12 + 8 * 3 * 3 * 2

    index = 12 + 2 * (7 * 3 + 2) + 1
    low, high = children(messages[index])
    low_row, low_path = children(low)
    high_row, high_path = children(high)
    assert low_row != high_row and low_path != high_path
    for name, answers, item in [('swapped', [high, low], 0),
                                ('duplicated', [low, low], 1)]:
        report = reject(name, index, with_children(messages[index], answers))
        assert authentication_rejection(report, descriptor) == (7, 2, True, item)
    for name, leaf in [('row', high_row), ('path', high_path)]:
        report = reject(f'substituted-{name}', index,
                        replace_child(messages[index], [0, 0 if name == 'row' else 1], leaf))
        assert authentication_rejection(report, descriptor) == (7, 2, True, 0)
    for name, answers in [('missing-sibling', [low]), ('missing-both', [])]:
        report = reject(name, index, with_children(messages[index], answers))
        assert authentication_rejection(report, descriptor, element=False) == (7, 2, True)
    terminal = messages[7]
    assert vector_count(terminal, QUARTIC_VECTOR, 16) == 1
    for name, value in [('short-terminal', terminal[:6] + bytes(4)),
                        ('long-terminal', terminal[:6] + (2).to_bytes(4, 'little') +
                         terminal[10:] + bytes(16))]:
        refused_at(reject(name, 7, value, 'artifact-stopped'), package,
                   'commit.terminal_length', [])
    for name, value, code in [('truncated', original[:-1], 'proof-truncated'),
                              ('trailing', original + b'\x00', 'proof-trailing')]:
        candidate = directory / f'{name}.proof'
        candidate.write_bytes(value)
        report = package.verify(public, candidate, refuses=code)
        evidence.append({'name': name, 'code': report['code']})
    journal.write('mutation-evidence.json', evidence)


def dishonest(toolchain, journal, directory, name, overrides):
    source = (PROJECT / 'main.zkc').read_text().replace('proof CleanProof', 'proof Unused')
    source = source.replace('proof Plonky3Proof', 'proof Proof')
    return Package.source(toolchain, journal, directory, source,
                          {'clean': ROOT / 'compiler/adapters/clean/fixtures/fibonacci/bundle.json',
                           'plonky3': ROOT / 'compiler/adapters/plonky3/fixtures/fibonacci/bundle.json'},
                          overrides=overrides, name=name, realization=QUARTIC_REALIZATION)


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


@pytest.mark.parametrize('variant', ['trace-rows', 'quotient-rows', 'fri-first-value'])
def test_wrong_openings_are_refused(toolchain, journal, directory, variant):
    """Reject wrong outer positions and a committed first value that disagrees with DEEP."""
    if variant == 'fri-first-value':
        # Authenticate a consistently changed initial word. Its selected value
        # must disagree with the outer DEEP value before any chain is checked.
        path = edited(directory, FRI, [(
            'let values @P = coset::values(current);',
            'let values @P = changed_initial(coset::values(current), round);'), (
            'fn padded<F: Field>',
            'fn changed_initial<F: Field>(values: Vector<F>, round: index) -> Vector<F> {\n'
            '  return if round == 0 { zkc::vector::add(values, fill<F>(1, length(values))) }\n'
            '    else { values };\n'
            '}\n\nfn padded<F: Field>')], 'fri.zkc')
        overrides = {'fri': path}
    else:
        target = {'trace-rows': 'K::open_base(prover.trace, positionsP, sizeP)',
                  'quotient-rows': 'K::open_extension(prover.quotient, positionsP, sizeP)'}[variant]
        path = edited(directory, LIBRARY / 'single_table/lib.zkc', [
            (target, target.replace('positionsP', 'shifted(positionsP, sizeP)')),
            ('fn deep_values<', SHIFTED + 'fn deep_values<')], 'argument.zkc')
        overrides = {'stark::single_table': path}
    package = dishonest(toolchain, journal, directory, variant, overrides)
    public, witness = fibonacci_inputs('Plonky3Proof')
    produced, proof = package.prove(public, witness)
    assert produced['status'] == 'produced'
    report = package.verify(public, proof, refuses=True)
    name, iterations = {
        'trace-rows': ('table.trace_opening', []),
        'quotient-rows': ('table.quotient_opening', []),
        'fri-first-value': ('check.association', ['0']),
    }[variant]
    refused_at(report, package, name, iterations)


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
    identity = refused_at(package.verify(public, proof, refuses=True), package,
                          'table.identity', [])

    claims = edited(directory, LIBRARY / 'single_table/lib.zkc', [
        ('  let proposed_quotient @P = opening_claims(coset::column_batch(geometryP, factsP.chunks, chunks), zetaP);',
         '  let honest_quotient @P = opening_claims(coset::column_batch(geometryP, factsP.chunks, chunks), zetaP);\n'
         '  let proposed_quotient @P = compensated<K::Extension,Table,B>(honest_quotient, proposed,\n'
         '    heightP, zetaP, alphaP);'),
        ('fn deep_values<', COMPENSATED + 'fn deep_values<')], 'argument.zkc')
    final = edited(directory, FRI, [(
        '  require !less(count, length(coefficients));\n'
        '  return concat(coefficients, fill<F>(0, count - length(coefficients)));',
        '  return if less(count, length(coefficients)) { zkc::vector::slice(coefficients, 0, count) }\n'
        '    else { concat(coefficients, fill<F>(0, count - length(coefficients))) };')],
        'fri.zkc')
    package = dishonest(toolchain, journal, directory, 'compensated',
                        {'air::polynomial': truncate, 'stark::single_table': claims,
                         'fri': final})
    produced, proof = package.prove(public, false)
    assert produced['status'] == 'produced'
    terminal = refused_at(package.verify(public, proof, refuses=True), package,
                          'check.terminal', ['0'])
    # The two provers are stopped by different verifier checks.
    assert identity['site'] != terminal['site']


CONFIGURATIONS = '''
use stark::configurations::contract::{Configuration, reversed_rows, reverse_positions};
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
}
'''


def test_outer_row_layouts_are_configurations(toolchain, journal, directory):
    """Natural and bit-reversed outer rows share the mathematical FRI client."""
    height, final, blowup, queries = 32, 1, 2, 16
    bundle, public_data, trace = quadratic_air(height, 3)
    asset = journal.write('bundle.json', bundle)
    proofs = {}
    for configuration in ['Poseidon2', 'Reversed']:
        source = generated(height, final, blowup, queries, configuration, CONFIGURATIONS)
        package = Package.source(toolchain, journal, directory, source, {'trace': asset},
                                 name=configuration, realization=QUARTIC_REALIZATION)
        proofs[configuration] = frames(package.honest({'public_data': public_data},
                                                      {'trace': trace}).read_bytes())
    natural, reversed_ = proofs['Poseidon2'], proofs['Reversed']
    rounds = height.bit_length() - 1 - final
    for messages in (natural, reversed_):
        assert_quartic_frames(messages, log_size=7, final=final, rounds=rounds,
                              queries=queries, width=3, chunks=1, claims=12)
    # The trace commitment precedes challenges and binds a different row order.
    assert natural[0] != reversed_[0]
    journal.write('sizes.json', {name: sum(map(len, value)) for name, value in proofs.items()})


DERIVATION = '''module sample;
use stark::configurations::koala_bear_octic::{Extension};
use stark::configurations::koala_bear_quartic::{Poseidon2, Quartic};
protocol Run roles(P)(draw: Extension @P) -> (challenge: Quartic @P) {
  let challenge @P = Poseidon2::challenge(draw);
  return (challenge = challenge);
}
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
'''


def test_quartic_challenges_are_octic_prefixes(toolchain, journal, directory):
    from entry import Entry
    entry = Entry(toolchain, journal, directory, DERIVATION, library_modules(
        'arguments/stark/configurations/koala_bear_octic',
        'arguments/stark/configurations/koala_bear_quartic'))
    for draw in ([1, 2, 3, 4, 5, 6, 7, 8], [P - 1] * 8, [0] * 7 + [9]):
        result = entry.run(f'draw-{draw[0]}-{draw[-1]}', {'draw': [str(x) for x in draw]})
        assert result['challenge'] == [str(x) for x in draw[:4]]


def test_comparison_with_existing_profile(toolchain, journal, directory):
    """Characterize named deployments of the same small Fibonacci AIR.

    Shared FRI authenticates every logical occurrence in dynamic packets.
    Quartic outer rows retain pruned batching; the octic caller opens outer
    rows separately. These costs do not describe the removed specialized FRI
    implementation or promise a size advantage for other parameters.
    """
    from test_fri import assert_merkle_frames
    public, witness = fibonacci_inputs('Plonky3Proof')
    for entry in ('CleanProof', 'Plonky3Proof'):
        for group in ('public', 'witness'):
            name = f'inputs/example.{entry}/{group}.json'
            assert (PROJECT / name).read_text() == (EXISTING / name).read_text()
    record = {}
    for project in (EXISTING, PROJECT):
        realization = OCTIC_REALIZATION if project == EXISTING else QUARTIC_REALIZATION
        package = Package.project(toolchain, journal, directory, project, 'Plonky3Proof',
                                  realization=realization)
        proof = package.honest(public, witness)
        messages = frames(proof.read_bytes())
        if project == PROJECT:
            assert_quartic_frames(messages, log_size=5, final=0, rounds=3, queries=8,
                                  width=2, chunks=1, claims=8)
        else:
            assert [tag(frame) for frame in messages[:4]] == [33, 35, 27, 27]
            assert len(messages[0]) == len(messages[1]) == 38
            assert vector_count(messages[2], 27, 32) == 8
            assert vector_count(messages[3], 27, 32) == 1
            assert_merkle_frames(messages[4:56], 5, 0, 3, 8)
            assert [tag(frame) for frame in messages[56:]] == [20, 34, 27, 36] * 8
            for query in range(8):
                row, path, quotient, quotient_path = messages[56 + 4 * query:60 + 4 * query]
                assert vector_count(row, 20, 4) == 2
                assert vector_count(quotient, 27, 32) == 1
                assert vector_count(path, 34, 32) == 5
                assert vector_count(quotient_path, 36, 32) == 5
        record[project.name] = {'scheme': QUARTIC_SCHEME if project == PROJECT else OCTIC_SCHEME,
                                **wire_profile(proof.read_bytes())}
    journal.write('comparison.json', record)
    # Occurrence identities bind the transcript, so a compiler change can
    # change sampled positions and hence pruned multiproof sharing. Pin the
    # complete fixed frame inventory, not one transcript's sibling count.
    siblings = sum(record['stark']['frames'][i]['count'] for i in (9, 11))
    assert {name: {key: value[key] for key in ('bytes', 'messages', 'payload_bytes')}
            for name, value in record.items()} == {
                'fibonacci': {'bytes': 19508, 'messages': 88, 'payload_bytes': 18764},
                'stark': {'bytes': 15004 + 32 * siblings, 'messages': 60,
                          'payload_bytes': 14484 + 32 * siblings}}
