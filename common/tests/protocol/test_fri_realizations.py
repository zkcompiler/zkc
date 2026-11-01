"""One quartic FRI subject under independently selected oracle realizations."""

import json

from coset_reference import CosetReference
from input_files import input_files
from oracle_deployment import table_realization
from source_modules import library_modules
from message_frames import children, replace_child, tag
from test_fri import authentication_rejection, messages, replace_messages


SOURCE = '''module sample;
use fri::{Configuration, ScalarLowDegree};
use zkc::vector::{Vector};
use zkc::indices::{Indices};
use zkc::encoding as encoding;
use zkc::bytes as bytes;
domain F = field("koala-bear.ext4-binomial3");
domain C = field("koala-bear.ext8-binomial3");
module Quartic: Configuration {
  type Value: Field = F;
  type Challenge: Field = C;
  fn challenge(draw: C) -> F effects(stop) where () {
    let words = encoding::field_le<C>(draw);
    let (valid, value) = encoding::field_from_le<F>(bytes::slice(words, 0, 16));
    require valid;
    return value;
  }
}
protocol Fri roles(P,V)(word: Vector<F> @P, shift: F @(P,V),
    round_count: index @(P,V), query_count: index @(P,V), coins: Random<C> @V)
    -> (accepted: bool @V, positionsP: Indices @P,
        positionsV: Indices @V, valuesV: Vector<F> @V) {
  let (accepted, positionsP, positionsV, valuesV) =
    ScalarLowDegree<Quartic,4,0,2,4>(word, shift, shift, round_count, query_count, coins);
  return (accepted = accepted, positionsP = positionsP,
    positionsV = positionsV, valuesV = valuesV);
}
proof Proof = Fri {
  prover P;
  verifier V;
  public { shift, round_count, query_count };
  accept accepted;
  construction fiat_shamir("merlin3.koala-bear.ext8-binomial3.rejection31le/0", coins);
}
'''


def test_one_fri_subject_under_clear_poseidon_and_keccak(toolchain, journal, directory):
    source = directory / 'fri.zkc'
    source.write_text(SOURCE)
    ref = CosetReference('koala-bear.ext4-binomial3')
    shift = (3, 1, 0, 0)
    coefficients = [(i + 1, i * i, 2 * i, 1) for i in range(4)]
    word = [ref.encode(ref.horner(coefficients, point))
            for point in ref.domain(shift, 16)]
    public = {'shift': ref.encode(shift), 'round_count': '2', 'query_count': '4'}
    producer = input_files(journal, 'producer.json', public=public, witness={'word': word})
    verifier = input_files(journal, 'verifier.json', public=public)
    profiles = [
        ('clear', table_realization('')),
        ('poseidon', table_realization('rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0')),
        ('keccak-pairs', table_realization('rows.merkle-keccak256.koala-bear.ext4-binomial3/0',
                                         grouping='antipodal-pairs', table_order='bit-reversed')),
    ]
    subjects, interfaces, pins = [], [], set()
    for name, selection in profiles:
        package = directory / f'{name}.zkpkg'
        compiled = journal.json([toolchain.runtime, '--json', 'compile',
                                 f'--compiler={toolchain.compiler}', f'--module=sample={source}',
                                 *library_modules('protocols/polynomial/fri', 'core/encoding'),
                                 'sample::Proof', f'--output={package}', selection])
        pins.add(compiled['package_sha256'])
        captured = json.loads(package.read_text())
        subjects.append(captured['original'])
        interfaces.append(captured['interface'])
        target = [f'--package={package}', f'--sha256={compiled["package_sha256"]}']
        proof = directory / f'{name}.proof'
        producer_results = directory / f'{name}-producer.json'
        verifier_results = directory / f'{name}-verifier.json'
        made = journal.json([toolchain.runtime, '--json', 'prove', *target, *producer,
                             f'--output={proof}', f'--results={producer_results}'])
        assert made['status'] == 'produced'
        checked = journal.json([toolchain.runtime, '--json', 'verify', *target, *verifier,
                                f'--proof={proof}', f'--results={verifier_results}'])
        assert checked['status'] == 'accepted'
        actual = json.loads(verifier_results.read_text())['values']
        positions = list(map(int, actual['positionsV']))
        assert actual['accepted'] is True and len(positions) == 4
        assert all(0 <= position < len(word) for position in positions)
        assert actual['valuesV'] == [word[position] for position in positions]
        assert json.loads(producer_results.read_text())['values'] == {
            'positionsP': actual['positionsV']}
        encoded = proof.read_bytes()
        frames = messages(encoded)
        journal.write(f'{name}-wire.json', {
            'bytes': len(encoded), 'frames': len(frames),
            'tags': [tag(frame) for frame in frames],
            'lengths': [len(frame) for frame in frames],
        })
        if name == 'clear':
            assert [tag(frame) for frame in frames] == [22, 22, 22]
            assert [int.from_bytes(frame[6:10], 'little') for frame in frames] == [16, 8, 1]
            continue
        paired = name == 'keccak-pairs'
        assert len(frames) == 2 + 1 + 2 * 2 * 4
        assert [tag(frame) for frame in frames[:3]] == ([79, 79, 22] if paired else [71, 71, 22])
        # A paired leaf supplies both values in one authenticated row. Logical
        # low/high reads remain distinct; their complete physical leaf is shared.
        for query in range(4):
            for layer in range(2):
                for fold in (False, True):
                    packet = frames[3 + 2 * (2 * query + layer) + fold]
                    answers = children(packet)
                    assert len(answers) == (1 if paired or not fold else 2)
                    for answer in answers:
                        row, path = children(answer)
                        assert tag(answer) == 65 and answer[6:10] == bytes(4)
                        assert tag(row) == 22 and len(row) == (42 if paired else 26)
                        assert int.from_bytes(row[6:10], 'little') == (2 if paired else 1)
                        assert tag(path) == (80 if paired else 72)
                        assert int.from_bytes(path[6:10], 'little') == 4 - layer - paired
                        assert len(path) == 10 + 32 * (4 - layer - paired)

        descriptor = json.loads(captured['artifact'])[2]

        def refuse(label, replacement):
            altered = directory / f'{name}-{label}.proof'
            altered.write_bytes(replace_messages(encoded, {4: replacement}))
            result = journal.json([toolchain.runtime, '--json', 'verify', *target, *verifier,
                                   f'--proof={altered}'], refuses='rejected:require')
            return authentication_rejection(result, descriptor, element=False)

        packet = frames[4]  # first virtual fold, after the first actual query
        for child, answer in enumerate(children(packet)):
            row, path = children(answer)
            for value in range(2 if paired else 1):
                changed = bytearray(row)
                at = 10 + 16 * value
                coefficient = int.from_bytes(changed[at:at + 4], 'little')
                changed[at:at + 4] = ((coefficient + 1) % ref.modulus).to_bytes(4, 'little')
                assert refuse(f'row-{child}-{value}', replace_child(
                    packet, [child, 0], bytes(changed))) == (0, 0, True)
            # Keep canonical path framing while omitting a complete digest.
            shortened = path[:6] + (int.from_bytes(path[6:10], 'little') - 1).to_bytes(4, 'little') + path[10:-32]
            assert refuse(f'path-{child}', replace_child(packet, [child, 1], shortened)) == (0, 0, True)
        if paired:
            row = children(children(packet)[0])[0]
            incomplete = row[:6] + (1).to_bytes(4, 'little') + row[10:26]
            assert refuse('incomplete-pair', replace_child(packet, [0, 0], incomplete)) == (0, 0, True)
    # Physical choices change deployment identity, not the retained protocol or
    # source interface. Transcript challenges need not agree across deployments.
    assert len(pins) == 3
    assert subjects[0] == subjects[1] == subjects[2]
    assert interfaces[0] == interfaces[1] == interfaces[2]
