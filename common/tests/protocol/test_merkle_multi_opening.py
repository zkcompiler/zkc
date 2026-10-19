"""Pruned multi-opening of Poseidon2 row commitments in a native proof.

The prover commits a table, sends the root, receives a challenge, opens several
public positions with one pruned proof and sends the rows and the proof; the
verifier checks them with `oracle.check_many`. Both installed instances run,
over `koala-bear` rows and over quartic-extension rows. The proof's digest
count is compared with a frontier computed here from the positions and the
height alone. These runs check execution, framing and refusal agreement; they
make no binding or extraction claim.
"""
import hashlib

import pytest

from input_files import input_files
from source_modules import core_packages, library_modules

SOURCE = '''module sample;
use zkc::oracle as oracle;
use zkc::indices::{Indices};
domain E = field("koala-bear.ext8-binomial3");
domain F = field("@FIELD@");
domain Rows = commitment("rows.merkle-poseidon2-16.@FIELD@/0");
type Vector<T: Field> = builtin("vector", T);
fn table(size: index) -> Vector<F> { return kernel<F>("vector.geometric", 3, size); }
fn rows(size: index, width: index) -> index { return kernel("index.div", size, width); }
protocol Open roles(P,V)(size:index@(P,V), width:index@(P,V), positions:Indices@(P,V),
    coins:Random<E>@V)->(accepted:bool@V) {
  let values @P=table(size);
  let tree @P=oracle::commit<Rows>(values, width);
  let height @V=rows(size, width);
  let root=send P->V(tree.0);
  let challenge=coins.draw();
  let delivered=send V->P(challenge);
  let opening @P=oracle::open_many<Rows>(tree.1, positions);
  let opened=send P->V(opening.0);
  let proof=send P->V(opening.1);
  let accepted @V=oracle::check_many<Rows>(root, width, height, positions, opened, proof);
  return(accepted=accepted);
}
proof Demo=Open {
  prover P; verifier V; public{size,width,positions}; accept accepted;
  construction fiat_shamir("merlin3.koala-bear.ext8-binomial3.rejection31le/0", coins);
}
'''

FIELDS = ['koala-bear', 'koala-bear.ext4-binomial3']


def frontier(height, positions):
    """Digests a pruned proof sends: siblings of the queried nodes' parents
    that cover no queried leaf, over every level of the padded binary tree."""
    count, nodes = 0, set(positions)
    for _ in range(max(height - 1, 0).bit_length()):
        parents = {n // 2 for n in nodes}
        count += sum(child not in nodes for p in parents for child in (2 * p, 2 * p + 1))
        nodes = parents
    return count


def proof_frame(proof):
    """The digest count of the one ZKCV pruned-proof frame (tag 72)."""
    marker = b'ZKCV\x00\x48'
    assert proof.count(marker) == 1
    start = proof.index(marker) + len(marker)
    return int.from_bytes(proof[start:start + 4], 'little'), start + 4


class Case:
    def __init__(self, toolchain, journal, directory, field):
        self.journal, self.directory, self.runtime = journal, directory, toolchain.runtime
        source = directory / 'opening.zkc'
        source.write_text(SOURCE.replace('@FIELD@', field))
        self.package = directory / 'opening.zkpkg'
        report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                               f'--module=sample={source}', 'sample::Demo',
                               f'--output={self.package}', *library_modules(*core_packages())])
        self.pin = report['package_sha256']
        assert self.pin == hashlib.sha256(self.package.read_bytes()).hexdigest()
        self.runs = 0

    def request(self, size, width, positions):
        self.runs += 1
        return input_files(self.journal, f'request-{self.runs}.json', context='',
                           public={'size': size, 'width': width, 'positions': positions},
                           witness={})

    def prove(self, size, width, positions, refuses=None):
        proof = self.directory / f'proof-{self.runs + 1}.bin'
        report = self.journal.json([self.runtime, '--json', 'prove', f'--package={self.package}',
                                    f'--sha256={self.pin}', *self.request(size, width, positions),
                                    f'--output={proof}'], refuses=refuses)
        return report, proof

    def verify(self, size, width, positions, proof, refuses=None):
        return self.journal.json([self.runtime, '--json', 'verify', f'--package={self.package}',
                                  f'--sha256={self.pin}', *self.request(size, width, positions),
                                  f'--proof={proof}'], refuses=refuses)


@pytest.mark.parametrize('field', FIELDS)
@pytest.mark.parametrize('width,height,positions', [
    (1, 1, [0]),
    (3, 16, [5]),
    (9, 13, [12, 0, 7, 7, 3]),
    (16, 64, [63, 1, 2, 40, 41, 17]),
    (2, 32, list(range(32))),
])
def test_multi_opening_proves_and_verifies(toolchain, journal, directory, field, width, height,
                                           positions):
    case = Case(toolchain, journal, directory, field)
    produced, proof = case.prove(width * height, width, positions)
    assert produced['status'] == 'produced'
    bytes_ = proof.read_bytes()
    count, start = proof_frame(bytes_)
    assert count == frontier(height, positions)
    assert case.verify(width * height, width, positions, proof)['status'] == 'accepted'
    if count:
        # Changing one bit of a canonical digest word keeps the frame
        # canonical; the verifier's check then fails.
        tampered = bytearray(bytes_)
        tampered[start] ^= 1
        changed = directory / 'tampered.bin'
        changed.write_bytes(tampered)
        report = case.verify(width * height, width, positions, changed, refuses=True)
        assert report['status'] != 'accepted'


@pytest.mark.parametrize('field', FIELDS)
def test_positions_are_checked_before_opening(toolchain, journal, directory, field):
    case = Case(toolchain, journal, directory, field)
    report, proof = case.prove(8, 2, [], refuses=True)
    assert 'oracle-positions' in str(report) and not proof.exists()
    report, proof = case.prove(8, 2, [4], refuses=True)
    assert 'oracle-coordinate' in str(report) and not proof.exists()
