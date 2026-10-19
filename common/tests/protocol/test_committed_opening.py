"""The committed-opening example: one Keccak row commitment, one index request and a terminal opening.

The proof carries three messages: the root, the opened row and its authentication path. An
independent Keccak-256 (`hash_chain_reference.py`) recomputes the tree of the honest table with
the leaf and node encodings of `docs/spec/domains/oracles.md` and checks that the path
authenticates the row, lowest level first, against the root the proof carries. These runs check
execution, encoding and rejection; they establish no security property of the example.
"""
from pathlib import Path

import pytest

import hash_chain_reference as reference
from input_files import input_files

ROOT = Path(__file__).resolve().parents[3]
PROJECT = ROOT / 'examples/projects/committed-opening'
WIDTH, HEIGHT, DEPTH = 3, 8, 3
CODEC = b'koala-bear.canonical-u32le/0'
# ZKCV leaf tags of the KoalaBear Merkle root, field vector and Merkle path.
ROOT_TAG, ROW_TAG, PATH_TAG = 33, 20, 34


def table(offset=0):
    return [[i + 1, i + 2, (i + 1) * (i + 2) + offset] for i in range(HEIGHT)]


def compile_entry(toolchain, journal, directory):
    package = directory / 'Proof.zkpkg'
    report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                           f'--project={PROJECT}/zkc.toml', 'example::Proof', f'--output={package}'])
    return package, report['package_sha256']


def prove(toolchain, journal, directory, package, pin, rows, name):
    producer = input_files(journal, f'{name}.json', witness={'table': [v for row in rows for v in row]})
    proof = directory / f'{name}.bin'
    made = journal.json([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}',
                         *producer, f'--output={proof}'])
    assert made['status'] == 'produced'
    return proof


def verify(toolchain, journal, package, pin, proof, refuses=None):
    return journal.run([toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}',
                        f'--proof={proof}'], refuses=refuses)


def messages(proof):
    at, result = 40, []
    while at < len(proof):
        size = int.from_bytes(proof[at:at + 8], 'little')
        result.append(proof[at + 8:at + 8 + size])
        at += 8 + size
    assert at == len(proof)
    return result


def leaf(row):
    header = (b'zkc.oracle.keccak256.leaf/0\0' + len(CODEC).to_bytes(8, 'little') + CODEC
              + WIDTH.to_bytes(8, 'little') + HEIGHT.to_bytes(8, 'little'))
    return reference.keccak256(header + b''.join(v.to_bytes(4, 'little') for v in row))


def node(left, right):
    return reference.keccak256(b'zkc.oracle.keccak256.node/0\0' + left + right)


def tree_root(rows):
    layer = [leaf(row) for row in rows]
    while len(layer) > 1:
        layer = [node(layer[2 * k], layer[2 * k + 1]) for k in range(len(layer) // 2)]
    return layer[0]


def climb(index, path, label):
    for sibling in path:
        label = node(label, sibling) if index % 2 == 0 else node(sibling, label)
        index //= 2
    return label


def test_committed_opening_matches_the_reference_tree(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory)
    proof = prove(toolchain, journal, directory, package, pin, table(), 'honest')
    verify(toolchain, journal, package, pin, proof)
    root, row, path = messages(proof.read_bytes())
    assert root[:6] == b'ZKCV\x00' + bytes([ROOT_TAG]) and len(root) == 38
    assert root[6:] == tree_root(table())
    assert row[:6] == b'ZKCV\x00' + bytes([ROW_TAG]) and int.from_bytes(row[6:10], 'little') == WIDTH
    opened = [int.from_bytes(row[10 + 4 * k:14 + 4 * k], 'little') for k in range(WIDTH)]
    assert len(row) == 10 + 4 * WIDTH
    assert path[:6] == b'ZKCV\x00' + bytes([PATH_TAG]) and int.from_bytes(path[6:10], 'little') == DEPTH
    assert len(path) == 10 + 32 * DEPTH
    siblings = [path[10 + 32 * k:42 + 32 * k] for k in range(DEPTH)]
    position = table().index(opened)
    assert climb(position, siblings, leaf(opened)) == root[6:]
    # The path authenticates the opened row at its own position only.
    assert all(climb(other, siblings, leaf(opened)) != root[6:]
               for other in range(HEIGHT) if other != position)


@pytest.mark.parametrize('message, at', [(0, 6), (1, 10), (2, 10), (2, -1)],
                         ids=['root', 'row-value', 'path-first', 'path-last'])
def test_committed_opening_rejects_a_changed_message(toolchain, journal, directory, message, at):
    package, pin = compile_entry(toolchain, journal, directory)
    proof = prove(toolchain, journal, directory, package, pin, table(), 'honest')
    original = proof.read_bytes()
    frames = messages(original)
    changed = bytearray(frames[message])
    changed[at] ^= 1
    frames[message] = bytes(changed)
    altered = directory / 'altered.bin'
    altered.write_bytes(original[:40] + b''.join(len(x).to_bytes(8, 'little') + x for x in frames))
    verify(toolchain, journal, package, pin, altered, refuses='artifact-stopped')


def test_committed_opening_rejects_a_table_whose_rows_fail(toolchain, journal, directory):
    package, pin = compile_entry(toolchain, journal, directory)
    proof = prove(toolchain, journal, directory, package, pin, table(offset=1), 'failing')
    verify(toolchain, journal, package, pin, proof, refuses='artifact-rejected')
