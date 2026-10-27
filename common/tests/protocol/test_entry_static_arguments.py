"""Current C++ relation exports through the strict Rust Entry consumer."""
from collections import Counter
import hashlib
import json
from pathlib import Path

from input_files import input_files

SOURCE = Path(__file__).with_name('sources') / 'typed-relation-arguments.zkc'


def test_native_typed_relation_arguments_reach_rust_entry(toolchain, journal, directory):
    module = f'--module=sample={SOURCE}'
    flags = ['--source-format=zkc', '--entry=sample::Demo', module]
    original = journal.run([toolchain.compiler, 'language-emit', *flags])
    interface = journal.json([toolchain.compiler, 'language-interface', *flags])
    assert interface['original'] == hashlib.sha256(original.encode()).hexdigest()
    rows = interface['relations']
    assert len(rows) == 6
    assert all(set(row) == {'symbol', 'inputs', 'static_arguments', 'definition'} for row in rows)
    opaque = [row for row in rows if row['definition']['kind'] == 'opaque']
    arguments = Counter(json.dumps(row['static_arguments']) for row in opaque)
    expected = [
        [['field', 'bls12-381.fr'], ['nat', '2'], ['nat', '7']],
        [['field', 'bls12-381.fr'], ['nat', '2'], ['nat', '7']],
        [['field', 'koala-bear'], ['nat', '2'], ['nat', '7']],
        [['field', 'bls12-381.fr'], ['nat', '3'], ['nat', '7']],
        [['field', 'bls12-381.fr'], ['nat', '2'], ['nat', '8']],
    ]
    assert arguments == Counter(json.dumps(value) for value in expected)
    assert [row['static_arguments'] for row in rows if row['definition']['kind'] == 'formula'] == [[]]

    source_view = journal.json([toolchain.runtime, '--json', 'inspect',
                               f'--compiler={toolchain.compiler}', module, 'sample::Demo'])
    assert source_view['status'] == 'inspected'
    package = directory / 'typed.zkpkg'
    report = journal.json([toolchain.runtime, '--json', 'compile',
                           f'--compiler={toolchain.compiler}', module,
                           'sample::Demo', f'--output={package}'])
    captured = json.loads(package.read_text())
    assert json.loads(captured['interface']) == interface
    pinned = [f'--package={package}', f'--sha256={report["package_sha256"]}']
    assert journal.json([toolchain.runtime, '--json', 'inspect', *pinned])['status'] == 'inspected'
    inputs = input_files(journal, 'typed', public={'a': '3', 'b': '5', 'flag': True})
    proof = directory / 'typed.proof'
    journal.json([toolchain.runtime, '--json', 'prove', *pinned, *inputs,
                  '--allow-authored', f'--output={proof}'])
    assert journal.json([toolchain.runtime, '--json', 'verify', *pinned, *inputs,
                         '--allow-authored', f'--proof={proof}'])['status'] == 'accepted'
