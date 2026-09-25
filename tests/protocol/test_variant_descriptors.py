"""Common graph refusal corpus, independently admitted by compiler and Lean.

The native reader also consumes this exact corpus in its backend unit tests.
"""
import json
from pathlib import Path

import pytest
from journal import Journal

CORPUS = json.loads((Path(__file__).resolve().parents[2] / 'tests/fixtures/variants/descriptors.json').read_text())


@pytest.mark.parametrize('name,accepted,graph', CORPUS, ids=[row[0] for row in CORPUS])
def test_variant_descriptor(toolchain, directory, name, accepted, graph):
    spelling = 'variant:' + json.dumps(graph, ensure_ascii=False, separators=(',', ':')).encode().hex()
    source = ['zkc.protocol/1', [],
              [['function', 'Inspect', [['v', spelling]], [], [['return', []]], ['Inspect', []]]],
              [['protocol', 'Main', ['P'], [], [], [], [], [['return', []]]]],
              [['instance', 'concrete', 'Main', [], [], [['P', 'P']]]],
              [['entry', 'main', 'concrete']]]
    journal = Journal(directory)
    path = journal.write('source.json', source)
    native = journal.attempt([toolchain.compiler, 'protocol-admit', path])
    reference = json.loads(journal.attempt([toolchain.checker('interactive-protocol'), '--admit', path]).stdout)
    assert (native.returncode == 0) == accepted, (name, native.stderr)
    assert (reference[0] == 'checked') == accepted, (name, reference)
    if not accepted:
        assert 'binding-type:' in native.stderr, (name, native.stderr)
        assert reference == ['refused', 'binding-type'], (name, reference)
    journal.save()
