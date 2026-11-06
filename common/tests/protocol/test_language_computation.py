"""All-layout imported Views, scoped consumers and unified reduction notation."""
import hashlib
import json
from pathlib import Path

import pytest

from entry import joint_package
from input_files import invocation_file

FIXTURES = Path(__file__).resolve().parents[3] / 'compiler/test/fixtures/layout/computation'


@pytest.mark.parametrize('flags', [(), ('--no-simplify',), ('--no-finite-bulk',)])
def test_imported_finite_reductions_execute(toolchain, journal, directory, flags):
    source_flags = [f'--module={name}={FIXTURES / filename}' for name, filename in (
        ('collections', 'collections.zkc'), ('reductions', 'reductions.zkc'),
        ('m', 'client.zkc'))]
    encoded = journal.run([toolchain.compiler, 'language-package',
                           '--source-format=zkc-layout', '--entry=m::Demo',
                           *source_flags, *flags])
    package = directory / 'computation.zkpkg'
    package.write_text(encoded)
    pin = hashlib.sha256(package.read_bytes()).hexdigest()
    original = joint_package(json.loads(encoded))['original']
    assert '"data.finite_fold"' in original and '"exec.fold"' in original
    for ordinal, (values, needle, shift) in enumerate([
        ([], 2, 1), ([2, 3], 2, 1), ([2, 3], 7, 1), ([2, 2, 3], 2, 2),
    ]):
        inputs = journal.write(f'inputs-{ordinal}.json', {'inputs': {'P': {
            'xs': [str(value) for value in values], 'needle': str(needle),
            'shift': str(shift),
        }}})
        binding = invocation_file(journal, f'invocations-{ordinal}.json', package)
        output = directory / f'outputs-{ordinal}.json'
        result = journal.json([toolchain.runtime, '--json', 'run',
                               f'--package={package}', f'--sha256={pin}',
                               f'--input={inputs}', binding, f'--results={output}'])
        assert result['status'] == 'executed'
        expected = sum(value + shift for value in values) + sum(
            value * value for value in values if value == needle)
        assert json.loads(output.read_text())['value']['P']['result'] == str(expected)
