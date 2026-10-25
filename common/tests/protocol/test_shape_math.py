"""Total shape source evaluation and bounded native target execution."""
import json
from pathlib import Path

from input_files import input_files


def test_total_shape_source_success_and_target_exhaustion(toolchain, journal, directory):
    root = Path(__file__).resolve().parents[3]
    fixture = root / 'compiler/test/fixtures/structured-source/shape.zkc'
    flags = ['--source-format=zkc', '--subject=sample::Run', f'--module=sample={fixture}']
    source = journal.run([toolchain.compiler, 'language-emit', *flags])
    interface = journal.json([toolchain.compiler, 'language-interface', *flags])
    original = directory / 'shape.mlir'
    original.write_text(source)
    request = journal.write('source-request.json', ['zkc.structured-open-request/0',
        'role00000000', [['1', '2'], '2', '1'], [], 1000000])
    observer = toolchain.directories['compiler'] / 'test/zkc-structured_reference-test'
    observed = journal.json([observer, 'open', original, interface['protocol'], request],
                            keep='source-result.json')
    assert observed[1] == ['returned', [True, '2', False, True]]

    package = directory / 'shape.zkpkg'
    built = journal.json([toolchain.runtime, '--json', 'compile',
        f'--compiler={toolchain.compiler}', f'--module=sample={fixture}',
        'sample::Demo', f'--output={package}'])
    inputs = input_files(journal, 'shape', arguments={
        'inputs': {'P': {'values': ['1', '2'], 'n': '2', 'r': '1'}}}, package=package)
    command = [toolchain.runtime, '--json', 'run', f'--package={package}',
               f'--sha256={built["package_sha256"]}', *inputs]
    output = directory / 'success.json'
    normal = journal.json([*command, f'--results={output}'], keep='target-success.json')
    assert normal['execution']['completed']
    assert normal['execution']['usage']['instructions'] > 100
    assert json.loads(output.read_text())['value'] == {
        'P': {'power': True, 'length': '2', 'less': False, 'shape': True}}

    capacity = journal.write('low.capacity.json', [
        'zkc.native-capacity/0', '65536', '4096', '16777216', '67108864',
        ['100', '100000', '4294967296'], ['67108864', '268435456']])
    unpublished = directory / 'exhausted.json'
    refused = journal.json([*command, f'--capacity={capacity}',
                            f'--results={unpublished}'], refuses=True,
                           keep='target-exhaustion.json')
    assert refused['status'] == 'refused'
    assert refused['code'] == 'entry-host-run-failed'
    assert not refused['execution']['completed'] and not unpublished.exists()
    assert refused['execution']['usage']['instructions'] <= 100
    assert refused['execution']['failure']['path']
    call, = refused['execution']['calls']
    assert call['operation'] == 'run' and not call['completed']
    stopped = call['native']['failure_role']['after']
    assert stopped[0] == 'stopped' and stopped[1]['cause'] == ['limit']
    assert stopped[1]['local']['function'], 'target must reach its compiled calculation'
