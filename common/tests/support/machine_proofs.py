"""The source machine argument through ordinary compilation and proof commands.

These tests cover the selected three-table, Boolean multiplicity profile, both
interaction reductions and the interactive entry. They provide execution and
adversarial evidence, not a proof of cryptographic soundness or upstream VM
compatibility.
"""

from input_files import input_files
import importlib.util
import json
from pathlib import Path



ROOT = Path(__file__).resolve().parents[3]
EXAMPLE = ROOT / 'examples/projects/accumulator-machine'
FIXTURES = ROOT / 'compiler/adapters/accumulator-machine/fixtures'
_spec = importlib.util.spec_from_file_location('machine_proof_requests', EXAMPLE / 'prepare.py')
prepare = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(prepare)


def compile_entry(toolchain, journal, directory, entry, *, flags=(), source=None, edits=(), asset=None, compiled_projects=None):
    path = EXAMPLE / 'main.zkc'
    if source is not None:
        path = directory / 'main.zkc'
        path.write_text(source)
    package = directory / f'{entry}.zkpkg'
    if source is None and not edits and asset is None:
        if compiled_projects is not None:
            return compiled_projects.compile(EXAMPLE / 'zkc.toml', f'accumulator_machine::{entry}', flags, journal)
        report = journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                               f'--project={EXAMPLE}/zkc.toml',
                               f'accumulator_machine::{entry}', f'--output={package}', *flags])
        return package, report['package_sha256']
    command = [toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
               f'--module=accumulator_machine={path}',
               f'--asset=machine=relation-bundle-json={asset or FIXTURES / "bundle.json"}',
               f'accumulator_machine::{entry}', f'--output={package}', *flags]
    for module, file in [('air_bundle', 'air/bundle'), ('air_interaction', 'air/interaction'),
                         ('air_stark', 'air/stark'), ('air_table', 'air/table'),
                         ('air_polynomial', 'air/polynomial'), ('fri', 'fri/lib')]:
        module_path = ROOT / 'libraries' / (file + '.zkc')
        replacements = [(old, new) for owner, old, new in edits if owner == module]
        if replacements:
            text = module_path.read_text()
            for old, new in replacements:
                assert text.count(old) == 1, (module, old)
                text = text.replace(old, new)
            module_path = directory / (module + '.zkc')
            module_path.write_text(text)
        command.append(f'--module={module}={module_path}')
    report = journal.json(command)
    return package, report['package_sha256']


def requests(run, **options):
    return prepare.run_inputs(json.loads((FIXTURES / run / 'run.json').read_text()), **options)


def prove_and_verify(toolchain, journal, directory, package, pin, name, pair):
    prover = input_files(journal, name + '-prover', public=pair[0], witness=pair[1])
    verifier = input_files(journal, name + '-verifier', public=pair[0])
    proof = directory / (name + '.proof')
    produced = journal.json([toolchain.runtime, '--json', 'prove', f'--package={package}', f'--sha256={pin}', *prover, f'--output={proof}'])
    checked = journal.json([toolchain.runtime, '--json', 'verify', f'--package={package}', f'--sha256={pin}', *verifier, f'--proof={proof}'])
    assert produced['status'] == 'produced'
    assert checked['status'] == 'accepted'
    return proof, verifier


def alter_vector(values, position, value=None):
    changed = list(values)
    changed[position] = str((int(values[position]) + 1) % prepare.machine.P if value is None else value)
    return changed


def proof_messages(proof):
    offset, result = 40, []
    while offset < len(proof):
        length = int.from_bytes(proof[offset:offset + 8], 'little')
        result.append(proof[offset + 8:offset + 8 + length])
        offset += 8 + length
    assert offset == len(proof)
    return result


def repack(proof, messages):
    return proof[:40] + b''.join(len(m).to_bytes(8, 'little') + m for m in messages)


def assert_refused(result):
    assert result.returncode > 0, result.stderr
    report = json.loads(result.stdout)
    assert report['status'] == 'refused', report
    return report
