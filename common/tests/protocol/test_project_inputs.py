"""Project convenience commands retain explicit Entry and input authority."""
import hashlib
import json
import os
from pathlib import Path

import pytest

from entry import project_invocation


def source_options(toolchain, project):
    return [f'--compiler={toolchain.compiler}', f'--project={project / "zkc.toml"}']


def test_initialize_discover_inspect_fill_check_and_run(toolchain, journal, directory):
    project = directory / 'project'
    initialized = journal.json([toolchain.runtime, '--json', 'new', project, f'--compiler={toolchain.compiler}'])
    assert initialized['status'] == 'initialized'
    assert {p.name for p in project.iterdir()} == {'zkc.toml', 'main.zkc', 'inputs'}
    sentinel = (project / 'main.zkc').read_bytes()
    journal.run([toolchain.runtime, '--json', 'new', project, f'--compiler={toolchain.compiler}'], refuses='source-project-exists')
    assert (project / 'main.zkc').read_bytes() == sentinel
    options = source_options(toolchain, project)
    inspected = journal.json([toolchain.runtime, '--json', 'inspect', *options])
    assert inspected['interface']['entry'] == 'example::Main'
    assert inspected['interface']['kind'] == 'function'
    assert inspected['interface']['signature']['parameters'][0]['name'] == 'value'
    assert 'package_sha256' not in inspected and 'execution' not in inspected
    generated = initialized
    path = project / 'inputs/example.Main/arguments.json'
    assert str(path) in generated['files']
    assert json.loads(path.read_text()) == {'value': None}
    journal.run([toolchain.runtime, '--json', 'run', '--dry-run', *options,
                 f'--input={path}'], refuses='entry-input-unfilled')
    journal.run([toolchain.runtime, '--json', 'run', *options,
                 '--session=forbidden'], refuses='cli-option')
    journal.run([toolchain.runtime, '--json', 'run', *options,
                 '--input=missing'], refuses='entry-input-document')
    path.write_text('{"value":"18446744073709551615"}')
    preserved = journal.json([toolchain.runtime, '--json', 'prepare', *options])
    assert preserved['files'] == [] and preserved['preserved'] == [str(path)]
    arguments = [*options, f'--input={path}']
    checked = journal.json([toolchain.runtime, '--json', 'run', '--dry-run', *arguments])
    assert checked['status'] == 'inputs-checked' and 'execution' not in checked
    output = directory / 'result.json'
    executed = journal.json([toolchain.runtime, '--json', 'run', *arguments, f'--results={output}'])
    assert checked['package_sha256'] == executed['package_sha256']
    assert json.loads(output.read_text())['value'] == '18446744073709551615'
    assert not list(project.rglob('*.zkpkg'))
    child = project / 'subdirectory'
    child.mkdir()
    result = journal.attempt([toolchain.runtime, '--json', 'inspect', f'--compiler={toolchain.compiler}'], cwd=child)
    assert result.returncode == 0 and json.loads(result.stdout)['entry'] == 'example::Main'


def test_selection_filters_only_when_the_name_is_omitted(toolchain, journal, directory):
    project = directory / 'project'
    journal.run([toolchain.runtime, '--json', 'new', project, f'--compiler={toolchain.compiler}'])
    (project / 'protocol.zkc').write_text('''module example_protocol;
    pub protocol Test roles(P,V)(b:bool@P)->(accepted:bool@V){let r=send P->V(b);return r;}
    ''')
    (project / 'main.zkc').write_text('''module example;
    use example_protocol::{Test};
    entry fn Interactive(inputs: Test::Inputs) { return Test::run(inputs); }
    proof Proof=Test{prover P;verifier V;public{};accept accepted;construction authored;}
    ''')
    with (project / 'zkc.toml').open('a') as manifest:
        manifest.write('example_protocol = \"protocol.zkc\"\n')
    options = source_options(toolchain, project)
    journal.run([toolchain.runtime, '--json', 'inspect', *options], refuses='source-compilation')
    for entry, group in [('Interactive', 'arguments'), ('Proof', 'witness')]:
        report = journal.json([toolchain.runtime, '--json', 'prepare', entry, *options])
        assert report['files'] == [str(project / f'inputs/example.{entry}/{group}.json')]
        requirements = report['entries'][0]['requirements']
        if entry == 'Proof':
            assert requirements == {'allow_authored': True, 'setups': []}
        else:
            assert requirements['invocations'] == '--invocations=FILE'
            assert requirements['allow_authored'] is None
            assert requirements['unresolved'] == ['child_policies']
            assert requirements['check_command'] == [*report['entries'][0]['commands'][0], '--dry-run']
        Path(report['files'][0]).write_text(json.dumps(
            {'b': True} if entry == 'Proof' else {'inputs': {'P': {'b': True}, 'V': {}}}))
    p = project / 'inputs/example.Interactive/arguments.json'
    invocation = project_invocation(toolchain, journal, directory, project=project / 'zkc.toml', entry='Interactive')
    run = journal.json([toolchain.runtime, '--json', 'run', 'Interactive', *options, invocation, f'--input={p}'])
    assert run['entry'] == 'example::Interactive'
    witness = project / 'inputs/example.Proof/witness.json'
    proof = directory / 'proof.bin'
    producing = ['--allow-authored', f'--witness={witness}', f'--output={proof}']
    assert journal.json([toolchain.runtime, '--json', 'prove', *options, *producing])['entry'] == 'example::Proof'

    # Explicit short names must remain ambiguous across different execution kinds.
    (project / 'other.zkc').write_text('''module other;
    use example_protocol::{Test};entry fn Proof(inputs: Test::Inputs) { return Test::run(inputs); }''')
    with (project / 'zkc.toml').open('a') as f:
        f.write('\nother = "other.zkc"\n')
    for command, invocation_flags in [('run', [invocation, f'--input={p}']),
                                ('prove', producing)]:
        refused = journal.json([toolchain.runtime, '--json', command, 'Proof', *options, *invocation_flags],
                               refuses='source-compilation')
        assert 'source.entry' in refused['diagnostics'] and 'ambiguous' in refused['diagnostics']
    assert journal.json([toolchain.runtime, '--json', 'prove', 'example::Proof', *options, *producing])['status'] == 'produced'
    assert journal.json([toolchain.runtime, '--json', 'verify', *options, '--allow-authored', f'--proof={proof}'])['status'] == 'accepted'
    refusal = journal.json([toolchain.runtime, '--json', 'prove', 'Interactive', *options, *producing], refuses='source-compilation')
    assert 'source.entry-kind' in refusal['diagnostics']
    journal.run([toolchain.runtime, '--json', 'verify', *options, '--allow-authored', f'--proof={proof}', '--witness=missing'], refuses='cli-option')
    # Additional run Entries require selection; proof selection remains unique.
    with (project / 'main.zkc').open('a') as f:
        f.write('\nentry fn Other(inputs: Test::Inputs) { return Test::run(inputs); }\n')
    journal.run([toolchain.runtime, '--json', 'run', *options, invocation, f'--input={p}'], refuses='source-compilation')
    assert journal.json([toolchain.runtime, '--json', 'prove', *options, *producing])['entry'] == 'example::Proof'


def test_dry_run_checks_inputs_without_executing_or_issuing_resources(toolchain, journal, directory):
    source = directory / 'stopped.zkc'
    source.write_text('''module test;
    protocol Test roles(P,V)(go:bool@P)->(accepted:bool@V){require go;let r=send P->V(go);return r;}
    proof Proof=Test{prover P;verifier V;public{};accept accepted;construction authored;}
    ''')
    options = [f'--compiler={toolchain.compiler}', f'--module=test={source}', '--allow-authored']
    witness = journal.write('witness.json', {'go': False})
    checked = journal.json([toolchain.runtime, '--json', 'prove', '--dry-run', *options, f'--witness={witness}'])
    assert checked['status'] == 'inputs-checked' and 'execution' not in checked
    journal.run([toolchain.runtime, '--json', 'prove', *options, f'--witness={witness}', f'--output={directory / "proof"}'], refuses='artifact-stopped')
    assert journal.json([toolchain.runtime, '--json', 'verify', '--dry-run', *options])['status'] == 'inputs-checked'
    journal.run([toolchain.runtime, '--json', 'verify', '--dry-run', *options, '--witness=missing'], refuses='cli-option')


@pytest.mark.skipif(os.name != 'posix', reason='confined descriptor traversal')
def test_references_are_pinned_confined_bounded_and_protected(toolchain, journal, directory):
    project = directory / 'project'
    journal.run([toolchain.runtime, '--json', 'new', project, f'--compiler={toolchain.compiler}'])
    options = source_options(toolchain, project)
    root = directory / 'data'
    root.mkdir()
    wire = b'ZKCV\x00\x1f' + (7).to_bytes(8, 'little')
    # Use the native index tag, independent of the new readable encoder.
    path = root / 'value.zkcv'
    path.write_bytes(wire)
    pin = hashlib.sha256(wire).hexdigest()
    document = root / 'P.json'
    def select(file='value.zkcv', digest=pin):
        document.write_text(json.dumps({'value': {'file': file, 'sha256': digest}}))
    select()
    command = [toolchain.runtime, '--json', 'run', '--dry-run', *options,
               f'--input={document}']
    assert journal.json(command)['status'] == 'inputs-checked'
    select(digest='00' * 32)
    journal.run(command, refuses='entry-input-reference-digest')
    for name in ['../data/value.zkcv', str(path), './value.zkcv', 'data//value', 'value.zkcv/']:
        select(name)
        report = journal.json(command, refuses='entry-input-reference')
        assert report['input_path'] == 'arguments.value'
    link = root / 'link'
    link.symlink_to(path)
    for name in ['link', 'absent']:
        select(name)
        journal.run(command, refuses='entry-input-reference')
    nested = root / 'nested'
    nested.mkdir()
    (nested / 'value.zkcv').write_bytes(wire)
    select('nested/value.zkcv')
    assert journal.json(command)['status'] == 'inputs-checked'
    alias = root / 'directory-link'
    alias.symlink_to(nested, target_is_directory=True)
    select('directory-link/value.zkcv')
    journal.run(command, refuses='entry-input-reference')
    fifo = root / 'fifo'
    os.mkfifo(fifo)
    select('fifo')
    journal.run(command, refuses='entry-input-reference', timeout=10)
    select()
    running = [toolchain.runtime, '--json', 'run', *options, f'--input={document}']
    hardlink = root / 'hardlink'
    os.link(path, hardlink)
    for destination in [path, hardlink, document]:
        journal.run([*running, f'--results={destination}'], refuses='entry-output-path')
        assert path.read_bytes() == wire
    capacity = journal.write('capacity.json', ['zkc.native-capacity/0', '65536', '4096', '8', '67108864',
        ['1000000', '100000', '4294967296'], ['67108864', '268435456']])
    # Document parsing has a separate bound; this cap applies to referenced wire.
    journal.run([*command, f'--capacity={capacity}'], refuses='entry-input-reference-byte-limit')
    oversized = wire + bytes(1024)
    path.write_bytes(oversized)
    select(digest=hashlib.sha256(oversized).hexdigest())
    capacity = journal.write('reference-capacity.json', ['zkc.native-capacity/0', '65536', '4096', '256', '67108864',
        ['1000000', '100000', '4294967296'], ['67108864', '268435456']])
    journal.run([*command, f'--capacity={capacity}'], refuses='entry-input-reference-byte-limit')


def test_modes_and_templates_never_guess_or_replace_inputs(toolchain, journal, directory):
    project = directory / 'project'
    journal.run([toolchain.runtime, '--json', 'new', project, f'--compiler={toolchain.compiler}'])
    options = source_options(toolchain, project)
    package = directory / 'entry.zkpkg'
    built = journal.json([toolchain.runtime, '--json', 'compile', *options, f'--output={package}'])
    pinned = [f'--package={package}', f'--sha256={built["package_sha256"]}']
    for extra in [['Main'], options, ['--compiler=missing']]:
        journal.run([toolchain.runtime, '--json', 'inspect', *pinned, *extra], refuses='cli-usage')
    journal.run([toolchain.runtime, '--json', 'inspect', *pinned, '--no-simplify'], refuses='cli-option')
    journal.run([toolchain.runtime, '--json', 'inspect', f'--package={package}'], refuses='cli-usage')
    journal.run([toolchain.runtime, '--json', 'prepare', *pinned], refuses='source-output-required')
    generated = journal.json([toolchain.runtime, '--json', 'prepare', *pinned, f'--output={directory / "templates"}'])
    assert generated['files'] == [str(directory / 'templates/arguments.json')]
    journal.run([toolchain.runtime, '--json', 'run', *pinned, '--input=missing.json'], refuses='entry-input-document')
    source = directory / 'unit.zkc'
    source.write_text('module u;entry fn Main(u:())->(){return u;}')
    explicit = [f'--compiler={toolchain.compiler}', f'--module=u={source}']
    generated = journal.json([toolchain.runtime, '--json', 'prepare', *explicit, f'--output={directory / "unit"}'])
    path = Path(generated['files'][0])
    assert json.loads(path.read_text()) == {'u': None}
    journal.run([toolchain.runtime, '--json', 'run', *explicit], refuses='entry-input-missing')
    assert journal.json([toolchain.runtime, '--json', 'run', *explicit, f'--input={path}'])['status'] == 'executed'


def test_dry_run_ignores_proof_and_result_paths_without_publication(toolchain, journal, directory):
    source = directory / 'stopped.zkc'
    source.write_text('''module test;
    protocol Test roles(P,V)(go:bool@P)->(accepted:bool@V){
      require go;let r=send P->V(go);return r;
    }
    proof Proof=Test{prover P;verifier V;public{};accept accepted;construction authored;}
    ''')
    target = [f'--compiler={toolchain.compiler}', f'--module=test={source}']
    witness = journal.write('witness.json', {'go': False})
    arguments = journal.write('arguments.json', {'inputs': {'P': {'go': False}, 'V': {}}})
    absent = directory / 'never-created'
    for operation, inputs in [
        ('run', [f'--input={arguments}', f'--results={absent}/run.json']),
        ('prove', ['--allow-authored', f'--witness={witness}',
                   f'--output={absent}/proof', f'--results={absent}/prove.json']),
        ('verify', ['--allow-authored', f'--proof={absent}/proof',
                    f'--results={absent}/verify.json']),
    ]:
        result = journal.json([toolchain.runtime, '--json', operation, '--dry-run', *target, *inputs])
        assert result['status'] == 'inputs-checked' and result['dry_run'] is True
        assert not {'execution', 'proof', 'output', 'results'} & result.keys()
        assert not absent.exists()
    # Existing destinations are not opened or overwritten, even if they alias inputs.
    before = witness.read_bytes()
    journal.json([toolchain.runtime, '--json', 'prove', '--dry-run', *target,
                  '--allow-authored', f'--witness={witness}', f'--output={witness}'])
    assert witness.read_bytes() == before
    witness.unlink()
    if os.name == 'posix':
        proof = directory / 'proof-fifo'
        os.mkfifo(proof)
        journal.json([toolchain.runtime, '--json', 'verify', '--dry-run', *target,
                      '--allow-authored', f'--proof={proof}'], timeout=10)


def test_prepare_output_override_selects_one_entry_and_preserves_inputs(toolchain, journal, directory):
    project = directory / 'project'
    journal.json([toolchain.runtime, '--json', 'new', project, f'--compiler={toolchain.compiler}'])
    with (project / 'main.zkc').open('a') as source:
        source.write('\nentry fn Other(value:index)->index{return value;}\n')
    options = source_options(toolchain, project)
    output = directory / 'custom'
    journal.json([toolchain.runtime, '--json', 'prepare', *options, f'--output={output}'],
                 refuses='source-compilation')
    assert not output.exists()
    prepared = journal.json([toolchain.runtime, '--json', 'prepare', 'Other', *options, f'--output={output}'])
    assert [entry['name'] for entry in prepared['entries']] == ['example::Other']
    value = output / 'arguments.json'
    value.write_text('{"value":"23"}')
    preserved = journal.json([toolchain.runtime, '--json', 'prepare', 'Other', *options, f'--output={output}'])
    assert preserved['files'] == [] and preserved['preserved'] == [str(value)]
    assert value.read_text() == '{"value":"23"}'
    arguments = prepared['entries'][0]['commands'][0]
    executed = journal.json([toolchain.runtime, '--json', *arguments[1:]])
    assert executed['status'] == 'executed'
    # The same policy applies to authenticated packages without project discovery.
    package = directory / 'entry.zkpkg'
    built = journal.json([toolchain.runtime, '--json', 'compile', 'Other', *options, f'--output={package}'])
    pinned = [f'--package={package}', f'--sha256={built["package_sha256"]}']
    repeated = journal.json([toolchain.runtime, '--json', 'prepare', *pinned, f'--output={output}'])
    assert repeated['preserved'] == [str(value)] and value.read_text() == '{"value":"23"}'
    value.unlink()
    value.symlink_to(project / 'main.zkc')
    journal.json([toolchain.runtime, '--json', 'prepare', *pinned, f'--output={output}'],
                 refuses='entry-output-exists')
