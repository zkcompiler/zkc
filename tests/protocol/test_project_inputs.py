"""Project convenience commands retain explicit Entry and input authority."""
import hashlib
import json
import os
from pathlib import Path

import pytest


def source_options(toolchain, project):
    return [f'--compiler={toolchain.compiler}', f'--project={project / "zkc.toml"}']


def test_initialize_discover_inspect_fill_check_and_run(toolchain, journal, directory):
    project = directory / 'project'
    initialized = journal.json([toolchain.runtime, 'init', project])
    assert initialized['status'] == 'initialized'
    assert initialized['next'][0] == ['zkc', 'check', f'--project={project / "zkc.toml"}']
    assert {p.name for p in project.iterdir()} == {'zkc.toml', 'protocol.zkc', 'main.zkc'}
    sentinel = (project / 'protocol.zkc').read_bytes()
    journal.run([toolchain.runtime, 'init', project], refuses='entry-output-exists')
    assert (project / 'protocol.zkc').read_bytes() == sentinel
    options = source_options(toolchain, project)
    inspected = journal.json([toolchain.runtime, 'inspect', *options])
    assert inspected['interface']['entry'] == 'example::Main'
    assert inspected['interface']['input_groups'][0]['name'] == 'P'
    assert 'package_sha256' not in inspected and 'execution' not in inspected
    generated = journal.json([toolchain.runtime, 'inputs', 'init', *options])
    path = project / 'inputs/example.Main/P.json'
    assert generated['files'] == [str(path)]
    assert json.loads(path.read_text()) == {'value': None}
    journal.run([toolchain.runtime, 'inputs', 'check', '--operation=run', *options,
                 '--session=project', f'--input=P={path}'], refuses='entry-input-unfilled')
    journal.run([toolchain.runtime, 'run', *options, '--session=project',
                 '--input=p=missing'], refuses='entry-input-roles')
    journal.run([toolchain.runtime, 'run', *options, '--session=project',
                 '--input=P=missing'], refuses='entry-input-document')
    path.write_text('{"value":"18446744073709551615"}')
    journal.run([toolchain.runtime, 'inputs', 'init', *options], refuses='entry-output-exists')
    arguments = [*options, '--session=project', f'--input=P={path}']
    checked = journal.json([toolchain.runtime, 'inputs', 'check', '--operation=run', *arguments])
    assert checked['status'] == 'inputs-checked' and 'execution' not in checked
    output = directory / 'result.json'
    executed = journal.json([toolchain.runtime, 'run', *arguments, f'--results={output}'])
    assert checked['package_sha256'] == executed['package_sha256']
    assert json.loads(output.read_text())['roles'] == {'P': {'result': '18446744073709551615'}}
    assert not list(project.rglob('*.zkpkg'))
    child = project / 'subdirectory'
    child.mkdir()
    result = journal.attempt([toolchain.runtime, 'inspect', f'--compiler={toolchain.compiler}'], cwd=child)
    assert result.returncode == 0 and json.loads(result.stdout)['entry'] == 'example::Main'


def test_selection_filters_only_when_the_name_is_omitted(toolchain, journal, directory):
    project = directory / 'project'
    journal.run([toolchain.runtime, 'init', project])
    (project / 'protocol.zkc').write_text('''module example_protocol;
    pub protocol Test roles(P,V)(b:bool@P)->(accepted:bool@V){let r=send P->V(b);return r;}
    ''')
    (project / 'main.zkc').write_text('''module example;
    use example_protocol::{Test};
    run Interactive=Test;
    proof Proof=Test{prover P;verifier V;public{};accept accepted;construction authored;}
    ''')
    options = source_options(toolchain, project)
    journal.run([toolchain.runtime, 'inspect', *options], refuses='source-compilation')
    journal.run([toolchain.runtime, 'inputs', 'init', *options], refuses='source-compilation')
    for entry, group in [('Interactive', 'P'), ('Proof', 'witness')]:
        report = journal.json([toolchain.runtime, 'inputs', 'init', entry, *options])
        assert report['files'] == [str(project / f'inputs/example.{entry}/{group}.json')]
        assert report['requirements'] == {'allow_header_only': entry == 'Proof', 'setups': []}
        Path(report['files'][0]).write_text('{"b":true}')
    p = project / 'inputs/example.Interactive/P.json'
    run = journal.json([toolchain.runtime, 'run', *options, '--session=test', f'--input=P={p}'])
    assert run['entry'] == 'example::Interactive'
    witness = project / 'inputs/example.Proof/witness.json'
    proof = directory / 'proof.bin'
    producing = ['--allow-header-only', f'--witness={witness}', f'--output={proof}']
    assert journal.json([toolchain.runtime, 'prove', *options, *producing])['entry'] == 'example::Proof'

    # Explicit short names must remain ambiguous across different execution kinds.
    (project / 'other.zkc').write_text('''module other;
    use example_protocol::{Test};run Proof=Test;''')
    with (project / 'zkc.toml').open('a') as f:
        f.write('\nother = "other.zkc"\n')
    for command, invocation in [('run', ['--session=test', f'--input=P={p}']),
                                ('prove', producing)]:
        refused = journal.json([toolchain.runtime, command, 'Proof', *options, *invocation],
                               refuses='source-compilation')
        assert 'source.entry' in refused['diagnostics'] and 'ambiguous' in refused['diagnostics']
    assert journal.json([toolchain.runtime, 'prove', 'example::Proof', *options, *producing])['status'] == 'produced'
    assert journal.json([toolchain.runtime, 'verify', *options, '--allow-header-only', f'--proof={proof}'])['status'] == 'accepted'
    refusal = journal.json([toolchain.runtime, 'prove', 'Interactive', *options, *producing], refuses='source-compilation')
    assert 'source.entry-kind' in refusal['diagnostics']
    journal.run([toolchain.runtime, 'verify', *options, '--allow-header-only', f'--proof={proof}', '--witness=missing'], refuses='cli-option')
    # Additional run Entries require selection; proof selection remains unique.
    with (project / 'main.zkc').open('a') as f:
        f.write('\nrun Other=Test;\n')
    journal.run([toolchain.runtime, 'run', *options, '--session=test', f'--input=P={p}'], refuses='source-compilation')
    assert journal.json([toolchain.runtime, 'prove', *options, *producing])['entry'] == 'example::Proof'


def test_check_prepares_without_executing_or_issuing_resources(toolchain, journal, directory):
    source = directory / 'stopped.zkc'
    source.write_text('''module test;
    protocol Test roles(P,V)(go:bool@P)->(accepted:bool@V){require go;let r=send P->V(go);return r;}
    proof Proof=Test{prover P;verifier V;public{};accept accepted;construction authored;}
    ''')
    options = [f'--compiler={toolchain.compiler}', f'--module=test={source}', '--allow-header-only']
    witness = journal.write('witness.json', {'go': False})
    checked = journal.json([toolchain.runtime, 'inputs', 'check', '--operation=prove', *options, f'--witness={witness}'])
    assert checked['status'] == 'inputs-checked' and 'execution' not in checked
    journal.run([toolchain.runtime, 'prove', *options, f'--witness={witness}', f'--output={directory / "proof"}'], refuses='artifact-stopped')
    assert journal.json([toolchain.runtime, 'inputs', 'check', '--operation=verify', *options])['status'] == 'inputs-checked'
    journal.run([toolchain.runtime, 'inputs', 'check', *options], refuses='cli-usage')
    journal.run([toolchain.runtime, 'inputs', 'check', '--operation=verify', *options, '--witness=missing'], refuses='cli-option')


@pytest.mark.skipif(os.name != 'posix', reason='confined descriptor traversal')
def test_references_are_pinned_confined_bounded_and_protected(toolchain, journal, directory):
    project = directory / 'project'
    journal.run([toolchain.runtime, 'init', project])
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
    command = [toolchain.runtime, 'inputs', 'check', '--operation=run', *options,
               '--session=reference', f'--input=P={document}']
    assert journal.json(command)['status'] == 'inputs-checked'
    select(digest='00' * 32)
    journal.run(command, refuses='entry-input-reference-digest')
    for name in ['../data/value.zkcv', str(path), './value.zkcv', 'data//value', 'value.zkcv/']:
        select(name)
        report = journal.json(command, refuses='entry-input-reference')
        assert report['input_path'] == 'P.value'
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
    running = [toolchain.runtime, 'run', *options, '--session=reference', f'--input=P={document}']
    hardlink = root / 'hardlink'
    os.link(path, hardlink)
    for destination in [path, hardlink, document]:
        journal.run([*running, f'--results={destination}'], refuses='entry-output-path')
        assert path.read_bytes() == wire
    capacity = journal.write('capacity.json', ['zkc.native-capacity/0', '65536', '4096', '8', '67108864',
        ['1000000', '100000', '4294967296'], ['67108864', '268435456']])
    journal.run([*command, f'--capacity={capacity}'], refuses='entry-input-reference-byte-limit')


def test_modes_and_templates_never_guess_or_replace_inputs(toolchain, journal, directory):
    project = directory / 'project'
    journal.run([toolchain.runtime, 'init', project])
    options = source_options(toolchain, project)
    package = directory / 'entry.zkpkg'
    built = journal.json([toolchain.runtime, 'compile', *options, f'--output={package}'])
    pinned = [f'--package={package}', f'--sha256={built["package_sha256"]}']
    for extra in [['Main'], options, ['--compiler=missing']]:
        journal.run([toolchain.runtime, 'inspect', *pinned, *extra], refuses='cli-usage')
    journal.run([toolchain.runtime, 'inspect', *pinned, '--no-simplify'], refuses='cli-option')
    journal.run([toolchain.runtime, 'inspect', f'--package={package}'], refuses='cli-usage')
    journal.run([toolchain.runtime, 'inputs', 'init', *pinned], refuses='source-output-required')
    generated = journal.json([toolchain.runtime, 'inputs', 'init', *pinned, f'--output={directory / "templates"}'])
    assert generated['files'] == [str(directory / 'templates/P.json')]
    journal.run([toolchain.runtime, 'run', *pinned, '--session=missing'], refuses='entry-input-missing')
    source = directory / 'unit.zkc'
    source.write_text('module u;protocol Unit roles(P)(u:()@P)->(){return();}run Main=Unit;')
    explicit = [f'--compiler={toolchain.compiler}', f'--module=u={source}']
    generated = journal.json([toolchain.runtime, 'inputs', 'init', *explicit, f'--output={directory / "unit"}'])
    path = Path(generated['files'][0])
    assert json.loads(path.read_text()) == {'u': None}
    journal.run([toolchain.runtime, 'run', *explicit, '--session=unit'], refuses='entry-input-missing')
    assert journal.json([toolchain.runtime, 'run', *explicit, '--session=unit', f'--input=P={path}'])['status'] == 'executed'
