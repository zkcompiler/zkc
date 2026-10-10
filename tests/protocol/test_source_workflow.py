"""Explicit project inputs, source-only checks and protected compilation outputs."""
import json
import os
from pathlib import Path
import sys
import tomllib

from project import project_text

import pytest

ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.parametrize('project', sorted((ROOT / 'examples/projects').glob('*/zkc.toml')),
                         ids=lambda path: path.parent.name)
def test_example_project_declarations_match_explicit_inputs(toolchain, journal, directory, project):
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}', '--declarations']
    checked = journal.json([*command, f'--project={project}'], cwd=directory)
    config = tomllib.loads(project.read_text())
    explicit = [f'--module={name}={project.parent / path}' for name, path in config['modules'].items()]
    explicit += [f'--asset={name}={asset["format"]}={project.parent / asset["path"]}'
                 for name, asset in config.get('assets', {}).items()]
    assert checked.pop("project") == str(project)
    assert checked == journal.json([*command, *explicit], cwd=directory)
    assert checked['scope'] == 'definitions'


def test_mapped_library_inference_and_admission_scopes(toolchain, journal, directory):
    library = directory / 'formula.zkc'
    library.write_text('''module formula;
pub math fn affine<F:Field>(low:F,high:F,r:F)->F{return low+(high-low)*r;}
''')
    source = directory / 'main.zkc'
    source.write_text('''module main;
use zkc::vector::{Vector};
domain F=field("koala-bear");
pub fn fold<T:Field>(a:Vector<T>,b:Vector<T>,r:T) {
  return map formula::affine(each a,each b,r);
}
protocol Run roles(P)(a:Vector<F>@P,b:Vector<F>@P,r:F@P)->(out:Vector<F>@P){
  return fold(a,b,r);
}
run Job=Run;
''')
    project = write(directory, 'zkc.toml', {'format': 'zkc.project/0', 'modules': {
        'main': source.name, 'formula': library.name,
        'zkc::vector': str(ROOT / 'libraries/zkc/vector.zkc')}, 'assets': {}})
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}', f'--project={project}']
    checked = journal.json([*command, '--declarations'])
    fold = next(d for d in checked['declarations'] if d['name'] == 'main::fold')
    assert fold['outputs'][0]['type'] == fold['inputs'][0]['type']
    assert fold['outputs'][0]['type'] != fold['inputs'][2]['type']
    assert journal.json([*command, 'main::Job'])['scope'] == 'entry'
    # Ordinary generic inference retains the helper's diagnostic origin under map.
    library.write_text('''module formula;
domain E=field("koala-bear.ext8-binomial3");
pub math fn affine<F:Field>(low:F,high:F,r:E)->F{return low;}
''')
    diagnostic = journal.json(command, refuses='source-compilation')['diagnostics']
    assert 'source.type' in diagnostic and str(library) in diagnostic
    # Full helper vocabulary admission belongs to the concrete mathematical IR.
    # Dead unsupported operations must still be refused before simplification.
    library.write_text('''module formula;
pub math fn affine<F:Field>(low:F,high:F,r:F)->F{let unused=low==high;return low;}
''')
    assert journal.json(command)['scope'] == 'definitions'
    diagnostic = journal.json([*command, 'main::Job'],
                              refuses='source-compilation')['diagnostics']
    assert 'algebra-map-formula' in diagnostic and str(library) in diagnostic
    assert str(source) in diagnostic
    assert '\\0A' not in diagnostic
    assert '\nrelated source declaration: formula::affine\n' in diagnostic


def write(directory, name, value):
    path = directory / name
    path.write_text(project_text(value))
    return path


def source_project(directory):
    source = directory / 'main.zkc'
    source.write_text('''module main;
math fn identity<T:Type+Copy+Drop>(value:T){return value;}
protocol Run roles(P)(x:bool@P)->(out:bool@P){return identity(x);}
run Job=Run;
''')
    project = write(directory, 'zkc.toml', {'format': 'zkc.project/0',
                     'modules': {'main': 'main.zkc'}, 'assets': {}})
    return source, project


def test_source_only_check_and_selected_entry(toolchain, journal, directory):
    source, project = source_project(directory)
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}']
    report = journal.json([*command, f'--project={project}'], cwd=directory.parent)
    assert report['status'] == 'checked' and report['scope'] == 'definitions'
    explicit = journal.json([*command, f'--module=main={source}'])
    assert report.pop("project") == str(project)
    assert explicit == report
    selected = journal.json([*command, f'--project={project}', 'main::Job'])
    assert selected['scope'] == 'entry'
    assert selected['capture'] == report['capture']
    assert len(selected['original']) == 64
    library = journal.json([*command, f'--project={ROOT}/libraries/zkc/zkc.toml'])
    assert library['scope'] == 'definitions'
    source.write_text(source.read_text() + '\nfn unused()->bool{return 3;}\n')
    failed = journal.json([*command, f'--project={project}'], refuses='source-compilation')
    assert 'source.type' in failed['diagnostics']


def test_check_requires_a_successful_compiler_report(toolchain, journal, directory):
    _, project = source_project(directory)
    compiler = directory / 'compiler'
    for text in ['not JSON', '{}', '{"format":"zkc.source-check/0","status":"refused"}',
                 '{"format":"zkc.source-check/0","status":"checked","scope":"entry"}']:
        compiler.write_text(f'#!{sys.executable}\nprint({text!r})\n')
        compiler.chmod(0o755)
        journal.run([toolchain.runtime, 'check', f'--compiler={compiler}',
                     f'--project={project}'], refuses='source-check-format')


def test_check_validates_the_compilers_selection_report(toolchain, journal, directory):
    _, project = source_project(directory)
    compiler = directory / 'compiler'
    job = {'name': 'main::Job', 'kind': 'run'}
    alias = {'name': 'main::Alias', 'kind': 'proof'}
    baseline = {'format': 'zkc.source-check/0', 'status': 'checked', 'scope': 'definitions'}
    controls = [
        ({}, None),
        ({'entries': [job, alias]}, None),
        ({'entries': [job, job]}, None),
        ({'entries': [job | {'extra': True}]}, None),
        ({'entries': [job | {'kind': 'unknown'}]}, None),
        ({'entries': [job | {'name': 'Job'}]}, None),
        ({'entries': [job], 'entry': 'main::Job'}, None),
        ({'entries': [alias, job], 'entry': 'main::Alias', 'scope': 'entry'}, 'Job'),
        ({'entries': [job, {'name': 'other::Job', 'kind': 'run'}],
          'entry': 'main::Job', 'scope': 'entry'}, 'Job'),
    ]
    for fields, selector in controls:
        text = json.dumps(baseline | fields)
        compiler.write_text(f'#!{sys.executable}\nprint({text!r})\n')
        compiler.chmod(0o755)
        journal.run([toolchain.runtime, 'check', f'--compiler={compiler}',
                     f'--project={project}', *([selector] if selector else [])],
                    refuses='source-check-format')


def test_check_inventory_reports_explicit_proof_kind(toolchain, journal, directory):
    source, _ = source_project(directory)
    source.write_text(source.read_text() + '''
protocol Verify roles(P,V)(ok:bool@V)->(ok:bool@V){return ok;}
proof Proof=Verify{prover P;verifier V;public{ok};accept ok;construction authored;}
''')
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}']
    report = journal.json(command, cwd=directory)
    assert report['entries'] == [{'name': 'main::Job', 'kind': 'run'},
                                 {'name': 'main::Proof', 'kind': 'proof'}]
    assert journal.json([*command, 'Proof'], cwd=directory)['entry'] == 'main::Proof'


def test_project_compilation_is_exact_and_inputs_are_protected(toolchain, journal, directory):
    source, project = source_project(directory)
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}', 'main::Job']
    package = directory / 'project.zkpkg'
    explicit = directory / 'explicit.zkpkg'
    first = journal.json([*command, f'--project={project}', f'--output={package}'])
    second = journal.json([*command, f'--module=main={source}', f'--output={explicit}'])
    assert first['package_sha256'] == second['package_sha256']
    assert package.read_bytes() == explicit.read_bytes()
    for path in (project, source):
        before = path.read_bytes()
        journal.run([*command, f'--project={project}', f'--output={path}'], refuses='entry-output-path')
        assert path.read_bytes() == before
    alias = directory / 'alias.json'
    os.link(project, alias)
    journal.run([*command, f'--project={project}', f'--output={alias}'], refuses='entry-output-path')


@pytest.mark.parametrize('change,code', [
    ({'format': 'zkc.unknown/0'}, 'source-project-format'),
    ({'extra': True}, 'source-project-format'),
    ({'modules': {}}, 'source-project-format'),
    ({'modules': {'main': ''}}, 'source-project-format'),
    ({'modules': {'main=other': 'main.zkc'}}, 'source-project-format'),
    ({'assets': {'a': {'format': 'guess', 'path': 'missing'}}}, 'source-project-format'),
    ({'assets': {'a': {'format': 'ring-json', 'path': 'missing', 'extra': 0}}}, 'source-project-format'),
    ({'modules': {f'm{i}': 'main.zkc' for i in range(257)}}, 'source-project-limit'),
])
def test_project_schema_refuses(toolchain, journal, directory, change, code):
    _, project = source_project(directory)
    project.write_text(project_text(tomllib.loads(project.read_text()) | change))
    journal.run([toolchain.runtime, 'check', f'--compiler={toolchain.compiler}', f'--project={project}'], refuses=code)


def test_project_ambiguity_duplicates_and_io_refuse(toolchain, journal, directory):
    source, project = source_project(directory)
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}']
    journal.run(command, cwd=directory.parent, refuses='source-project-missing')
    for flags in [ ['--entry='], [f'--project={project}'], ['--no-simplify'] ]:
        journal.run([*command, f'--project={project}', *flags], refuses='cli-option')
    journal.run([toolchain.runtime, 'compile', '--declarations'], refuses='cli-option')
    journal.run([*command, f'--project={project}', f'--module=main={source}'], refuses='cli-usage')
    journal.run([*command, f'--module=main={source}', f'--module=main={source}'], refuses='source-project-duplicate')
    journal.run([*command, f'--project={directory}/missing'], refuses='source-project-io')
    for text in [
        'format="zkc.project/0"\n[modules]\nmain="main.zkc"\nmain="missing"',
        'format="zkc.project/0"\n[modules]\nmain="main.zkc"\n[assets.a]\nformat="ring-json"\nformat="air-json"\npath="missing"',
        'format="zkc.project/0"\n[modules]\nmain="main.zkc"\nfalse',
        '{"format":"zkc.project/0","modules":{"main":"main.zkc"}}',
    ]:
        project.write_text(text)
        journal.run([*command, f'--project={project}'], refuses='source-project-format')
    project.write_bytes(b' ' * (1024 * 1024 + 1))
    journal.run([*command, f'--project={project}'], refuses='source-project-limit')


def test_relative_project_and_module_paths_share_the_callers_directory(toolchain, journal, directory):
    source, _ = source_project(directory)
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}']
    checked = journal.json([*command, '--project=zkc.toml', 'main::Job', '--declarations'], cwd=directory)
    assert checked['scope'] == 'entry' and checked['entry'] == 'main::Job'
    assert 'declarations' in checked and 'check' not in checked
    explicit = journal.json([*command, '--module=main=main.zkc', 'main::Job', '--declarations'], cwd=directory)
    assert checked.pop("project") == "zkc.toml"
    assert checked == explicit
    before = source.read_bytes()
    journal.run([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                 '--module=main=main.zkc', 'main::Job', '--output=main.zkc'],
                cwd=directory, refuses='entry-output-path')
    assert source.read_bytes() == before


def test_project_paths_use_the_visible_parent_and_do_not_enter_identity(toolchain, journal, directory):
    original = directory / 'original'
    original.mkdir()
    source, project = source_project(original)
    relocated = directory / 'relocated'
    relocated.mkdir()
    (relocated / 'main.zkc').write_bytes(source.read_bytes())
    link = relocated / 'zkc.toml'
    link.symlink_to(project)
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}', 'main::Job']
    pins = []
    for i, manifest in enumerate((project, link)):
        report = journal.json([*command, f'--project={manifest}', f'--output={directory}/{i}.zkpkg'])
        pins.append(report['package_sha256'])
    assert pins[0] == pins[1]
    # A symlinked manifest still names inputs relative to its visible parent.
    (relocated / 'main.zkc').write_text('module wrong;')
    journal.run([*command, f'--project={link}', f'--output={directory}/bad.zkpkg'], refuses='source-compilation')


def test_project_assets_are_captured_and_protected(toolchain, journal, directory):
    _, project = source_project(directory)
    asset = directory / 'product.ring.json'
    asset.write_bytes((ROOT / 'examples/projects/expression-sumcheck/product.ring.json').read_bytes())
    config = tomllib.loads(project.read_text())
    config['assets'] = {'product': {'format': 'ring-json', 'path': asset.name}}
    project.write_text(project_text(config))
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
               'main::Job', f'--project={project}']
    journal.run([*command, f'--output={directory}/with-asset.zkpkg'])
    before = asset.read_bytes()
    journal.run([*command, f'--output={asset}'], refuses='entry-output-path')
    assert asset.read_bytes() == before
    config['assets']['product']['format'] = 'air-json'
    project.write_text(project_text(config))
    journal.run([*command, f'--output={directory}/wrong.zkpkg'], refuses='source-compilation')


def test_completed_declarations_and_actionable_inference_errors(toolchain, journal, directory):
    library = directory / 'library.zkc'
    library.write_text('''module library;
pub math fn zero<F:Field>()->F{return 0;}
pub fn identity(value:bool)->bool{return value;}
''')
    source = directory / 'main.zkc'
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}',
               f'--module=library={library}', f'--module=main={source}']
    source.write_text('''module main;
use library::{zero};
pub fn work()->bool {let unresolved = zero(); return true;}
''')
    report = journal.json(command, refuses='source-compilation')
    assert "cannot infer static argument 'F'" in report['diagnostics']
    assert 'library::zero' in report['diagnostics']
    assert 'note: related source' in report['diagnostics']
    assert f'{library}:2:' in report['diagnostics']
    source.write_text('''module main;
use library::{identity};
domain F=field("bls12-381.fr");
pub fn work(value:F)->bool {return identity(value);}
''')
    report = journal.json(command, refuses='source-compilation')
    assert 'type conflict:' in report['diagnostics'] and 'bool' in report['diagnostics']
    assert f'{library}:3:' in report['diagnostics']
    source.write_text('''module main;
use library::{identity};
pub protocol Run roles(P,V)(x:bool@(P,V))->(out:bool@V){
 let unresolved = identity(x);
 return x;
}
''')
    report = journal.json(command, refuses='source-compilation')
    assert 'ambiguous participant (P, V)' in report['diagnostics'] and '@Role' in report['diagnostics']
    source.write_text(source.read_text().replace('unresolved =', 'unresolved @P ='))
    checked = journal.json([*command, '--declarations'])
    declarations = checked['declarations']
    assert [d['name'] for d in declarations] == ['library::identity', 'library::zero', 'main::Run']
    assert declarations[-1]['roles'] == ['P', 'V']
    assert declarations[1]['outputs'][0]['type'] == 'F'
    assert declarations[1]['parameters'][0]['sort'] == 'Field'
    assert declarations[0]['effects'] == {'opaque': False, 'stop': False}
    compact = journal.json(command)
    assert 'declarations' not in compact
    source.write_text('module main; fn bad<T:Type+Copy+Drop>(x:T)->bool{return x;}')
    diagnostic = journal.json(command, refuses='source-compilation')['diagnostics']
    assert 'parameter:' not in diagnostic
    assert 'T versus bool' in diagnostic or 'bool versus T' in diagnostic


def test_discovery_selection_and_default_output(toolchain, journal, directory):
    source, project = source_project(directory)
    child = directory / 'nested'
    child.mkdir()
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}']
    definitions = journal.json(command, cwd=child)
    assert definitions['project'] == str(project)
    assert definitions['scope'] == 'definitions'
    assert definitions['entries'] == [{'name': 'main::Job', 'kind': 'run'}]
    selected = journal.json([*command, 'Job'], cwd=child)
    assert selected['entry'] == 'main::Job' and selected['scope'] == 'entry'
    compile = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}']
    outputs = []
    for selector in ([], ['Job'], ['main::Job']):
        report = journal.json([*compile, *selector], cwd=child)
        assert report['entry'] == 'main::Job'
        assert report['output'] == str(directory / 'build/zkc/main.Job.zkpkg')
        outputs.append(report['package_sha256'])
    assert len(set(outputs)) == 1
    # Adding a library preserves selection; adding a named alias requires a choice.
    library = directory / 'library.zkc'
    library.write_text('module library; pub math fn same(x:bool)->bool{return x;}')
    config = tomllib.loads(project.read_text())
    config['modules']['library'] = library.name
    project.write_text(project_text(config))
    assert journal.json(compile, cwd=child)['entry'] == 'main::Job'
    source.write_text(source.read_text() + '\nrun Alias=Job;')
    refused = journal.json(compile, cwd=child, refuses='source-compilation')
    assert 'source.entry' in refused['diagnostics']
    assert 'main::Alias (run)' in refused['diagnostics'] and 'main::Job (run)' in refused['diagnostics']
    assert journal.json([*compile, 'Job'], cwd=child)['entry'] == 'main::Job'
    # Another module's same short name is ambiguous, never preferred by location.
    library.write_text('module library; protocol Run roles(P)()->(){return();}run Job=Run;')
    refused = journal.json([*command, 'Job'], cwd=child, refuses='source-compilation')
    assert 'library::Job (run)' in refused['diagnostics']
    assert journal.json([*command, 'main::Job'], cwd=child)['entry'] == 'main::Job'
    journal.run([*command, 'main::Run'], cwd=child, refuses='source-compilation')
    # Explicit input mode never discovers the surrounding manifest.
    journal.run([*compile, f'--module=main={source}'], cwd=child, refuses='source-output-required')
    report = journal.json([*command, f'--module=main={source}'], cwd=child)
    assert 'project' not in report and len(report['entries']) == 2


@pytest.mark.parametrize('kind', ['invalid', 'dangling', 'directory', 'fifo', 'unreadable'])
def test_discovery_never_skips_a_broken_nearer_manifest(toolchain, journal, directory, kind):
    _, parent = source_project(directory)
    child = directory / 'child'
    child.mkdir()
    path = child / 'zkc.toml'
    if kind == 'invalid': path.write_text('invalid TOML')
    elif kind == 'dangling': path.symlink_to('absent')
    elif kind == 'directory': path.mkdir()
    elif kind == 'unreadable':
        path.write_text(parent.read_text())
        path.chmod(0)
    else: os.mkfifo(path)
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}']
    journal.run(command, cwd=child, refuses='source-project-format' if kind == 'invalid' else 'source-project-io')
    assert journal.json([*command, f'--project={parent}'], cwd=child)['scope'] == 'definitions'


def test_default_output_protection_and_name_collision(toolchain, journal, directory):
    source, project = source_project(directory)
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}']
    report = journal.json(command, cwd=directory)
    output = Path(report['output'])
    output.unlink()
    for target, symlink in [(source, True), (project, False), (Path(toolchain.compiler), True)]:
        before = target.read_bytes()
        if symlink: output.symlink_to(target)
        else: os.link(target, output)
        journal.run(command, cwd=directory, refuses='entry-output-path')
        assert target.read_bytes() == before
        output.unlink()
    # Case-folded collisions refuse even on a case-sensitive filesystem.
    source.write_text(source.read_text() + '\nrun job=Job;')
    journal.run([*command, 'Job'], cwd=directory)
    original = output.read_bytes()
    journal.run([*command, 'job'], cwd=directory, refuses='source-output-collision')
    assert output.read_bytes() == original
    # An explicit distinct filename resolves the collision.
    assert journal.json([*command, 'job', '--output=alias.zkpkg'],
                        cwd=directory)['entry'] == 'main::job'


def test_toml_comments_order_and_omitted_assets_preserve_capture(toolchain, journal, directory):
    _, project = source_project(directory)
    (directory / 'lib.zkc').write_text('module lib;')
    config = tomllib.loads(project.read_text())
    config['modules']['lib'] = 'lib.zkc'
    project.write_text(project_text(config))
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}']
    first = journal.json(command, cwd=directory)
    project.write_text('# The module map is authored.\nformat="zkc.project/0"\n\n'
                      '[modules]\nlib="lib.zkc"\nmain="./main.zkc"\n')
    second = journal.json(command, cwd=directory)
    assert first['package_sha256'] == second['package_sha256']


@pytest.mark.parametrize('module,entry', [('CON', 'Job'), ('m' * 125, 'E' * 125)])
def test_default_output_requires_a_portable_filename(toolchain, journal, directory, module, entry):
    source, project = source_project(directory)
    source.write_text(source.read_text().replace('module main;', f'module {module};')
                      .replace('run Job=', f'run {entry}='))
    project.write_text(project_text({'format': 'zkc.project/0', 'modules': {module: source.name}}))
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}']
    journal.run(command, cwd=directory, refuses='source-output-name')
    assert journal.json([*command, '--output=short.zkpkg'], cwd=directory)['entry'] == f'{module}::{entry}'


def test_default_output_directory_and_regeneration(toolchain, journal, directory):
    source_project(directory)
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}']
    build = directory / 'build'
    build.write_text('ordinary file')
    journal.run(command, cwd=directory, refuses='source-output-directory')
    assert build.read_text() == 'ordinary file'
    build.unlink()
    output = build / 'zkc/main.Job.zkpkg'
    output.parent.mkdir(parents=True)
    output.write_text('not a package')
    report = journal.json(command, cwd=directory)
    assert report['entry'] == 'main::Job' and output.stat().st_size > 100
    output.write_bytes(b'')
    assert journal.json(command, cwd=directory)['package_sha256'] == report['package_sha256']
    journal.run([*command, ''], cwd=directory, refuses='source-entry-selection')


def test_default_output_uses_the_entire_module_name(toolchain, journal, directory):
    source, project = source_project(directory)
    source.write_text(source.read_text().replace('module main;', 'module zkc::sample;'))
    project.write_text(project_text({'format': 'zkc.project/0',
                                    'modules': {'zkc::sample': source.name}}))
    report = journal.json([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}'],
                          cwd=directory)
    assert Path(report['output']).name == 'zkc.sample.Job.zkpkg'
