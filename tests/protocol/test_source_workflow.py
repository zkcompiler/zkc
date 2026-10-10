"""Explicit project inputs, source-only checks and protected compilation outputs."""
import json
import os
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]


@pytest.mark.parametrize('project', sorted((ROOT / 'examples/projects').glob('*/zkc.json')),
                         ids=lambda path: path.parent.name)
def test_example_project_declarations_match_explicit_inputs(toolchain, journal, directory, project):
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}', '--declarations']
    checked = journal.json([*command, f'--project={project}'], cwd=directory)
    config = json.loads(project.read_text())
    explicit = [f'--module={name}={project.parent / path}' for name, path in config['modules'].items()]
    explicit += [f'--asset={name}={asset["format"]}={project.parent / asset["path"]}'
                 for name, asset in config['assets'].items()]
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
entry Job=Run;
''')
    project = write(directory, 'zkc.json', {'format': 'zkc.project/0', 'modules': {
        'main': source.name, 'formula': library.name,
        'zkc::vector': str(ROOT / 'libraries/zkc/vector.zkc')}, 'assets': {}})
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}', f'--project={project}']
    checked = journal.json([*command, '--declarations'])
    fold = next(d for d in checked['declarations'] if d['name'] == 'main::fold')
    assert fold['outputs'][0]['type'] == fold['inputs'][0]['type']
    assert fold['outputs'][0]['type'] != fold['inputs'][2]['type']
    assert journal.json([*command, '--entry=main::Job'])['scope'] == 'entry'
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
    diagnostic = journal.json([*command, '--entry=main::Job'],
                              refuses='source-compilation')['diagnostics']
    assert 'algebra-map-formula' in diagnostic and str(library) in diagnostic
    assert str(source) in diagnostic


def write(directory, name, value):
    path = directory / name
    path.write_text(json.dumps(value))
    return path


def source_project(directory):
    source = directory / 'main.zkc'
    source.write_text('''module main;
math fn identity<T:Type+Copy+Drop>(value:T){return value;}
protocol Run roles(P)(x:bool@P)->(out:bool@P){return identity(x);}
entry Job=Run;
''')
    project = write(directory, 'zkc.json', {'format': 'zkc.project/0',
                     'modules': {'main': 'main.zkc'}, 'assets': {}})
    return source, project


def test_source_only_check_and_selected_entry(toolchain, journal, directory):
    source, project = source_project(directory)
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}']
    report = journal.json([*command, f'--project={project}'], cwd=directory.parent)
    assert report['status'] == 'checked' and report['scope'] == 'definitions'
    explicit = journal.json([*command, f'--module=main={source}'])
    assert explicit == report
    selected = journal.json([*command, f'--project={project}', '--entry=main::Job'])
    assert selected['scope'] == 'entry'
    assert selected['capture'] == report['capture']
    assert len(selected['original']) == 64
    library = journal.json([*command, f'--project={ROOT}/libraries/zkc/zkc.json'])
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


def test_project_compilation_is_exact_and_inputs_are_protected(toolchain, journal, directory):
    source, project = source_project(directory)
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}', '--entry=main::Job']
    package = directory / 'project.entry'
    explicit = directory / 'explicit.entry'
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
    project.write_text(json.dumps(json.loads(project.read_text()) | change))
    journal.run([toolchain.runtime, 'check', f'--compiler={toolchain.compiler}', f'--project={project}'], refuses=code)


def test_project_ambiguity_duplicates_and_io_refuse(toolchain, journal, directory):
    source, project = source_project(directory)
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}']
    journal.run(command, refuses='cli-usage')
    for flags in [ ['--entry='], [f'--project={project}'], ['--no-simplify'] ]:
        journal.run([*command, f'--project={project}', *flags], refuses='cli-option')
    journal.run([toolchain.runtime, 'compile', '--declarations'], refuses='cli-option')
    journal.run([*command, f'--project={project}', f'--module=main={source}'], refuses='cli-usage')
    journal.run([*command, f'--module=main={source}', f'--module=main={source}'], refuses='source-project-duplicate')
    journal.run([*command, f'--project={directory}/missing'], refuses='source-project-io')
    for text in [
        '{"format":"zkc.project/0","modules":{"main":"main.zkc","main":"missing"},"assets":{}}',
        '{"format":"zkc.project/0","modules":{"main":"main.zkc"},"assets":{"a":{"format":"ring-json","format":"air-json","path":"missing"}}}',
        '{"format":"zkc.project/0","modules":{"main":"main.zkc"},"assets":{}} false',
    ]:
        project.write_text(text)
        journal.run([*command, f'--project={project}'], refuses='source-project-format')
    project.write_bytes(b' ' * (1024 * 1024 + 1))
    journal.run([*command, f'--project={project}'], refuses='source-project-limit')


def test_relative_project_and_module_paths_share_the_callers_directory(toolchain, journal, directory):
    source, _ = source_project(directory)
    command = [toolchain.runtime, 'check', f'--compiler={toolchain.compiler}']
    checked = journal.json([*command, '--project=zkc.json', '--entry=main::Job', '--declarations'], cwd=directory)
    assert checked['scope'] == 'entry' and checked['entry'] == 'main::Job'
    assert 'declarations' in checked and 'check' not in checked
    explicit = journal.json([*command, '--module=main=main.zkc', '--entry=main::Job', '--declarations'], cwd=directory)
    assert checked == explicit
    before = source.read_bytes()
    journal.run([toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
                 '--module=main=main.zkc', '--entry=main::Job', '--output=main.zkc'],
                cwd=directory, refuses='entry-output-path')
    assert source.read_bytes() == before


def test_project_paths_use_the_visible_parent_and_do_not_enter_identity(toolchain, journal, directory):
    original = directory / 'original'
    original.mkdir()
    source, project = source_project(original)
    relocated = directory / 'relocated'
    relocated.mkdir()
    (relocated / 'main.zkc').write_bytes(source.read_bytes())
    link = relocated / 'zkc.json'
    link.symlink_to(project)
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}', '--entry=main::Job']
    pins = []
    for i, manifest in enumerate((project, link)):
        report = journal.json([*command, f'--project={manifest}', f'--output={directory}/{i}.entry'])
        pins.append(report['package_sha256'])
    assert pins[0] == pins[1]
    # A symlinked manifest still names inputs relative to its visible parent.
    (relocated / 'main.zkc').write_text('module wrong;')
    journal.run([*command, f'--project={link}', f'--output={directory}/bad.entry'], refuses='source-compilation')


def test_project_assets_are_captured_and_protected(toolchain, journal, directory):
    _, project = source_project(directory)
    asset = directory / 'product.ring.json'
    asset.write_bytes((ROOT / 'examples/projects/expression-sumcheck/product.ring.json').read_bytes())
    config = json.loads(project.read_text())
    config['assets'] = {'product': {'format': 'ring-json', 'path': asset.name}}
    project.write_text(json.dumps(config))
    command = [toolchain.runtime, 'compile', f'--compiler={toolchain.compiler}',
               '--entry=main::Job', f'--project={project}']
    journal.run([*command, f'--output={directory}/with-asset.entry'])
    before = asset.read_bytes()
    journal.run([*command, f'--output={asset}'], refuses='entry-output-path')
    assert asset.read_bytes() == before
    config['assets']['product']['format'] = 'air-json'
    project.write_text(json.dumps(config))
    journal.run([*command, f'--output={directory}/wrong.entry'], refuses='source-compilation')


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
