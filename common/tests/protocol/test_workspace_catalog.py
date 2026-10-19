"""Explicit catalog selection preserves capture identity and input protection."""
from pathlib import Path
import shutil

import pytest

from project import project_arguments, project_text


def fixture(directory):
    leaf = directory / 'leaf'
    leaf.mkdir()
    (leaf / 'lib.zkc').write_text('module formula; pub math fn identity(value:bool)->bool{return value;}')
    (leaf / 'zkc.toml').write_text(project_text({
        'format': 'zkc.project/0', 'modules': {'formula': 'lib.zkc'},
        'assets': {'product': {'format': 'ring-json', 'path': 'unused.json'}}}))
    shutil.copyfile(Path(__file__).resolve().parents[3] /
                    'examples/projects/sumcheck/product/product.ring.json', leaf / 'unused.json')
    (directory / 'main.zkc').write_text('''module main; use formula::{identity};
protocol Run roles(P)(value:bool@P)->(result:bool@P){return identity(value);}
run Demo=Run;''')
    catalog = directory / 'zkc.workspace.toml'
    catalog.write_text(project_text({'format': 'zkc.workspace/0',
                                    'packages': {'chosen': 'leaf', 'unselected': 'absent'}}))
    project = directory / 'zkc.toml'
    project.write_text(project_text({'format': 'zkc.project/0', 'modules': {'main': 'main.zkc'},
                                    'workspace': {'path': catalog.name},
                                    'dependencies': {'library': {'workspace': 'chosen'}}}))
    return project, catalog


def test_catalog_path_and_explicit_inputs_share_identity_after_relocation(toolchain, journal, directory):
    original = directory / 'original'
    original.mkdir()
    project, _ = fixture(original)
    explicit = project_arguments(project)
    command = [toolchain.runtime, '--json', 'check', f'--compiler={toolchain.compiler}']
    checked = journal.json([*command, f'--project={project}', '--api'])
    graph = checked.pop('project_graph')
    checked.pop('api')
    checked.pop('project')
    assert checked == journal.json([*command, *explicit])
    root = next(p for p in graph['packages'] if p['manifest'] == str(project))
    assert root['dependencies'] == {'library': str(original / 'leaf/zkc.toml')}
    assert root['catalog_dependencies'] == {'library': {
        'catalog': str(original / 'zkc.workspace.toml'), 'package': 'chosen'}}
    compile = [toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}', 'main::Demo']
    first = journal.json([*compile, f'--project={project}', f'--output={directory}/catalog.zkpkg'])
    second = journal.json([*compile, *explicit, f'--output={directory}/explicit.zkpkg'])
    moved = directory / 'moved'
    shutil.copytree(original, moved)
    third = journal.json([*compile, f'--project={moved}/zkc.toml', f'--output={directory}/moved.zkpkg'])
    config = {'format': 'zkc.project/0', 'modules': {'main': 'main.zkc'}, 'dependencies': {'library': 'leaf'}}
    project.write_text(project_text(config))
    fourth = journal.json([*compile, f'--project={project}', f'--output={directory}/path.zkpkg'])
    assert len({r['package_sha256'] for r in (first, second, third, fourth)}) == 1


@pytest.mark.parametrize('alias', ['direct', 'symlink', 'hardlink'])
def test_used_catalog_is_a_protected_compilation_input(toolchain, journal, directory, alias):
    project, catalog = fixture(directory)
    output = catalog
    if alias != 'direct':
        output = directory / 'alias.zkpkg'
        if alias == 'symlink': output.symlink_to(catalog)
        else: output.hardlink_to(catalog)
    before = catalog.read_bytes()
    journal.json([toolchain.runtime, '--json', 'compile', f'--compiler={toolchain.compiler}',
                  f'--project={project}', f'--output={output}', 'main::Demo'], refuses='entry-output-path')
    assert catalog.read_bytes() == before


@pytest.mark.parametrize('change,code', [
    ({'packages': {'chosen': 'missing'}}, 'source-project-io'),
    ({'packages': {'other': 'leaf'}}, 'source-project-format'),
    ({'packages': {'chosen': 'leaf', 'unselected': ''}}, 'source-project-format'),
    ({'unknown': True}, 'source-project-format'),
])
def test_catalog_refusals_do_not_fall_back_to_path_discovery(toolchain, journal, directory, change, code):
    project, catalog = fixture(directory)
    catalog.write_text(project_text({'format': 'zkc.workspace/0', 'packages': {'chosen': 'leaf'}} | change))
    journal.json([toolchain.runtime, '--json', 'check', f'--compiler={toolchain.compiler}',
                  f'--project={project}'], refuses=code)
