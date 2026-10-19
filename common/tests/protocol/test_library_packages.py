"""Every reusable package checks independently and owns its source exactly once."""
import tomllib

import pytest

from library_architecture import violations
from toolchain import ROOT

LIBRARIES = ROOT / 'libraries'
MANIFESTS = sorted(LIBRARIES.rglob('zkc.toml'))
EXAMPLES = sorted((ROOT / 'examples/projects').rglob('zkc.toml'))


@pytest.mark.parametrize('manifest', MANIFESTS + EXAMPLES,
                         ids=lambda path: str(path.relative_to(ROOT)))
def test_manifest_closure_obeys_library_boundaries(toolchain, journal, manifest):
    report = journal.json([toolchain.runtime, '--json', 'check', '--api',
                           f'--compiler={toolchain.compiler}', f'--project={manifest}'])
    assert violations(report['project_graph'], report['api'], LIBRARIES) == []


def test_library_sources_have_exactly_one_manifest_owner():
    owners, modules, assets, asset_paths = {}, {}, {}, {}
    for manifest in MANIFESTS:
        value = tomllib.loads(manifest.read_text())
        for name, source in value['modules'].items():
            assert name not in modules, f'library-owner: module {name}'
            modules[name] = manifest
            path = (manifest.parent / source).resolve()
            assert path not in owners, f'library-owner: {path}: {owners.get(path)}, {manifest}'
            owners[path] = manifest
        for name, asset in value.get('assets', {}).items():
            assert name not in assets, f'library-owner: asset {name}'
            assets[name] = manifest
            path = (manifest.parent / asset['path']).resolve()
            assert path not in owners, f'library-owner: source {path}'
            assert path not in asset_paths, f'library-owner: asset {path}'
            asset_paths[path] = manifest
    assert set(owners) == set(LIBRARIES.rglob('*.zkc'))
    assert all(path.is_relative_to(LIBRARIES) for path in owners)
    assert all(path.is_relative_to(LIBRARIES) for path in asset_paths)


def test_facade_interface_calls_follow_the_authored_binder(toolchain, journal, directory):
    root = directory / 'libraries'
    lower = root / 'core/primitives/algebra'
    facade = root / 'core/algebra'
    client = root / 'protocols/example'
    for package in (lower, facade, client):
        package.mkdir(parents=True)
    (lower / 'lib.zkc').write_text('''module lower;
      pub interface Contract {math fn value()->bool;}
    ''')
    (lower / 'zkc.toml').write_text('''format="zkc.project/0"
      [modules]
      lower="lib.zkc"
    ''')
    (facade / 'lib.zkc').write_text('module facade;pub use lower::{Contract};')
    (facade / 'zkc.toml').write_text('''format="zkc.project/0"
      [modules]
      facade="lib.zkc"
      [dependencies]
      lower="../primitives/algebra"
    ''')
    source = client / 'lib.zkc'
    source.write_text('''module client;
      use facade as api;
      use facade::{Contract};
      pub math fn aliased<C:api::Contract>()->bool where () {return C::value();}
      pub math fn imported<C:Contract>()->bool where () {return C::value();}
      pub module Generic<C:api::Contract> {
        pub math fn inherited()->bool where () {return C::value();}
      }
    ''')
    manifest = client / 'zkc.toml'
    manifest.write_text('''format="zkc.project/0"
      [modules]
      client="lib.zkc"
      [dependencies]
      facade="../../core/algebra"
    ''')
    command = [toolchain.runtime, '--json', 'check', '--api',
               f'--compiler={toolchain.compiler}', f'--project={manifest}']
    report = journal.json(command)
    calls = [item for item in report['api']['references']
             if item.get('abstract_module') and item['source']['module'] == 'client']
    assert len(calls) == 3
    assert all(item['provider'] == 'facade' and item['target_module'] == 'lower'
               for item in calls)
    assert violations(report['project_graph'], report['api'], root) == []
    source.write_text(source.read_text().replace('C:api::Contract', 'C:lower::Contract'))
    report = journal.json(command)
    errors = violations(report['project_graph'], report['api'], root)
    assert errors == [f'library-dependency: client -> lower at {manifest}']
