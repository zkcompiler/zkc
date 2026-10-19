"""Architecture failures use resolved providers, not canonical target guesses."""

from copy import deepcopy

import pytest

from library_architecture import violations


@pytest.fixture
def views(tmp_path):
    root = tmp_path / 'libraries'
    paths = {name: str(root / directory / 'zkc.toml') for name, directory in {
        'lower': 'core/primitives/collections', 'facade': 'core/collections',
        'client': 'protocols/polynomial/fold'}.items()}
    packages = [{'manifest': path, 'modules': {name: str(root / f'{name}.zkc')},
                 'assets': {}, 'dependencies': {}} for name, path in paths.items()]
    packages[1]['dependencies'] = {'lower': paths['lower']}
    packages[2]['dependencies'] = {'collections': paths['facade']}
    graph = {'format': 'zkc.project-graph/0', 'root': paths['client'], 'packages': packages}
    api = {'format': 'zkc.source-api/0', 'declarations': [], 'references': [{
        'owner': 'client::fold', 'source': {'module': 'client'},
        'provider': 'facade', 'provider_origin': 'captured', 'target': 'lower::fold'}]}
    return root, graph, api


def test_facade_hides_its_lower_dependency(views):
    root, graph, api = views
    assert violations(graph, api, root) == []
    api['references'][0]['provider'] = 'lower'
    assert violations(graph, api, root)[0].startswith('library-dependency:')


def test_dependency_declaration_and_layer_direction_are_independent(views):
    root, graph, api = views
    graph['packages'][2]['dependencies'].clear()
    assert violations(graph, api, root)[0].startswith('library-dependency:')
    graph['packages'][0]['dependencies'] = {'upward': graph['packages'][1]['manifest']}
    assert any(error.startswith('library-layer:') for error in violations(graph, api, root))


@pytest.mark.parametrize('kind', ['module', 'asset', 'source'])
def test_a_binding_or_source_has_one_owner(views, kind):
    root, graph, api = views
    lower, facade = graph['packages'][:2]
    if kind == 'module':
        facade['modules'].update(lower['modules'])
    elif kind == 'asset':
        lower['assets']['setup'] = {'format': 'ring-json', 'path': '/setup.json'}
        facade['assets'] = deepcopy(lower['assets'])
    else:
        facade['modules']['renamed'] = lower['modules']['lower']
    assert any(error.startswith(f'library-owner: {kind}') for error in violations(graph, api, root))


def test_public_authored_contract_growth_requires_an_explicit_boundary(views):
    root, graph, api = views
    function = {'name': 'client::fold', 'source': {'module': 'client', 'origin': 'captured'},
                'kind': 'local', 'definition': 'body', 'requirements_written': False,
                'effects_written': False}
    api['declarations'] = [function]
    assert len(violations(graph, api, root)) == 2
    function.update(requirements_written=True, effects_written=True)
    assert violations(graph, api, root) == []
    function.update(definition='primitive', requirements_written=False, effects_written=False)
    assert violations(graph, api, root) == []


def test_installed_provider_needs_no_manifest(views):
    root, graph, api = views
    api['references'][0].update(provider='zkc::prelude', provider_origin='installation')
    assert violations(graph, api, root) == []
    api['references'][0]['provider_origin'] = 'captured'
    assert violations(graph, api, root)[0].startswith('library-provider:')


@pytest.mark.parametrize('directory', ['', 'unclassified'])
def test_library_packages_cannot_bypass_layers_with_an_unknown_location(views, directory):
    root, graph, api = views
    manifest = str(root / directory / 'zkc.toml')
    graph['packages'].append({'manifest': manifest, 'modules': {}, 'assets': {},
                              'dependencies': {}})
    assert violations(graph, api, root) == [f'library-layer: unclassified package {manifest}']


def test_application_packages_are_outside_library_layer_policy(views):
    root, graph, api = views
    graph['packages'].append({'manifest': str(root.parent / 'application/zkc.toml'),
                              'modules': {}, 'assets': {}, 'dependencies': {}})
    assert violations(graph, api, root) == []
