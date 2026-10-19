"""Check library boundaries against compiler references and manifest ownership.

Manifests own modules and assets. The compiler owns name resolution and contract
completion. This checker compares their diagnostic views without re-parsing zkc
or inventing a second module registry.
"""

from collections import defaultdict
from pathlib import Path


def layer(manifest, library_root):
    """The physical hierarchy expresses the permitted dependency direction."""
    try:
        parts = Path(manifest).relative_to(library_root).parts
    except ValueError:
        return None
    if parts[:2] == ('core', 'primitives'):
        return 0
    if parts[:2] == ('core', 'traversal'):
        return 1
    return {'core': 2, 'protocols': 3, 'relations': 3, 'commitments': 3,
            'arguments': 4, 'constructions': 5}.get(parts[0])


def violations(project_graph, api, library_root, *, contracts=True):
    """Return sorted, named diagnostics; a facade's provider owns the dependency.

    This is a maintained-library policy check, not source admission or a native
    security check. Explicit SDK captures do not require a package graph.
    """
    assert project_graph['format'] == 'zkc.project-graph/0'
    assert api['format'] == 'zkc.source-api/0'
    library_root = Path(library_root).resolve()
    packages = {item['manifest']: item for item in project_graph['packages']}
    owners, assets, paths = defaultdict(set), defaultdict(set), defaultdict(set)
    errors = set()
    for manifest, package in packages.items():
        for module, path in package['modules'].items():
            owners[module].add(manifest)
            paths[Path(path).resolve()].add(manifest)
        for asset, value in package['assets'].items():
            assets[asset].add(manifest)
            paths[Path(value['path']).resolve()].add(manifest)
        source_layer = layer(manifest, library_root)
        if source_layer is None and Path(manifest).is_relative_to(library_root):
            errors.add(f'library-layer: unclassified package {manifest}')
        for dependency in package['dependencies'].values():
            target_layer = layer(dependency, library_root)
            if source_layer is not None and (target_layer is None or target_layer > source_layer):
                errors.add(f'library-layer: {manifest} -> {dependency}')
    for kind, bindings in [('module', owners), ('asset', assets), ('source', paths)]:
        for name, bindings_owners in bindings.items():
            if len(bindings_owners) != 1:
                errors.add(f'library-owner: {kind} {name}: {", ".join(sorted(bindings_owners))}')
    for reference in api['references']:
        if reference['provider_origin'] == 'installation':
            continue
        module = reference['source']['module']
        provider = reference['provider']
        if module not in owners or provider not in owners:
            errors.add(f'library-provider: {module} -> {provider}')
            continue
        for owner in owners[module]:
            allowed = {owner, *packages[owner]['dependencies'].values()}
            if not owners[provider] <= allowed:
                errors.add(f'library-dependency: {module} -> {provider} at {owner}')
    if contracts:
        for declaration in api['declarations']:
            source = declaration['source']
            if source['origin'] != 'captured':
                continue
            # Applications may infer their own contracts. Reusable library
            # bodies freeze them; native bindings retain catalog authority.
            if not any(layer(owner, library_root) is not None for owner in owners[source['module']]):
                continue
            if declaration.get('definition') != 'body':
                continue
            kind = declaration['kind']
            if kind in ('math', 'local', 'protocol', 'domain'):
                if not declaration['requirements_written']:
                    errors.add(f'library-contract: {declaration["name"]}: missing where clause')
                if kind == 'local' and not declaration['effects_written']:
                    errors.add(f'library-contract: {declaration["name"]}: missing effects clause')
    return sorted(errors)
