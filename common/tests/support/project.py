"""Write small authored project fixtures without a second TOML dependency."""
import json
from pathlib import Path
import shutil
import tomllib


def project_text(value):
    """Render string/bool/count values and nested tables used by schema controls."""
    lines = []

    def table(mapping, prefix=()):
        for name, item in mapping.items():
            if not isinstance(item, dict):
                lines.append(f'{json.dumps(name)} = {json.dumps(item)}')
        for name, item in mapping.items():
            if isinstance(item, dict):
                path = (*prefix, name)
                lines.extend(['', '[' + '.'.join(json.dumps(part) for part in path) + ']'])
                table(item, path)
    table(value)
    return '\n'.join(lines) + '\n'


def project_inputs(path, *, manifests=None):
    """Expand known-good test projects for comparison with explicit SDK inputs.

    Production admission and refusal cases belong to the Rust loader. This
    helper does not load untrusted manifests or reproduce those checks.
    """
    modules, assets, seen, catalogs = {}, {}, set(), set()

    def visit(path):
        path = Path(path)
        context = path.parent.resolve() / path.name
        if context in seen:
            return
        seen.add(context)
        if manifests is not None:
            manifests.append(context)
        config = tomllib.loads(path.read_text())
        for name, source in config.get('modules', {}).items():
            source = (path.parent / source).resolve()
            assert name not in modules or modules[name] == source
            modules[name] = source
        for name, asset in config.get('assets', {}).items():
            value = (asset['format'], (path.parent / asset['path']).resolve())
            assert name not in assets or assets[name] == value
            assets[name] = value
        for dependency in config.get('dependencies', {}).values():
            if isinstance(dependency, str):
                visit(path.parent / dependency / 'zkc.toml')
            else:
                catalog = path.parent / config['workspace']['path']
                catalog = catalog.parent.resolve() / catalog.name
                if manifests is not None and catalog not in catalogs:
                    manifests.append(catalog)
                catalogs.add(catalog)
                locations = tomllib.loads(catalog.read_text())['packages']
                selected = catalog.parent / locations[dependency['workspace']]
                visit(selected / 'zkc.toml' if selected.is_dir() else selected)
    visit(path)
    return modules, assets


def project_arguments(path):
    modules, assets = project_inputs(path)
    return ([f'--module={name}={source}' for name, source in sorted(modules.items())]
            + [f'--asset={name}={kind}={source}'
               for name, (kind, source) in sorted(assets.items())])


def copy_project(path, directory, *, manifest='zkc.toml'):
    """Copy a trusted manifest closure into an independent consumer directory.

    The consumer has explicit inputs, with no paths back to the checkout.
    Logical module and asset names remain unchanged. Ownership policy uses the
    original manifests; this flattened capture tests the installed tools.
    """
    directory = Path(directory)
    modules, assets = project_inputs(path)
    copied_modules, copied_assets = {}, {}
    for index, (name, source) in enumerate(sorted(modules.items())):
        target = f'module-{index:03}.zkc'
        shutil.copyfile(source, directory / target)
        copied_modules[name] = target
    for index, (name, (kind, source)) in enumerate(sorted(assets.items())):
        target = f'asset-{index:03}{source.suffix}'
        shutil.copyfile(source, directory / target)
        copied_assets[name] = {'format': kind, 'path': target}
    target = directory / manifest
    target.write_text(project_text({'format': 'zkc.project/0', 'modules': copied_modules,
                                    'assets': copied_assets}))
    return target
