"""Capture owned library packages in small protocol test adapters."""

from pathlib import Path

from project import project_inputs, project_source_format

ROOT = Path(__file__).resolve().parents[3]


def core_packages(source_format):
    """Select core manifests for the explicit source format of a test capture."""
    return [str(path.parent.relative_to(ROOT / 'libraries'))
            for path in sorted((ROOT / 'libraries/core').rglob('zkc.toml'))
            if project_source_format(path) == source_format]


def library_inputs(*packages, overrides=None):
    modules = {}
    for package in packages:
        selected, assets = project_inputs(ROOT / 'libraries' / package / 'zkc.toml')
        assert not assets, 'application assets belong to the test client'
        for name, path in selected.items():
            assert name not in modules or modules[name] == path
            modules[name] = path
    modules.update(overrides or {})
    return modules


def library_modules(*packages, overrides=None):
    modules = library_inputs(*packages, overrides=overrides)
    return [f'--module={name}={path}' for name, path in sorted(modules.items())]
