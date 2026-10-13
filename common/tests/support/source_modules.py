"""Capture maintained library families in small protocol test adapters."""

from pathlib import Path

from project import project_inputs

ROOT = Path(__file__).resolve().parents[3]


def library_modules(*families, overrides=None):
    modules = {}
    for family in families:
        selected, assets = project_inputs(ROOT / 'libraries' / family / 'zkc.toml')
        assert not assets, 'application assets belong to the test client'
        for name, path in selected.items():
            assert name not in modules or modules[name] == path
            modules[name] = path
    modules.update(overrides or {})
    return [f'--module={name}={path}' for name, path in sorted(modules.items())]
