#!/usr/bin/env python3
"""Resolve every maintained package and compiler source fixture for one test.

The output maps each package manifest under libraries/ and examples/projects/
to its source format, modules and assets, and lists every compiler `.zkc`
fixture. Source bytes remain runtime inputs.
"""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'common/tests/support'))
from project import project_inputs, project_source_format  # noqa: E402

packages = {}
for base in ('libraries', 'examples/projects'):
    for manifest in sorted((ROOT / base).rglob('zkc.toml')):
        modules, assets = project_inputs(manifest)
        packages[str(manifest.relative_to(ROOT))] = {
            'format': project_source_format(manifest),
            'modules': {name: str(path) for name, path in sorted(modules.items())},
            'assets': {name: [kind, str(path)]
                       for name, (kind, path) in sorted(assets.items())},
        }
fixtures = sorted(str(path) for path in (ROOT / 'compiler/test/fixtures').rglob('*.zkc'))
Path(sys.argv[1]).write_text(json.dumps({'packages': packages, 'fixtures': fixtures}))
