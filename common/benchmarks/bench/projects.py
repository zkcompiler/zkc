"""Project closure discovery and capture shared by benchmark adapters."""
from pathlib import Path
import sys

from .io import ROOT

sys.path.insert(0, str(ROOT / 'common/tests/support'))
from project import project_inputs  # noqa: E402


def freeze_project(root, project, capture):
    manifest = root / project / 'zkc.toml'
    manifests = []
    modules, assets = project_inputs(manifest, manifests=manifests)
    files = {*manifests, *modules.values(), *(v[1] for v in assets.values())}
    for path in sorted(files):
        capture.add(path, Path('source') / path.relative_to(root))
    return capture.directory / 'source' / project / 'zkc.toml'
