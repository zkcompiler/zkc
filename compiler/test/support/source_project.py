#!/usr/bin/env python3
"""Resolve a trusted maintained fixture through its owning project manifest."""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'common/tests/support'))
from project import project_inputs  # noqa: E402

modules, _ = project_inputs(sys.argv[1])
Path(sys.argv[2]).write_text(json.dumps(dict(sorted((name, str(path))
                                                  for name, path in modules.items()))))
