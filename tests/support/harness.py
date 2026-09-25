"""Controlled scripts and executable fixtures for tests of the test harness."""

import importlib.util
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def executable(path):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("#!/bin/sh\nexit 0\n")
    path.chmod(0o755)
    return path


def fake_command(directory, name):
    path = directory / name
    path.write_text(f'''#!{sys.executable}
import json, os, sys
from pathlib import Path
with Path(os.environ["COMMAND_RECORD"]).open("a") as stream:
    stream.write(json.dumps({{"command": Path(sys.argv[0]).name,
        "arguments": sys.argv[1:], "cwd": os.getcwd(),
        "jobs": os.environ.get("CMAKE_BUILD_PARALLEL_LEVEL")}}) + "\\n")
''')
    path.chmod(0o755)
