"""Shared byte-language controls for independent executable readers."""

import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import records, tool

root = Path(__file__).resolve().parents[2]
corpus = json.loads((root / "common/tests/fixtures/program/bytes.json").read_text())
assert corpus["format"] == "zkc.program-byte-fixtures/0"
commands = Commands(records())
seen = set()
for item in corpus["cases"]:
    assert item["name"] not in seen
    seen.add(item["name"])
    with case(item["name"]):
        result = commands.attempt([tool("program_codec")], stdin=item["wire"])
        assert result.returncode == (0 if item["admitted"] else 1), result
        if item["admitted"]:
            assert json.loads(result.stdout) == json.loads(item["wire"])
        else:
            assert result.stderr.strip() and not result.stdout, result
print(f"Program byte controls: {counted()} cases; {commands.save()}")
