"""Shared byte-language controls for independent executable readers."""

import json
from pathlib import Path

from cases import case, counted
from commands import Commands
from tools import records, tool

root = Path(__file__).resolve().parents[2]
corpus = json.loads((root / "common/tests/fixtures/program/bytes.json").read_text())
assert corpus["format"] == "zkc.program-byte-fixtures/0"


def wire(value):
    """One string, or segments whose repeats write `{i}` as 0..count."""
    if isinstance(value, str):
        return value
    out = []
    for segment in value:
        if isinstance(segment, str):
            out.append(segment)
        else:
            assert set(segment) == {"repeat", "count", "separator"}, segment
            out.append(segment["separator"].join(
                segment["repeat"].replace("{i}", str(i))
                for i in range(segment["count"])))
    return "".join(out)


commands = Commands(records())
seen = set()
for item in corpus["cases"]:
    assert item["name"] not in seen
    seen.add(item["name"])
    with case(item["name"]):
        text = wire(item["wire"])
        result = commands.attempt([tool("program_codec"), "--report"],
                                  stdin=text)
        assert result.returncode == 0, result
        outcome = json.loads(result.stdout)
        if "admitted" in item:
            assert "refused" not in item
            expected = item["admitted"]
            assert outcome[0] == "admitted", outcome
            assert outcome[1] == json.loads(text)
            assert outcome[2:] == [expected["static_instructions"],
                                   expected["descriptor_charge"]], outcome[2:]
        else:
            assert outcome[:2] == ["refused", item["refused"]], outcome
print(f"Program byte controls: {counted()} cases; {commands.save()}")
