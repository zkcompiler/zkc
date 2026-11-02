"""The EVM target declaration's generator refuses every shared case by rule.

The compiler projects `common/targets/evm.json` at configure time. These checks
run the same generator on the authored file and on each shared refusal case;
`crates/zkc/build.rs` runs the same cases against the Rust SDK build.
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

from cases import case
from tools import records

ROOT = Path(__file__).resolve().parents[2]
TARGETS = ROOT / "common/targets"
sys.path.insert(0, str(TARGETS))
import generate  # noqa: E402
import validation_cases  # noqa: E402

DATA = (TARGETS / "evm.json").read_bytes()
OUT = Path(records())

with case("the authored declaration is accepted and named by its bytes"):
    declaration = generate.check(DATA)
    assert generate.identity(DATA) == "zkc.evm-target/0:" + hashlib.sha256(DATA).hexdigest()
    result = subprocess.run([sys.executable, TARGETS / "generate.py", "--source", TARGETS / "evm.json",
                             "--output", OUT / "Declaration.h.inc"], capture_output=True, text=True)
    assert result.returncode == 0, result.stderr
    header = (OUT / "Declaration.h.inc").read_text()
    assert f'identity[] = "{generate.identity(DATA)}";' in header
    for fork in declaration["forks"]:
        assert f'X({fork["name"].capitalize()}, "{fork["name"]}", ' in header

with case("the generator's Keccak-256 matches the standard vectors"):
    assert generate.keccak256(b"").hex() == (
        "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
    assert generate.keccak256(b"a" * 136).hex() != generate.keccak256(b"a" * 135).hex()
    assert generate.keccak256(declaration["abi"]["signature"].encode())[:4].hex() == "a488e1e4"

cases = validation_cases.load()
with case("the shared cases cover every rule"):
    assert {item["rule"] for item in cases} == {
        "keys", "format", "fork", "default-fork", "rules", "selector", "abi", "solc", "limit",
        "revert"}

for item in cases:
    with case(f"refused: {item['name']}"):
        edited = validation_cases.apply(item["edits"], declaration)
        try:
            generate.validate(edited)
        except generate.Refusal as refusal:
            assert refusal.rule == item["rule"], str(refusal)
        else:
            raise AssertionError("accepted")
        source = OUT / "case.json"
        source.write_text(json.dumps(edited))
        result = subprocess.run([sys.executable, TARGETS / "generate.py", "--source", source],
                                capture_output=True, text=True)
        assert result.returncode == 1 and f"evm-target {item['rule']}:" in result.stderr, result

for name, text in (("repeated key", b'{"format":"zkc.evm-target/0","format":"zkc.evm-target/0"}'),
                   ("fractional number", DATA.replace(b'"maximum": 10}', b'"maximum": 10.0}', 1)),
                   ("non-ASCII byte", DATA.replace(b'"cancun"', b'"canc\xc3\xbcn"', 1))):
    with case(f"refused before validation: {name}"):
        assert text != DATA or name == "repeated key"
        try:
            generate.check(text)
        except generate.Refusal as refusal:
            assert refusal.rule in ("keys", "format"), str(refusal)
        else:
            raise AssertionError("accepted")
