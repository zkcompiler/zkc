#!/usr/bin/env python3
"""Check mathematical bytes and schema against independent Lean/native readers."""

import argparse
import copy
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tests/fixtures/mathematical"
sys.path.insert(0, str(FIXTURES))
import encoding  # noqa: E402


def check_readers(native=None):
    subprocess.run(["lake", "build", "mathematical-reference"], cwd=ROOT / "formal", check=True)
    lean = ROOT / "formal/.lake/build/bin/mathematical-reference"
    count = 0
    with tempfile.TemporaryDirectory(prefix="zkc-mathematical-readers-") as temporary:
        directory = Path(temporary)
        path = directory / "value.bin"
        text = directory / "value.json"

        def run(tool, mode, source, accepted, expected=None):
            result = subprocess.run([str(tool), mode, str(source)], capture_output=True, text=True, timeout=20)
            assert (result.returncode == 0) == accepted, (tool, mode, result.stderr)
            if accepted:
                assert result.stdout.splitlines()[0] == expected, (tool, mode, result.stdout[:200])

        def binary(data):
            nonlocal count
            count += 1
            path.write_bytes(data)
            try:
                decoded = encoding.decode(data)
            except ValueError:
                accepted, expected = False, None
            else:
                accepted, expected = True, encoding.encode(decoded).hex()
            run(lean, "binary", path, accepted, expected)
            if native:
                run(native, "binary", path, accepted, expected)

        def schema(value, accepted):
            nonlocal count
            count += 1
            raw = encoding.encode(value)
            path.write_bytes(raw)
            run(lean, "schema", path, accepted, raw.hex())
            if native:
                text.write_text(json.dumps(value))
                run(native, "schema", text, accepted, raw.hex())

        for vector in json.loads((FIXTURES / "vectors.json").read_text()):
            name = vector["name"]
            raw = bytes.fromhex((FIXTURES / f"{name}.hex").read_text())
            binary(raw)
            if name.endswith(".subject"):
                schema(json.loads((FIXTURES / f"{name}.json").read_text()), True)

        base = bytes.fromhex((FIXTURES / "message.subject.hex").read_text())
        rng = random.Random(4917)
        for index in range(250):
            mutated = bytearray(base)
            if index % 3 == 0:
                del mutated[rng.randrange(len(mutated)):]
            else:
                position = rng.randrange(len(mutated))
                mutated[position] ^= rng.randrange(1, 256)
            binary(bytes(mutated))

        for tree in [["unknown"], ["natural", "01"], ["natural", "-1"],
                     ["natural", "18446744073709551616"], ["boolean", "yes"],
                     ["object", "b", ["natural", "1"], "a", ["natural", "2"]],
                     ["object", "a", ["natural", "1"], "a", ["natural", "2"]],
                     ["array", "untyped"], ["string", "x", "y"]]:
            binary(encoding.tree_bytes(tree))
        for tag in [b"\0", b"\1"]:
            binary(tag + (2**64 - 1).to_bytes(8, "little"))
        binary(b"\0\x01\0\0\0\0\0\0\0\xff")
        binary(base + b"\0")
        nested = 0
        for _ in range(63):
            nested = [nested]
        binary(encoding.encode(nested))
        # Build a logical tree manually so the reference encoder cannot refuse
        # it before all independent readers receive the same depth violation.
        wrapper = b"\1" + (2).to_bytes(8, "little") + b"\0" + (5).to_bytes(8, "little") + b"array"
        binary(wrapper + encoding.encode(nested))

        source = json.loads((FIXTURES / "message.subject.json").read_text())
        for mutate in [
            lambda value: value.update(debug=0),
            lambda value: value.update(profile="zkc.math.located.v1"),
            lambda value: value["module"].pop("roots"),
            lambda value: value["module"]["entry"].update(definition="0"),
            lambda value: value["module"]["definitions"][0]["body"]["terminal"].append(0),
            lambda value: value["module"]["definitions"][0]["body"]["steps"][0].__setitem__(0, "oracle"),
        ]:
            changed = copy.deepcopy(source)
            mutate(changed)
            schema(changed, False)
    print(f"mathematical readers: {count} golden, mutation, schema and resource cases; "
          f"Python/Lean{'/native' if native else ''} agreement")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path, help="also compare the built native mathematical codec")
    args = parser.parse_args()
    subprocess.run([sys.executable, str(FIXTURES / "check.py"), "--lean"], cwd=ROOT, check=True)
    check_readers(args.native.resolve() if args.native else None)
