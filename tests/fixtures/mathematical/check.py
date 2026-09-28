#!/usr/bin/env python3
"""Canonical encoding controls, independent of mathematical type admission."""

import argparse
import copy
import json
from pathlib import Path
import random
import subprocess

import encoding as codec

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def refused(action):
    try:
        action()
    except ValueError:
        return
    raise AssertionError("malformed input accepted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="compare the independent Lean encoder")
    args = parser.parse_args()
    vectors = json.loads((HERE / "vectors.json").read_text())
    for vector in vectors:
        path = HERE / (vector["name"] + ".json")
        value = codec.parse(path.read_text())
        expected = (HERE / (vector["name"] + ".hex")).read_text().strip()
        raw = codec.encode(value)
        assert raw.hex() == expected
        assert len(raw) == vector["bytes"]
        assert codec.decode(raw) == value
        if vector["digest"]:
            assert codec.digest(value) == vector["digest"]
            independent = subprocess.run(["sha256sum"], input=codec.PREFIXES[value["profile"]] + raw,
                                         capture_output=True, check=True).stdout.decode().split()[0]
            assert independent == vector["digest"]
        if args.lean:
            result = subprocess.run(
                ["lake", "env", "lean", "--run", str(HERE / "encode.lean"), str(path)],
                cwd=ROOT / "formal", capture_output=True, text=True, check=True, timeout=120)
            assert result.stdout.strip() == expected, vector["name"]

    # Manually specified logical bytes, independent of the encoder.
    assert codec.encode([]) == b"\x01\x01\0\0\0\0\0\0\0\x00\x05\0\0\0\0\0\0\0array"
    assert codec.encode({"b": 2, "a": 1}) == codec.encode({"a": 1, "b": 2})
    assert codec.encode("é") != codec.encode("e\u0301")
    for text in ['{"x":1,"x":2}', 'null', '-1', '1.0', 'NaN', '18446744073709551616',
                 '"\\ud800"', '[01]', '[' * 66 + '0' + ']' * 66]:
        refused(lambda text=text: codec.parse(text))
    for value in [None, -1, 2**64, 1.0, {1: 2}, '\ud800', [0] * codec.MAX_ITEMS]:
        refused(lambda value=value: codec.encode(value))
    value = 0
    for _ in range(63):
        value = [value]
    codec.encode(value)
    refused(lambda: codec.encode([value]))
    refused(lambda: codec.encode([[0] * 10_000] * 20))
    refused(lambda: codec.encode('x' * codec.MAX_BYTES))
    refused(lambda: codec.encode({'x' * codec.MAX_BYTES: 0}))
    refused(lambda: codec.parse(' ' * (codec.MAX_JSON_BYTES + 1)))
    refused(lambda: codec.decode(b'\x01' + (2**64 - 1).to_bytes(8, 'little')))
    refused(lambda: codec.decode(b'\0' + (2**64 - 1).to_bytes(8, 'little')))
    refused(lambda: codec.decode(b'\0\x01\0\0\0\0\0\0\0\xff'))
    for tree in [['unknown'], ['natural', '01'], ['natural', '-1'], ['boolean', 'yes'],
                 ['object', 'b', ['natural', '1'], 'a', ['natural', '2']],
                 ['object', 'a', ['natural', '1'], 'a', ['natural', '2']],
                 ['array', 'untyped'], ['string', 'x', 'y']]:
        refused(lambda tree=tree: codec.decode(codec.tree_bytes(tree)))
    raw = codec.encode({"a": [1, True]})
    for offset in range(len(raw)):
        refused(lambda offset=offset: codec.decode(raw[:offset]))
    refused(lambda: codec.decode(raw + b'\0'))

    # Random byte mutations must either refuse or have one exact canonical re-encoding.
    randomizer = random.Random(7469)
    for _ in range(250):
        changed = bytearray(raw)
        changed[randomizer.randrange(len(raw))] ^= randomizer.randrange(1, 256)
        try:
            value = codec.decode(bytes(changed))
        except ValueError:
            continue
        assert codec.encode(value) == bytes(changed)

    subject = codec.parse((HERE / 'message.subject.json').read_text())
    original = codec.digest(subject)
    for change in ('site', 'wire', 'role'):
        other = copy.deepcopy(subject)
        if change == 'site':
            other['module']['definitions'][0]['body']['steps'][0][1] = 1
        elif change == 'wire':
            other['manifest']['wires'][0]['digest'] = '1' * 64
        else:
            other['module']['roles'][0] = 'different-role'
        assert codec.digest(other) != original
    # Presentation data is outside the subject, not silently stripped inside it.
    debug = dict(subject, debug={"line": 7})
    refused(lambda: codec.digest(debug))
    refused(lambda: codec.digest(dict(subject, profile='zkc.unknown.v1')))
    print(f"{len(vectors)} golden vectors; canonicality, mutation and resource controls passed"
          + ("; independent Lean bytes matched" if args.lean else ""))


if __name__ == '__main__':
    main()
