"""Native/reference byte agreement and exact raw mathematical schema controls."""

import copy
import json
import random
import subprocess
import sys

from tools import corpus, mathematical_codec, records

fixtures = corpus / "mathematical"
sys.path.insert(0, str(fixtures))
import encoding  # noqa: E402

directory = records()


def run(mode, path, accepted=True):
    result = subprocess.run([mathematical_codec, mode, path], capture_output=True, text=True, timeout=20)
    assert (result.returncode == 0) == accepted, (mode, path, result.stderr)
    return result.stdout.splitlines()


for vector in json.loads((fixtures / "vectors.json").read_text()):
    name = vector["name"]
    source = fixtures / f"{name}.json"
    expected = (fixtures / f"{name}.hex").read_text().strip()
    actual = run("json", source)
    assert actual[0] == expected, name
    if vector["digest"]:
        assert actual[1] == vector["digest"], name
    binary = directory / f"{name}.bin"
    binary.write_bytes(bytes.fromhex(expected))
    assert run("binary", binary) == actual, name
    if name.endswith(".subject"):
        assert run("schema", source) == actual, name

# The same adversarial bytes go to two independent binary readers. Agreement
# includes accepted canonical mutations, not only rejection of random garbage.
rng = random.Random(4917)
base = bytes.fromhex((fixtures / "message.subject.hex").read_text().strip())
for index in range(200):
    mutated = bytearray(base)
    if index % 3 == 0:
        del mutated[rng.randrange(len(mutated)):]
    else:
        position = rng.randrange(len(mutated))
        mutated[position] ^= rng.randrange(1, 256)
    path = directory / f"mutation-{index}.bin"
    path.write_bytes(mutated)
    try:
        decoded = encoding.decode(bytes(mutated))
    except ValueError:
        run("binary", path, False)
    else:
        assert run("binary", path)[0] == encoding.encode(decoded).hex()

base = json.loads((fixtures / "message.subject.json").read_text())
for label, mutate in {
    "unknown-top-field": lambda value: value.update(debug=0),
    "wrong-profile": lambda value: value.update(profile="zkc.math.located.v1"),
    "missing-roots": lambda value: value["module"].pop("roots"),
    "wrong-ref-sort": lambda value: value["module"]["entry"].update(definition="0"),
    "extra-terminal-field": lambda value: value["module"]["definitions"][0]["body"]["terminal"].append(0),
    "unknown-step": lambda value: value["module"]["definitions"][0]["body"]["steps"][0].__setitem__(0, "oracle"),
}.items():
    changed = copy.deepcopy(base)
    mutate(changed)
    path = directory / f"{label}.json"
    path.write_text(json.dumps(changed))
    run("schema", path, False)

print("native mathematical codec: five vectors, 200 binary mutations, schema roundtrips and malformed records")
