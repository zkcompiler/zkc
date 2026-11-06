#!/usr/bin/env python3
"""Capture tiny typed-index roots and check strict source/construction readers.

This records structural evidence. It does not authenticate cryptographic source
execution, run Lake, or regenerate the maintained large protocol fixtures.
"""

import argparse
import hashlib
import json
import subprocess
import sys
import time
from copy import deepcopy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
from bridges.common import lean_render  # noqa: E402
from bridges.construction import pair  # noqa: E402
from bridges.structured import snapshot  # noqa: E402

ROOTS = ("Scalar", "Block", "Local", "Repeated")
SCALAR_OPERATION = "transcript.native.indexed.index"
BLOCK_OPERATION = "transcript.native.indexed.indices"


def find_operation(data, contract):
    return next(operation for operation in data[1][7]
                if operation[0] == "exec.apply" and operation[2][0] == contract)


def parameters(operation):
    return next(attribute[1][1] for attribute in operation[1]
                if attribute[0] == "parameters")


def check_refusals(captures):
    refusals = []

    def refuses(name, root_name, mutation):
        data = deepcopy(captures[root_name])
        mutation(data)
        try:
            pair.decode(data)
        except ValueError as error:
            refusals.append({"name": name, "reason": str(error)})
        else:
            raise AssertionError("accepted malformed export: " + name)

    def scalar(data):
        return find_operation(data, SCALAR_OPERATION)

    def block(data):
        return find_operation(data, BLOCK_OPERATION)

    refuses("scalar_missing_bound", "Scalar", lambda data: scalar(data)[3].pop(1))
    refuses("scalar_wrong_reference_sort", "Scalar",
            lambda data: scalar(data)[3].__setitem__(1, 0))
    refuses("scalar_wrong_result", "Scalar",
            lambda data: scalar(data)[4].__setitem__(0, ["apply", "indices", []]))
    refuses("scalar_extra_static_bound", "Scalar",
            lambda data: parameters(scalar(data)).append(["parameter", ["natural", "8"]]))
    for label, value in (("non_power_two", "3"), ("above_provider_bound", str(2**64 - 1))):
        refuses("scalar_" + label, "Scalar", lambda data, value=value:
                parameters(find_operation(data, "index.constant"))[0].__setitem__(1, ["natural", value]))
    refuses("block_extra_dynamic_bound", "Block", lambda data: block(data)[3].append(1))
    refuses("block_wrong_result", "Block",
            lambda data: block(data)[4].__setitem__(0, ["apply", "index", []]))
    for label, value in (("zero", "0"), ("non_power_two", "3"),
                         ("above_provider_bound", str(2**64 - 1))):
        refuses("block_" + label, "Block", lambda data, value=value:
                parameters(block(data))[1].__setitem__(1, ["natural", value]))
    for label, value in (("zero_count", "0"), ("count_cap", "1048577")):
        refuses("block_" + label, "Block", lambda data, value=value:
                parameters(block(data))[2].__setitem__(1, ["natural", value]))
    refuses("block_missing_count", "Block", lambda data: parameters(block(data)).pop())
    refuses("block_wrong_method", "Block",
            lambda data: parameters(block(data))[0][1][1][-1].__setitem__(5, "index"))
    refuses("pair_changed_request_identity", "Block",
            lambda data: data[2][3].__setitem__(5, "other-suite"))
    for data in captures.values():
        pair.decode(data, expected=deepcopy(data))
    return refusals


def capture(compiler, output, update_data):
    output.mkdir(parents=True, exist_ok=True)
    commands = []

    def run(name, arguments):
        command = [str(compiler), *map(str, arguments)]
        started = time.monotonic()
        result = subprocess.run(command, capture_output=True, text=True)
        (output / (name + ".stdout")).write_text(result.stdout)
        (output / (name + ".stderr")).write_text(result.stderr)
        commands.append({"command": command, "code": result.returncode,
                         "seconds": time.monotonic() - started})
        (output / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(result.stderr)
        return result.stdout

    terms, captures = [], {}
    for name in ROOTS:
        flags = ["--source-format=zkc", "--entry=index_services::" + name + "Proof",
                 "--module=index_services=" + str(ROOT / "lean/fixtures/index-services/main.zkc"),
                 "--module=zkc::indices=" + str(ROOT / "libraries/core/collections/indices.zkc"),
                 "--module=zkc::primitives::indices=" +
                 str(ROOT / "libraries/core/primitives/collections/indices.zkc")]
        original = output / (name + ".mlir")
        original.write_text(run(name + "-emit", ["language-emit", *flags]))
        bundle = json.loads(run(name + "-bundle", ["language-bundle", *flags]))
        policy = output / (name + "-policy.json")
        policy.write_text(json.dumps(bundle[2][1]))
        candidate = output / (name + "-candidate.mlir")
        candidate.write_text(run(name + "-construct",
                                 ["protocol-construct-proof", original, policy]))
        data = json.loads(run(name + "-pair",
                              ["protocol-constructed-pair", original, policy, candidate]))
        (output / (name + "-pair.json")).write_text(json.dumps(data, indent=2) + "\n")
        source = json.loads(run(name + "-source",
                                ["protocol-structured", original, "--symbol=" + data[1][3][1]]))
        (output / (name + "-source.json")).write_text(json.dumps(source, indent=2) + "\n")
        captures[name] = data
        terms.append(lean_render.strip_header(snapshot.render(source,
                         "Tests.IndexServices." + name + ".Source")))
        terms.append(lean_render.strip_header(pair.render(data, "Tests.IndexServices." + name)))

    generated = ("module\n\npublic import Zkc.Construction.AuthoredPair\n\n"
                 "@[expose] public section\n\n" + "\n".join(terms))
    target = ROOT / "lean/Tests/IndexServicesData.lean"
    (output / "IndexServicesData.lean").write_text(generated)
    if update_data:
        target.write_text(generated)
    elif generated != target.read_text():
        raise AssertionError("retained tiny data differs from fresh export; inspect before --update-data")
    refusals = check_refusals(captures)
    manifest = {
        "kind": "structural-source-capture", "compiler": str(compiler),
        "compilerSha256": hashlib.sha256(compiler.read_bytes()).hexdigest(),
        "fixtureSha256": hashlib.sha256(
            (ROOT / "lean/fixtures/index-services/main.zkc").read_bytes()).hexdigest(),
        "roots": list(captures), "refusals": refusals,
        "artifacts": {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                      for path in sorted(output.iterdir())
                      if path.suffix in (".json", ".mlir", ".lean")
                      and path.name not in ("manifest.json", "commands.json")},
    }
    (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Four fresh source/constructed roots, {len(refusals)} strict malformed-export refusals")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--update-data", action="store_true")
    arguments = parser.parse_args()
    capture(arguments.compiler.resolve(), arguments.output.resolve(), arguments.update_data)


if __name__ == "__main__":
    main()
