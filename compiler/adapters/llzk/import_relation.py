#!/usr/bin/env python3
"""Run LLVM20 LLZK ingress and LLVM23 native validation in separate processes.

The final directory is published only after both tools succeed. A receipt binds
bytes and an explicit interface; it is not evidence of frontend adequacy.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

SOURCE_LIMIT = 2 * 1024 * 1024
OUTPUT_LIMIT = 16 * 1024 * 1024


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def invoke(command, env, destination=None):
    # File-backed output is bounded after exit; the adapter has its own memory,
    # CPU and input limits. Native relation-read has independent reader limits.
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        result = subprocess.run(command, env=env, stdout=out, stderr=err, timeout=60)
        err.seek(0)
        message = err.read(8192).decode(errors="replace")
        if result.returncode:
            raise ValueError(f"llzk-subprocess: exit {result.returncode}: {message}")
        out.seek(0)
        data = out.read(OUTPUT_LIMIT + 1)
        if len(data) > OUTPUT_LIMIT:
            raise ValueError("llzk-native-output-limit")
        if destination:
            destination.write_bytes(data)
        return data


def import_relation(args):
    output = args.output.resolve()
    if output.exists():
        raise ValueError("llzk-output-exists")
    adapter, native = args.adapter.resolve(), args.native.resolve()
    env = os.environ.copy()
    adapter_env = env.copy()
    if args.adapter_library_path:
        adapter_env["LD_LIBRARY_PATH"] = args.adapter_library_path
    # A private snapshot prevents a changing source pathname from mixing receipts.
    with tempfile.TemporaryDirectory(prefix=".llzk-import-", dir=output.parent) as tmp:
        work = Path(tmp)
        with args.source.open("rb") as src:
            data = src.read(SOURCE_LIMIT + 1)
        if len(data) > SOURCE_LIMIT:
            raise ValueError("llzk-source-limit")
        snapshot = work / "source.llzk"
        snapshot.write_bytes(data)
        bundle = work / "bundle"
        invoke(
            [
                str(adapter),
                str(snapshot),
                "--field",
                args.field,
                "--entry",
                args.entry,
                "--outputs",
                args.outputs,
                "--public-inputs",
                args.public_inputs,
                "--output",
                str(bundle),
            ],
            adapter_env,
        )
        receipt = json.loads((bundle / "receipt.json").read_text())
        for key, path in [
            ("source", snapshot),
            ("normalized", bundle / "normalized.llzk"),
            ("r1cs", bundle / "relation.r1cs"),
        ]:
            if receipt[key + "_sha256"] != digest(path):
                raise ValueError("llzk-receipt-hash")
        canonical = bundle / "relation.json"
        invoke(
            [str(native), "relation-read", str(bundle / "relation.r1cs")],
            env,
            canonical,
        )
        info = json.loads(
            invoke([str(native), "relation-inspect", str(canonical)], env)
        )
        if info["public_outputs"] != len(receipt["public_outputs"]) or info[
            "public_inputs"
        ] != len(receipt["public_inputs"]):
            raise ValueError("llzk-native-public-layout")
        native_receipt = {
            "schema": "zkc-llzk-native-binding/v1",
            "subject": info["subject"],
            "field": info["field"],
            "columns": info["columns"],
            "constraints": info["constraints"],
            "public_outputs": receipt["public_outputs"],
            "public_inputs": receipt["public_inputs"],
            "canonical_sha256": digest(canonical),
            "adapter_receipt_sha256": digest(bundle / "receipt.json"),
            "adapter_binary_sha256": digest(adapter),
            "native_binary_sha256": digest(native),
            "claim": "Native target relation validated; source adequacy remains a trust premise.",
        }
        (bundle / "native-binding.json").write_text(
            json.dumps(native_receipt, indent=2) + "\n"
        )
        shutil.copyfile(snapshot, bundle / "source.llzk")
        # mkdir is exclusive. Failure cannot replace any pre-existing destination.
        output.mkdir()
        for file in bundle.iterdir():
            shutil.move(str(file), output / file.name)
        return native_receipt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--adapter", type=Path, required=True)
    parser.add_argument("--native", type=Path, required=True)
    parser.add_argument("--adapter-library-path")
    parser.add_argument("--field", choices=["bls12381", "bn254"], required=True)
    parser.add_argument("--entry", required=True)
    parser.add_argument(
        "--outputs", required=True, help="ordered CSV, empty string for none"
    )
    parser.add_argument(
        "--public-inputs",
        required=True,
        help="ordered names; #N for unnamed argument N",
    )
    parser.add_argument("--output", type=Path, required=True)
    try:
        result = import_relation(parser.parse_args())
    except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        parser.exit(2, f"Refused {error}\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
