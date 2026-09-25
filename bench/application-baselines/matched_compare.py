#!/usr/bin/env python3
"""Functional same-fixture comparison; no performance conclusions from this run."""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--native", action="store_true")
    a = parser.parse_args()
    a.output.mkdir(parents=True, exist_ok=False)
    records = []

    def call(name, command, expected=None):
        command = list(map(str, command))
        result = subprocess.run(command, capture_output=True, text=True, check=False)
        (a.output / (name + ".stdout")).write_text(result.stdout)
        (a.output / (name + ".stderr")).write_text(result.stderr)
        try:
            value = json.loads(result.stdout)
        except ValueError:
            value = None
        if expected is None:
            passed = result.returncode == 0 and isinstance(value, dict)
        elif expected.startswith("tx-"):
            passed = (
                result.returncode == 1
                and isinstance(value, dict)
                and value.get("error") == expected
            )
        else:
            passed = (
                result.returncode != 0
                and isinstance(value, dict)
                and value.get("code") == expected
                and value.get("phase") == "run"
            )
        records.append(
            dict(
                name=name,
                command=command,
                exit=result.returncode,
                expected=expected,
                passed=passed,
                report={k: v for k, v in value.items() if k != "events"}
                if isinstance(value, dict)
                else None,
            )
        )
        write(a.output / "commands.json", records)
        assert passed, (name, value, result.stderr)
        return value

    run = a.run.resolve()
    parameters = run / "parameters.json"
    ledger = run / "fixture/ledger.json"
    statement = run / "fixture/statement.json"
    witness = run / "fixture/witness.json"
    params = json.loads(parameters.read_text())
    helper = run / "tools/helper"
    inputs = [parameters, ledger, statement]
    pins = {
        str(p): digest(p)
        for p in [*inputs, witness, helper, a.binary, Path(__file__).resolve()]
    }
    public = a.output / "public-only"
    public.mkdir()
    public_inputs = [
        write(public / path.name, json.loads(path.read_text())) for path in inputs
    ]
    proof = a.output / "direct.proof"
    second = a.output / "fresh.proof"
    for name, target in [("direct", proof), ("fresh", second)]:
        assert call(
            name + ".produce",
            [a.binary, "tx-matched", "prove", *inputs, witness, target],
        )["produced"]
        verified = call(
            name + ".verify", [a.binary, "tx-matched", "verify", *public_inputs, target]
        )
        assert verified["accepted"] and verified["witness_read"] is False
    assert proof.read_bytes() != second.read_bytes()
    trace = a.output / "direct.trace.json"
    envelope = public / "validator.json"
    call(
        "direct.trace", [a.binary, "tx-matched", "trace", *public_inputs, proof, trace]
    )
    call("helper.admit", [helper, "admit", *public_inputs, envelope])
    assert json.loads(envelope.read_text())[3] == []
    observed = json.loads(trace.read_text())
    actual_public = {row[0]: row[2] for row in json.loads(envelope.read_text())[2]}
    for name in ["g", "h"]:
        encoded = bytes.fromhex(actual_public[name])
        assert encoded[:6] == b"ZKCV\x01\x11"
        assert (
            int.from_bytes(encoded[6:10], "little")
            == params["bits"] * params["outputs"]
        )
        assert observed["generators"][name] == [
            encoded[i : i + 32].hex() for i in range(10, len(encoded), 32)
        ]
    independent = call(
        "helper.equations", [helper, "equations", parameters, envelope, trace]
    )
    assert independent["pass"] is True

    def native(name, producer, validator, expected=None):
        artifact = [
            run / n
            for n in [
                "source.stdout",
                "descriptor.stdout",
                "construct.stdout",
                "dense.compile.stdout",
            ]
        ]
        tools = [run / "tools" / n for n in ["runtime", "compiler", "lean"]]
        for path in [*artifact, *tools]:
            current = digest(path)
            assert str(path) not in pins or pins[str(path)] == current
            pins[str(path)] = current
        output = a.output / (name + ".native.proof")
        for role, data in [("produce", producer), ("validate", validator)]:
            report = call(
                name + ".native." + role,
                [
                    tools[0],
                    role + "-artifact",
                    *artifact,
                    data,
                    tools[1],
                    tools[2],
                    output,
                    "1000000",
                    "--trace=none",
                ],
                expected if role == "validate" else None,
            )
            if role == "validate" and expected is None:
                assert report["status"] == "accepted"
            if role == "produce":
                assert report["status"] == "produced"

    if a.native:
        producer = a.output / "producer.json"
        call("helper.prepare", [helper, "prepare", *inputs, witness, producer])
        native("honest", producer, envelope)
    # These invalid private relations must create complete proofs before rejection.
    original_w = json.loads(witness.read_text())
    original_t = json.loads(statement.read_text())
    mutations = [
        (f"owner-{i}", "tx-matched-authorization") for i in range(params["inputs"])
    ]
    mutations += [
        ("excess", "tx-matched-balance"),
        ("conservation", "tx-matched-balance"),
    ]
    if params["bits"] < 64:
        mutations.append(("range", "tx-matched-range"))
    for name, expected in mutations:
        ww, tt = copy.deepcopy(original_w), copy.deepcopy(original_t)
        if name.startswith("owner-"):
            index = int(name.split("-")[1])
            ww["secrets"][index] = (991).to_bytes(32, "little").hex()
        elif name == "excess":
            ww["input_blindings"][0] = (991).to_bytes(32, "little").hex()
        else:
            ww["values"][0] = str(
                1 << params["bits"] if name == "range" else int(ww["values"][0]) + 1
            )
            tt["outputs"][0] = call(
                name + ".commit",
                [helper, "commit", ww["values"][0], ww["blindings"][0]],
            )["commitment"]
        wp = write(a.output / (name + ".witness.json"), ww)
        sp = write(a.output / (name + ".statement.json"), tt)
        candidate = a.output / (name + ".proof")
        call(
            name + ".produce",
            [a.binary, "tx-matched", "prove", parameters, ledger, sp, wp, candidate],
        )
        call(
            name + ".verify",
            [a.binary, "tx-matched", "verify", parameters, ledger, sp, candidate],
            expected,
        )
        if a.native:
            pp = a.output / (name + ".producer.json")
            vp = a.output / (name + ".validator.json")
            call(name + ".prepare", [helper, "prepare", parameters, ledger, sp, wp, pp])
            call(name + ".admit", [helper, "admit", parameters, ledger, sp, vp])
            native(name, pp, vp, "rejected:require")
    assert all(digest(path) == value for path, value in pins.items())
    report = dict(
        passed=True,
        parameters=params,
        fresh=True,
        public_only=True,
        exact_generator_bytes=True,
        independent_equations=independent,
        native_dense_compared=a.native,
        checks=len(records),
        pins=pins,
        scope="functional fresh whole proofs on identical fixture data; different transcripts/wires; no timing inference",
    )
    write(a.output / "summary.json", report)
    print(json.dumps(report))


if __name__ == "__main__":
    main()
