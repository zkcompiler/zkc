#!/usr/bin/env python3
"""Whole proof controls against independent public-only CLI verifier processes."""

import argparse
import copy
import json
from pathlib import Path
import struct
import subprocess


def write(path, value):
    path.write_text(json.dumps(value) + "\n")
    return path


def messages(proof):
    result = []
    pos = 8
    while pos < len(proof):
        (size,) = struct.unpack_from("<I", proof, pos)
        result.append((pos, pos + 4, size))
        pos += 4 + size
    assert pos == len(proof)
    return result


class Controls:
    def __init__(self, binary, output):
        self.binary = binary
        self.output = output
        self.records = []

    def call(self, name, args, accepts):
        command = list(map(str, [self.binary, *args]))
        call = subprocess.run(command, capture_output=True, text=True, check=False)
        try:
            result = json.loads(call.stdout)
        except ValueError:
            result = None
        # A process crash or malformed report is never a successful refusal.
        passed = isinstance(result, dict) and (
            call.returncode == 0
            and (result.get("accepted") is True or result.get("produced") is True)
            if accepts
            else call.returncode == 1
            and result.get("accepted") is False
            and isinstance(result.get("error"), str)
        )
        record = dict(
            name=name,
            expected_success=accepts,
            exit=call.returncode,
            result=result,
            command=command,
            passed=passed,
            stderr=call.stderr,
        )
        self.records.append(record)
        write(self.output / "results.json", self.records)
        assert passed, (name, record)
        return result

    def mutate_proof(self, app, public, honest):
        proof = honest.read_bytes()
        cases = dict(
            trailing=proof + b"\0",
            truncated=proof[:-1],
            wrong_version=b"BADMAGIC" + proof[8:],
        )
        frames = messages(proof)
        # Every encoded proof message is changed once: round polynomials,
        # evaluation reports, each public/final PCS proof, range and Schnorr.
        for i, (_, start, size) in enumerate(frames):
            bad = bytearray(proof)
            bad[start + size - 1] ^= 1
            cases[f"message-{i}"] = bad
        for index in [0, len(frames) // 2, len(frames) - 1]:
            pos, start, size = frames[index]
            cases[f"length-{index}"] = (
                proof[:pos]
                + struct.pack("<I", size + 32)
                + proof[start : start + size]
                + bytes(32)
                + proof[start + size :]
            )
        for name, data in cases.items():
            path = self.output / f"{name}.proof"
            path.write_bytes(data)
            self.call(name, [app, "verify", *public, path], False)


def transaction(a, c):
    public = [
        a.run / "parameters.json",
        a.run / "fixture/ledger.json",
        a.run / "fixture/statement.json",
    ]
    p, ledger, statement = [json.loads(f.read_text()) for f in public]
    w = json.loads((a.run / "fixture/witness.json").read_text())
    honest = a.output / "honest.proof"
    c.call(
        "honest-produce",
        [a.application, "prove", *public, a.run / "fixture/witness.json", honest],
        True,
    )
    # The copied verifier directory contains neither witness nor proving state.
    verifier = a.output / "public-only"
    verifier.mkdir()
    public_only = [
        write(verifier / f"{i}.json", v) for i, v in enumerate([p, ledger, statement])
    ]
    c.call("public-only-verify", [a.application, "verify", *public_only, honest], True)
    c.mutate_proof(a.application, public_only, honest)
    public_mutations = [
        "context",
        "fee",
        "owner",
        "input-order",
        "output-order",
        "snapshot",
        "network",
        "prior-range",
        "duplicate-id",
        "owner-identity",
    ]
    if len(statement["input_ids"]) == 1:
        # There is no nontrivial order or pair of owners to swap in this shape.
        public_mutations.remove("input-order")
        public_mutations.remove("owner")
    for name in public_mutations:
        ll, ss = copy.deepcopy(ledger), copy.deepcopy(statement)
        if name == "context":
            ss["context"] += "-changed"
        elif name == "fee":
            ss["fee"] = str(int(ss["fee"]) + 1)
        elif name == "owner":
            ll["entries"][0]["owner"] = ll["entries"][1]["owner"]
        elif name == "input-order":
            ss["input_ids"].reverse()
        elif name == "output-order":
            ss["outputs"].reverse()
        elif name == "snapshot":
            ll["snapshot"] += "x"
            ss["ledger_snapshot"] = ll["snapshot"]
        elif name == "network":
            ll["network"] += "x"
            ss["network"] = ll["network"]
        elif name == "prior-range":
            ll["entries"][0]["range_bits"] = p["bits"] * 2
        elif name == "duplicate-id":
            if len(ss["input_ids"]) > 1:
                ss["input_ids"][1] = ss["input_ids"][0]
            else:
                ss["input_ids"].append(ss["input_ids"][0])
        else:
            ll["entries"][0]["owner"] = "00" * 32
        assert ll != ledger or ss != statement, (name, "mutation changed nothing")
        paths = [
            public[0],
            write(a.output / f"{name}-ledger.json", ll),
            write(a.output / f"{name}-statement.json", ss),
        ]
        c.call(name, [a.application, "verify", *paths, honest], False)
    for name in [
        "wrong-owner-secret",
        "wrong-excess-secret",
        "consistent-false-output",
        "out-of-range",
    ]:
        ww, ss = copy.deepcopy(w), copy.deepcopy(statement)
        if name == "out-of-range" and p["bits"] == 64:
            # Bulletproofs' witness API is u64. At full width an out-of-range
            # natural is unrepresentable; test input refusal, not a fake proof.
            ww["values"][0] = str(1 << 64)
            wp = write(a.output / f"{name}-witness.json", ww)
            c.call(
                "out-of-range-witness-admission",
                [a.application, "prove", *public, wp, a.output / f"{name}.proof"],
                False,
            )
            continue
        if name == "wrong-owner-secret":
            ww["secrets"][0] = (991).to_bytes(32, "little").hex()
        elif name == "wrong-excess-secret":
            ww["input_blindings"][0] = (991).to_bytes(32, "little").hex()
        else:
            ww["values"][0] = str(
                int(ww["values"][0]) + 1
                if name == "consistent-false-output"
                else 1 << p["bits"]
            )
            helper = subprocess.check_output(
                [a.run / "tools/helper", "commit", ww["values"][0], ww["blindings"][0]],
                text=True,
            )
            ss["outputs"][0] = json.loads(helper)["commitment"]
        wp = write(a.output / f"{name}-witness.json", ww)
        sp = write(a.output / f"{name}-statement.json", ss)
        proof = a.output / f"{name}.proof"
        paths = [*public[:2], sp]
        c.call(
            name + "-produce-without-relation-gate",
            [a.application, "prove", *paths, wp, proof],
            True,
        )
        c.call(name + "-verify", [a.application, "verify", *paths, proof], False)


def execution(a, c):
    public = [a.export / "public.json", a.export / "setup.json"]
    data, setup = [json.loads(f.read_text()) for f in public]
    wpath = a.run / "relation/assignment.json"
    z = json.loads(wpath.read_text())
    honest = a.output / "honest.proof"
    c.call("honest-produce", ["execution", "prove", *public, wpath, honest], True)
    verifier = a.output / "public-only"
    verifier.mkdir()
    # Remove even the path and pin for the public proving key. Verifier imports
    # only its own verifier key, no assignment/trace/setup private state.
    public_setup = {k: setup[k] for k in ["verifier_key", "verifier_key_id"]}
    public_only = [
        write(verifier / "public.json", data),
        write(verifier / "setup.json", public_setup),
    ]
    c.call("public-only-verify", ["execution", "verify", *public_only, honest], True)
    c.mutate_proof("execution", public_only, honest)
    for name in [
        "context",
        "source",
        "statement",
        "cpu-matrix",
        "memory-matrix",
        "link-matrix",
    ]:
        dd = copy.deepcopy(data)
        if name == "context":
            dd["config"]["steps"] += 1
        elif name == "source":
            dd["source_sha256"] = "11" * 32
        elif name == "statement":
            dd["statement"][0] = str(int(dd["statement"][0]) + 1)
        else:
            view = ["cpu-matrix", "memory-matrix", "link-matrix"].index(name)
            dd["matrices"][view][0][0][2] = str(int(dd["matrices"][view][0][0][2]) + 1)
        pp = write(a.output / f"{name}-public.json", dd)
        c.call(name, ["execution", "verify", pp, public_only[1], honest], False)
    layout = json.loads((a.run / "relation/layout.json").read_text())
    for name in [
        "consistent-false-output",
        "private-cpu",
        "private-memory",
        "private-link",
        "ONE",
    ]:
        dd, zz = copy.deepcopy(data), z.copy()
        if name == "consistent-false-output":
            zz[1] = str(int(zz[1]) + 1)
            dd["statement"][0] = zz[1]
        elif name == "ONE":
            zz[0] = "2"
        else:
            target = {
                "private-cpu": "cpu.1.acc",
                "private-memory": "memory.1.cell0",
                "private-link": "memory.0.read",
            }[name]
            index = layout.index(target)
            zz[index] = str(int(zz[index]) + 1)
        pp = write(a.output / f"{name}-public.json", dd)
        wp = write(a.output / f"{name}-assignment.json", zz)
        proof = a.output / f"{name}.proof"
        c.call(
            name + "-produce-without-relation-gate",
            ["execution", "prove", pp, public[1], wp, proof],
            True,
        )
        c.call(
            name + "-verify", ["execution", "verify", pp, public_only[1], proof], False
        )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument(
        "--application", choices=["tx", "tx-matched", "execution"], required=True
    )
    p.add_argument("--run", type=Path, required=True)
    p.add_argument("--export", type=Path)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument(
        "--binary",
        type=Path,
        required=True,
    )
    a = p.parse_args()
    a.output.mkdir(parents=True, exist_ok=False)
    c = Controls(a.binary, a.output)
    (transaction if a.application in ("tx", "tx-matched") else execution)(a, c)
    print(
        json.dumps(
            dict(
                passed=True,
                checks=len(c.records),
                results=str(a.output / "results.json"),
            )
        )
    )


if __name__ == "__main__":
    main()
