#!/usr/bin/env python3
"""Independently enforce public artifact admission over broader common sources.

Each subject must first pass the native common constructor. Then both native
artifact entries and the original-source Lean consumer must refuse the same
profile defect before executing any proof operation.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path


import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "tests/support"))
from bls_fixture import nominal
from journal import Journal, TIMEOUT, positive_timeout

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("native", "compiler", "lean-checker", "lean-reference", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--timeout", type=positive_timeout, default=TIMEOUT)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    fixtures = Path(__file__).parent / "fixtures/artifact"
    source = json.loads((fixtures / "dleq.json").read_text())
    descriptor = json.loads((fixtures / "dleq.construction.json").read_text())
    cases, commands, records = [], [], []
    journal = Journal(args.output / "commands", timeout=args.timeout)

    def removed(name, labels):
        desc = copy.deepcopy(descriptor)
        desc[4] = [b for b in desc[4] if b[0] not in labels]
        cases.append((name, source, desc, "artifact-unbound-verifier-input"))

    removed("unbound-image", [descriptor[4][-1][0]])
    removed("unbound-statement", [b[0] for b in descriptor[4]])
    for role, kind in [("V", "bool"), ("V", "rng"), ("V", "nonce"),
                       ("V", "opening_state"), ("V", "transcript"), ("P", "transcript")]:
        src = copy.deepcopy(source)
        entry = src[3][-1]
        name = "extra_" + kind
        entry[4].append([name, role, nominal(kind)])
        entry[5].append([role, nominal(kind)])
        entry[7][-1][1].append(name)
        code = ("artifact-source-transcript" if kind == "transcript" else
                "artifact-unbound-verifier-input" if kind == "bool" else
                "artifact-verifier-resource")
        cases.append((role + "-" + kind, src, descriptor, code))
    countermodel = fixtures / "unbound-dleq"
    cases.append(("review-forgery", json.loads((countermodel / "source.json").read_text()),
                  json.loads((countermodel / "descriptor.json").read_text()),
                  "artifact-unbound-verifier-input"))

    def call(argv):
        result = journal.attempt(argv)
        commands.append({"argv": list(map(str, argv)), "returncode": result.returncode})
        return result

    for name, src, desc, code in cases:
        case = args.output / name
        case.mkdir(exist_ok=True)

        def save(name, value):
            path = case / (name + ".json")
            path.write_text(json.dumps(value, separators=(",", ":")) + "\n")
            return path

        s, d = save("source", src), save("descriptor", desc)
        compiled = call([args.compiler, "protocol-construct", s, d])
        assert compiled.returncode == 0, (name, compiled.stderr)
        construction = json.loads(compiled.stdout)
        c = save("construction", construction)
        common = save("common", construction[2])
        compiled = call([args.compiler, "protocol-compile", common])
        assert compiled.returncode == 0, (name, compiled.stderr)
        physical = save("physical", json.loads(compiled.stdout))
        # Most cases deliberately lack inputs: profile rejection precedes them.
        # The reviewer case retains the actual historically accepted forgery.
        values = (json.loads((countermodel / "validator.json").read_text()) if name == "review-forgery"
                  else ["zkc.artifact-inputs/1", "", [], [], ["zkc.public-configuration/1", [], [], []]])
        inputs = save("inputs", values)
        replies = save("replies", ["zkc.primitive-replies/1", []])
        proof = case / "proof.bin"
        original = (countermodel / "proof.bin").read_bytes() if name == "review-forgery" else b"unchanged output"
        proof.write_bytes(original)
        reference = call([args.lean_reference, "reference", s, d, inputs, proof, replies])
        assert reference.returncode == 1, (name, reference.stdout, reference.stderr)
        assert json.loads(reference.stdout) == ["refused", code], (name, reference.stdout)
        save("reference", json.loads(reference.stdout))
        for mode in ("produce-artifact", "validate-artifact"):
            native = call([args.native, mode, s, d, c, physical, inputs,
                           args.compiler, args.lean_checker, proof, "10000"])
            result = json.loads(native.stdout)
            save(mode, result)
            assert native.returncode == 1 and result["code"] == code, (name, mode, result)
            assert result["phase"] == "admission" and result["events"] == []
            assert result["proof_bytes"] == 0 and proof.read_bytes() == original
            records.append({"case": name, "mode": mode, "code": code,
                            "native_and_reference_agree": True})
    summary = {"status": "pass", "subjects": len(cases), "comparisons": len(records),
               "cases": records, "tools": {
                   name: {"path": str(getattr(args, name)),
                          "sha256": hashlib.sha256(getattr(args, name).read_bytes()).hexdigest()}
                   for name in ("native", "compiler", "lean_checker", "lean_reference")}}
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (args.output / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
    print(json.dumps({k: summary[k] for k in ("status", "subjects", "comparisons")}))


if __name__ == "__main__":
    main()
