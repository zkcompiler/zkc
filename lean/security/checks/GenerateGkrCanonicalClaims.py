"""Render fixed GKR soundness requests through the common data-only renderer.

The request quantities are proposals. The generated registration applies the
checked compiled theorems to their exact meanings; this script proves nothing.
"""

import argparse
from copy import deepcopy
import hashlib
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "lean"))
from bridges.pipeline import evidence, source_claims  # noqa: E402


def natural(value):
    return {"kind": "natural", "value": str(value)}


def reference(name):
    return {"kind": "reference", "name": name}


def binary(operator, left, right):
    return {"kind": "binary", "operator": operator, "left": left, "right": right}


def application(name, arguments=(), version=None):
    return {"kind": "application", "name": name, "version": version,
            "arguments": [{"label": label, "value": value} for label, value in arguments]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--original", type=Path, required=True)
    parser.add_argument("--validator", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    original = source_claims.decode(args.original.read_text())
    validator = source_claims.decode(args.validator.read_text())
    if original[0] != "zkc.structured-source/0" or validator[0] != "zkc.constructed-participant/0":
        raise ValueError("expected current structured source and constructed validator")
    if original[2] != validator[1]:
        raise ValueError("source identity mismatch")
    cardinality = application("cardinality", [(None, reference("bls12-381.fr"))])
    price = binary("/", natural(4), cardinality)
    cost = binary("/", natural(160), cardinality)
    request = {
        "subject": {"unit": source_claims.digest(args.original.read_bytes()),
                    "entry": original[3], "stage": "compiled-ideal",
                    "artifacts": [{"role": "constructed-participant",
                                   "digest": source_claims.digest(args.validator.read_bytes())}]},
        "property": {"name": "soundness", "version": 0},
        "model": application("models.fiat_shamir", [
            ("level", reference("levels.ideal")),
            ("statement", reference("statements.adaptive")),
            ("oracle", application("oracles.random", [(None, reference("construction.provider"))], 0)),
            ("queries", reference("Q")), ("budget_symbol", reference("Q")),
            ("validator_cost", cost), ("application", reference("application"))], 0),
        "target": {"protocol": original[3], "clause": 1, "name": "circuit_outputs"},
        "accept": {"output": True, "port": 0, "role": 1, "path": []},
        "quantity": {"kind": "scalar", "expression": binary("/",
            binary("*", natural(4), binary("+", reference("Q"), natural(40))), cardinality)},
        "capabilities": []}
    charged = deepcopy(request)
    charged["quantity"] = {"kind": "charged", "charges": [
        {"site": site, "expression": price}
        for site in ["output", "left.challenge", "right.challenge", "line_challenge"]]}
    namespace = "ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessClaims"
    registration = "ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessRegistration"
    sources = {"claims": [
        {"request": value, "method": application(method, version=0)}
        for value, method in [(request, "fs.keyed_soundness"), (charged, "fs.keyed_charged")]]}
    header = evidence.HEADER.format(
        imports=f"public import {registration}\npublic meta import {registration}",
        doc="Generated fixed requests. Regenerate with checks/GenerateGkrCanonicalClaims.py. "
            "The common renderer emits data and checked receipt-construction calls.")
    source = header + evidence.request_commands(namespace, sources, registration + ".library")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(source)
    print(f"generated {namespace}: sha256:{hashlib.sha256(source.encode()).hexdigest()}")


if __name__ == "__main__":
    main()
