#!/usr/bin/env python3
"""Check private fixture support against the frozen public proof.

This command does not generate a protocol proof or write fixtures.  The
declassified private sidecar is one support point and provides no entropy,
necessity, or uniform-sampling evidence.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import sys
from typing import Any

from duplexmodel.construction import parse_construction
from duplexmodel.diagnostics import DuplexModelError, MalformedInput
from duplexmodel.execution import (
    PUBLIC_PROOF_SCHEMA,
    PublicProof,
    derive_generation_prefix_challenges,
    parse_public_inputs,
    parse_public_proof,
)
from duplexmodel.provenance import load_fixture
from duplexmodel.report import CONSTRUCTION_PATH, PUBLIC_INPUT_PATH, PUBLIC_PROOF_PATH
from duplexmodel.terms import canonical_json_text, exact_keys
from duplexmodel.transition import symbols


PRIVATE_PATH = "evaluation/duplex-sponge-transcript/cases/private-generation.json"


def _normalize_message(value: Any) -> object:
    if value is None:
        return None
    return symbols(value, where="generation-support prover message")


def proof_from_generation_support(value: Any) -> PublicProof:
    obj = exact_keys(
        value,
        {
            "schema",
            "classification",
            "salt_symbols",
            "prover_messages",
            "policy",
        },
        where="private generation input",
    )
    if obj["schema"] != "zkc.duplex-sponge-transcript.private-generation.v1":
        raise MalformedInput("private-generation schema differs")
    if obj["classification"] != "DeclassifiedToyGenerationSupportPoint":
        raise MalformedInput("private-generation classification differs")
    policy = exact_keys(
        obj["policy"],
        {
            "portable_identity",
            "public_report_digest",
            "uniformity_evidence",
            "allowed_use",
        },
        where="private generation policy",
    )
    if policy != {
        "portable_identity": False,
        "public_report_digest": False,
        "uniformity_evidence": False,
        "allowed_use": "fixture consistency and prefix-simulation comparison",
    }:
        raise MalformedInput("private-generation policy differs")
    salt = symbols(obj["salt_symbols"], where="generation-support salt symbols")
    if type(obj["prover_messages"]) is not list:
        raise MalformedInput("generation-support prover messages must be a list")
    messages = tuple(_normalize_message(value) for value in obj["prover_messages"])
    return PublicProof(salt, messages)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo-root", type=Path, default=Path(__file__).resolve().parents[2]
    )
    parser.add_argument(
        "--check-fixtures",
        action="store_true",
        help="reconstruct public proof bytes from private support and compare",
    )
    args = parser.parse_args()
    if not args.check_fixtures:
        print("generate.py requires --check-fixtures", file=sys.stderr)
        return 2
    try:
        construction = parse_construction(
            load_fixture(
                args.repo_root, CONSTRUCTION_PATH, role="generation-construction"
            ).value
        )
        inputs = parse_public_inputs(
            load_fixture(
                args.repo_root, PUBLIC_INPUT_PATH, role="generation-public-inputs"
            ).value
        )
        private = load_fixture(
            args.repo_root, PRIVATE_PATH, role="private-generation-support"
        )
        raw_generated = proof_from_generation_support(private.value)
        if len(raw_generated.salt) != construction.salt_length:
            raise MalformedInput("generation support has the wrong exact salt length")
        # Parsing the generated term checks every message type and codec.
        generated = parse_public_proof(
            raw_generated.to_term(), construction, inputs
        )
        frozen = parse_public_proof(
            load_fixture(args.repo_root, PUBLIC_PROOF_PATH, role="frozen-public-proof").value,
            construction,
            inputs,
        )
        if generated.proof != frozen.proof:
            raise MalformedInput("support-derived proof differs from frozen public proof")
        prefix = derive_generation_prefix_challenges(
            construction, inputs, generated
        )
        summary = {
            "schema": "zkc.duplex-sponge-transcript.generation-support-check.v1",
            "public_proof": {
                "schema": PUBLIC_PROOF_SCHEMA,
                "matches_frozen": True,
            },
            "simulated_prefix_challenges": [
                list(value) if type(value) is tuple else value for value in prefix
            ],
            "simulated_challenge_occurrences": ["challenge-1", "challenge-2"],
            "final_verifier_squeeze_simulated": False,
            "claim_boundaries": {
                "entropy_uniformity": False,
                "prover_necessity": False,
                "proof_generation": False,
                "portable_identity": False,
            },
        }
    except (DuplexModelError, OSError, TypeError, ValueError) as error:
        print(f"duplex generation-support failure: {error}", file=sys.stderr)
        return 1
    print(canonical_json_text(summary, pretty=True), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
