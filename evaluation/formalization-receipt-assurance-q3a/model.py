#!/usr/bin/env python3
"""Direct model for the Q3-A formalization-receipt assurance audit.

This module deliberately does not import the production receipt driver.  It
reads the public registry, the frozen external observation, and the exact
source files that define the current reading path.  The black-box path lives
in ``independent.py``.
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Iterator, Mapping


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
SIGNATURE = ROOT / "registry" / "soundness-signature.json"
UPSTREAMS = ROOT / "registry" / "upstreams.json"
DRIVER = ROOT / "test" / "Soundness" / "Inputs" / "formalization_receipts.py"
WORKFLOW = ROOT / ".github" / "workflows" / "lean-reading.yml"
OBSERVATION = HERE / "live-observation.json"

ARKLIB = "https://github.com/Verified-zkEVM/ArkLib"
OBSERVATION_SCHEMA = "zkc.formalization-receipt-assurance-q3a.observation.v0"


class AuditFailure(RuntimeError):
    """The frozen audit input is malformed or has drifted."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


def require(condition: bool, detail: str) -> None:
    if not condition:
        raise AuditFailure(detail)


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditFailure(f"cannot read {path.relative_to(ROOT)}") from error


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def canonical_digest(value: Any) -> str:
    encoded = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")
    return sha256_bytes(encoded)


def receipts(signature: Mapping[str, Any]) -> Iterator[tuple[str, int, Mapping[str, Any]]]:
    for rule, annotation in sorted(signature["annotations"].items()):
        for index, receipt in enumerate(annotation.get("formalization", [])):
            yield rule, index, receipt


def inventory(signature: Mapping[str, Any], pin: str) -> dict[str, Any]:
    all_receipts = list(receipts(signature))
    checkable = [
        (rule, index, receipt)
        for rule, index, receipt in all_receipts
        if receipt.get("repository") == ARKLIB
        and receipt.get("revision") == pin
        and bool(receipt.get("statement"))
    ]
    outside = [item for item in all_receipts if item not in checkable]
    states: dict[str, int] = {}
    for _, _, receipt in all_receipts:
        state = str(receipt.get("state", ""))
        states[state] = states.get(state, 0) + 1
    return {
        "total": len(all_receipts),
        "checkable": len(checkable),
        "outside": len(outside),
        "state_counts": dict(sorted(states.items())),
        "checkable_declarations": [
            receipt["declaration"] for _, _, receipt in checkable
        ],
        "outside_declarations": [receipt["declaration"] for _, _, receipt in outside],
    }


def validate_observation(
    observation: Mapping[str, Any], signature: Mapping[str, Any], pin: str
) -> dict[str, Any]:
    require(observation.get("schema") == OBSERVATION_SCHEMA, "observation schema drift")
    body = dict(observation)
    recorded_id = body.pop("observation_body_sha256", None)
    require(recorded_id == canonical_digest(body), "observation body digest drift")

    source_files = {
        "driver": DRIVER,
        "signature": SIGNATURE,
        "upstreams": UPSTREAMS,
        "workflow": WORKFLOW,
    }
    recorded_sources = observation.get("zkc_sources", {})
    for name, path in source_files.items():
        require(
            recorded_sources.get(name, {}).get("sha256") == sha256_file(path),
            f"{name} source drift",
        )

    arklib = observation.get("arklib_environment", {})
    require(arklib.get("repository") == ARKLIB, "ArkLib repository drift")
    require(arklib.get("revision") == pin, "ArkLib revision drift")
    require(arklib.get("clean_worktree") is True, "observation was not clean")

    current_inventory = inventory(signature, pin)
    reading = observation.get("reading", {})
    require(reading.get("exit_status") == 0, "external reading did not succeed")
    require(reading.get("checkable") == current_inventory["checkable"], "checkable count drift")
    require(reading.get("outside_checkout") == current_inventory["outside"], "outside count drift")
    require(reading.get("agree") == current_inventory["checkable"], "agreement count drift")
    observed_declarations = [entry.get("declaration") for entry in reading.get("declarations", [])]
    require(
        observed_declarations == current_inventory["checkable_declarations"],
        "observed declaration order drift",
    )
    require(
        all(entry.get("statement") == "agree" and entry.get("axioms") == "agree"
            for entry in reading.get("declarations", [])),
        "observation contains a non-agreement",
    )
    return current_inventory


def direct_findings() -> tuple[list[Finding], dict[str, Any]]:
    signature = read_json(SIGNATURE)
    upstreams = read_json(UPSTREAMS)
    observation = read_json(OBSERVATION)
    pin = upstreams["upstreams"]["arklib"]["revision"]
    measured = validate_observation(observation, signature, pin)

    driver_source = DRIVER.read_text(encoding="utf-8")
    workflow_source = WORKFLOW.read_text(encoding="utf-8")
    require("#print axioms" in driver_source, "driver no longer reads axiom profiles")
    require("recorded_statement != printed_statement" in driver_source,
            "driver no longer compares statements")
    require("git\", \"-C\", str(checkout), \"rev-parse\", \"HEAD\"" in driver_source,
            "driver pin check changed")
    require("status\", \"--porcelain" not in driver_source,
            "driver now checks checkout cleanliness; update the audit")
    require("actions/upload-artifact" not in workflow_source,
            "workflow now preserves a result artifact; update the audit")
    require("lean4checker" not in workflow_source and "lean4checker" not in driver_source,
            "independent kernel replay was added; update the audit")

    findings = [
        Finding("exact-predecessor-sources-pinned", "Affirmative", "Q3A-A-SOURCE-PINS"),
        Finding("ten-receipt-inventory", "Affirmative", "Q3A-A-INVENTORY"),
        Finding("six-arklib-four-outside-partition", "Affirmative", "Q3A-A-CHECKABILITY-PARTITION"),
        Finding("clean-exact-pin-reading-observed", "Affirmative", "Q3A-A-LIVE-READING"),
        Finding("six-printed-statements-reproduced", "Affirmative", "Q3A-A-STATEMENT-READING"),
        Finding("six-axiom-sets-reproduced", "Affirmative", "Q3A-A-AXIOM-READING"),
        Finding("one-standard-axiom-only-declaration", "Affirmative", "Q3A-A-NO-SORRY-DECLARATION"),
        Finding("driver-and-direct-auditor-separated", "Affirmative", "Q3A-A-PATH-SEPARATION"),
        Finding("four-external-receipts-authenticated", "CannotAnswer", "Q3A-C-EXTERNAL-RECEIPTS"),
        Finding("durable-q3-result-envelope", "CannotAnswer", "Q3A-C-RESULT-ENVELOPE"),
        Finding("checker-toolchain-dependency-result-binding", "CannotAnswer", "Q3A-C-ENVIRONMENT-BINDING"),
        Finding("driver-enforced-clean-checkout", "CannotAnswer", "Q3A-C-CHECKOUT-CLEANLINESS"),
        Finding("independent-kernel-replay", "CannotAnswer", "Q3A-C-KERNEL-REPLAY"),
        Finding("pir-subject-to-theorem-correspondence", "CannotAnswer", "Q3A-C-SUBJECT-CORRESPONDENCE"),
        Finding("qualified-property-consumption", "CannotAnswer", "Q3A-C-PROPERTY-CONSUMPTION"),
    ]
    return findings, {
        **measured,
        "arklib_revision": pin,
        "observation_body_sha256": observation["observation_body_sha256"],
    }
