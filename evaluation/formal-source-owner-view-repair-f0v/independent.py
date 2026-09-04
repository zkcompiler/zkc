"""Cold inspection of the migrated owner-view publication topology.

This module imports neither the F0-V1 reference model nor the Foundation-backed
publication compiler. It repeats the selected inventory and uses the cold
publication implementation to reconstruct the authored profile bodies.
"""

from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
COLD_MODEL = ROOT / "evaluation" / "semantic-profile-publication" / "independent.py"


def _load_module(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


cold = _load_module("_zkc_f0v_cold_publication", COLD_MODEL)


class TopologyError(ValueError):
    """The cold inventory rejects the proposed repair topology."""


REVISED_PROFILES = (
    "interaction",
    "canonical-framed-fiat-shamir",
    "duplex-sponge-fiat-shamir",
    "public-setup",
    "interface-plan",
    "endpoint-source-view",
)
EXPECTED_REVISIONS = {
    "interaction": 3,
    "canonical-framed-fiat-shamir": 4,
    "duplex-sponge-fiat-shamir": 3,
    "public-setup": 2,
    "interface-plan": 2,
    "endpoint-source-view": 2,
}
ROTATED_PROFILES = (
    "analysis-afk-theorem-source-validation",
    "analysis-afk-transport",
    "analysis-cryptographic-property",
    "analysis-incremental-composition",
    "analysis-incremental-composition-source-validation",
    "canonical-framed-fiat-shamir",
    "commitment-opening",
    "duplex-sponge-fiat-shamir",
    "endpoint-source-view",
    "interaction",
    "interface-plan",
    "oir-endpoint-graph",
    "oir-projection-relation",
    "oracle-commitment",
    "public-setup",
    "relations",
    "verifier-derived-query-plan",
)
STABLE_PROFILES = ("analysis-kernel",)
BASELINE_IDENTITIES = ROOT / "evaluation/formal-source-owner-view-repair-f0v/baseline-identities.json"
SCHEMA_ORDER = (
    "public-binding-view-v0",
    "strategy-decision-view-v0",
    "public-coin-view-v0",
    "effect-view-v0",
    "claim-reduction-view-v0",
    "execution-view-v0",
)
SCHEMA_OWNER = {
    "public-binding-view-v0": "pir.interactive-core",
    "strategy-decision-view-v0": "pir.interactive-core",
    "public-coin-view-v0": "pir.interactive-core",
    "effect-view-v0": "pir.interactive-core",
    "claim-reduction-view-v0": "pir.interactive-core",
    "execution-view-v0": "pir.protocol",
}
SCHEMA_TAG = {
    "public-binding-view-v0": "PublicBindingView",
    "strategy-decision-view-v0": "StrategyDecisionView",
    "public-coin-view-v0": "PublicCoinView",
    "effect-view-v0": "EffectView",
    "claim-reduction-view-v0": "ClaimReductionView",
    "execution-view-v0": "ExecutionView",
}
SCHEMA_LAW = {
    "public-binding-view-v0": ("core-admission-v0",),
    "strategy-decision-view-v0": (
        "core-admission-v0",
        "prover-view-formation-v0",
    ),
    "public-coin-view-v0": (
        "core-admission-v0",
        "public-coin-eligibility-v0",
    ),
    "effect-view-v0": ("core-admission-v0",),
    "claim-reduction-view-v0": ("core-admission-v0",),
    "execution-view-v0": (
        "core-admission-v0",
        "execution-and-replay-v0",
        "protocol-outcome-partition-v0",
        "run-view-issuance-v0",
        "visible-history-v0",
        "replay-qualification-v0",
    ),
}
LOCAL_COMPILER = {
    "pir.source-binding-payload": "source-binding-payload-body-v0",
    "pir.source-capability-requirement": ("source-capability-requirement-body-v0"),
    "pir.source-no-policy": "source-no-policy-body-v0",
    "pir.source-policy-closure": "source-policy-closure-body-v0",
}
COMMON_COMPILER = {
    "pir.source-consumer": "source-consumer-role-body-v0",
    "pir.source-purpose": "source-purpose-role-body-v0",
}


def _reference(profile: str, kind: str, name: str) -> dict[str, str]:
    return {"profile": profile, "kind": kind, "name": name}


def _local_selector(profile: str, kind: str) -> str:
    prefixes = {
        "interaction": "PIR",
        "canonical-framed-fiat-shamir": "CanonicalFramed",
        "duplex-sponge-fiat-shamir": "Duplex",
        "public-setup": "PublicSetup",
        "interface-plan": "InterfacePlan",
        "endpoint-source-view": "Endpoint",
    }
    suffixes = {
        "pir.source-binding-payload": "SourceBindingPayloadBody(x) =",
        "pir.source-capability-requirement": "SourceCapabilityRequirementBody(x) =",
        "pir.source-no-policy": "SourceNoPolicyBody(x) =",
        "pir.source-policy-closure": "SourcePolicyClosureBody(x) =",
    }
    return prefixes[profile] + suffixes[kind]


def _schema_selector(name: str) -> str:
    return f"StaticViewSchema({SCHEMA_TAG[name]}) = {{"


def _schema_dependencies(name: str) -> list[dict[str, str]]:
    rows = [
        _reference("self", "pir.body-compiler", "static-view-body-v0"),
        _reference(
            "self",
            "pir.semantic-law",
            "static-view-schema-resolution-v0",
        ),
    ]
    rows.extend(_reference("self", "pir.semantic-law", law) for law in SCHEMA_LAW[name])
    return rows


def _definitions(
    manifest: Mapping[str, Any],
) -> dict[tuple[str, str], Mapping[str, Any]]:
    return {(row["kind"], row["name"]): row for row in manifest["definitions"]}


def _routes(manifest: Mapping[str, Any]) -> dict[str, tuple[str, str]]:
    return {
        row["kind"]: (
            row["body_compiler"]["profile"],
            row["body_compiler"]["name"],
        )
        for row in manifest["subjects"]
        if row["kind"].startswith("pir.source-")
    }


def _wanted_routes(profile: str) -> dict[str, tuple[str, str]]:
    result = {kind: ("self", name) for kind, name in LOCAL_COMPILER.items()}
    result.update(
        {
            kind: (
                "self" if profile == "interaction" else "interaction",
                name,
            )
            for kind, name in COMMON_COMPILER.items()
        }
    )
    return result


def _validate(profiles: Mapping[str, Any]) -> None:
    for key in REVISED_PROFILES:
        manifest = profiles[key].manifest
        if manifest["revision"] != EXPECTED_REVISIONS[key]:
            raise TopologyError("a changed source profile has the wrong revision")
        if _routes(manifest) != _wanted_routes(key):
            raise TopologyError("a repaired profile has a wrong source route")
        declarations = _definitions(manifest)
        for kind, name in LOCAL_COMPILER.items():
            row = declarations.get(("pir.body-compiler", name))
            if row is None or row["selector"] != _local_selector(key, kind):
                raise TopologyError("a profile lacks one closed local body compiler")
        if any(
            row["name"] == "source-authority-envelope-body-v0"
            for row in manifest["definitions"]
        ):
            raise TopologyError("the catch-all body compiler remains published")

    interaction = profiles["interaction"].manifest
    declarations = _definitions(interaction)
    schemas = [
        row
        for row in interaction["definitions"]
        if row["kind"] == "pir.static-view-schema"
    ]
    if tuple(row["name"] for row in schemas) != SCHEMA_ORDER:
        raise TopologyError("the owner schema inventory is not exact")
    for row in schemas:
        name = row["name"]
        if row["selector"] != _schema_selector(name):
            raise TopologyError("an owner schema selector changed")
        if row["dependencies"] != _schema_dependencies(name):
            raise TopologyError("an owner schema dependency set changed")
    source_body = profiles["interaction"].body_bytes
    for name in SCHEMA_ORDER:
        tag = SCHEMA_TAG[name]
        owner = (
            f"ProtocolView(ProtocolId, {tag})"
            if name == "execution-view-v0"
            else f"CoreView(CoreId, {tag})"
        )
        if source_body.count(f"owner: {owner},".encode("ascii")) != 1:
            raise TopologyError("an owner schema owner changed")
    issuance = declarations[("pir.semantic-law", "static-view-issuance-v0")]
    if issuance["dependencies"] != [
        _reference("self", "pir.static-view-schema", name) for name in SCHEMA_ORDER
    ]:
        raise TopologyError("issuance does not authenticate the exact schema set")
    role_selectors = {
        "source-consumer-role-body-v0": "PIRSourceConsumerRoleBody(x) = R",
        "source-purpose-role-body-v0": "PIRSourcePurposeRoleBody(x) = R",
    }
    for name, selector in role_selectors.items():
        row = declarations.get(("pir.body-compiler", name))
        if row is None or row["selector"] != selector:
            raise TopologyError("the common role-body split is incomplete")


def _summary(profile: Any) -> dict[str, Any]:
    return {
        "body_sha256": hashlib.sha256(profile.body_bytes).hexdigest(),
        "profile_ref_hex": profile.identifier.ref().hex(),
        "direct_imports": list(profile.direct_import_keys),
        "declarations": {
            f"{kind}/{name}": ordinal
            for (kind, name), ordinal in sorted(profile.declaration_index.items())
        },
    }


def observe(candidate: Any | None = None) -> dict[str, Any]:
    repaired = (
        cold.compile_repository()
        if candidate is None
        else cold.compile_repository(
            manifest_overrides=candidate.manifests,
            page_overrides=candidate.pages,
        )
    )
    _validate(repaired.profiles)
    baseline = json.loads(BASELINE_IDENTITIES.read_text(encoding="utf-8"))["profiles"]
    rotated = tuple(
        sorted(
            key
            for key in cold.KEYS
            if baseline[key] != repaired.profiles[key].identifier.digest.hex()
        )
    )
    stable = tuple(sorted(set(cold.KEYS) - set(rotated)))
    if rotated != ROTATED_PROFILES:
        raise TopologyError("cold reconstruction derived a wrong rotation cone")
    if stable != STABLE_PROFILES:
        raise TopologyError("cold reconstruction derived a wrong stable complement")

    interaction = repaired.profiles["interaction"].manifest
    return {
        "rotated_profiles": list(rotated),
        "stable_profiles": list(stable),
        "schema_entries": [
            row["name"]
            for row in interaction["definitions"]
            if row["kind"] == "pir.static-view-schema"
        ],
        "revisions": {
            key: repaired.profiles[key].manifest["revision"] for key in REVISED_PROFILES
        },
        "source_routes": {
            key: {
                kind: {"profile": route[0], "compiler": route[1]}
                for kind, route in sorted(
                    _routes(repaired.profiles[key].manifest).items()
                )
            }
            for key in REVISED_PROFILES
        },
        "profiles": {key: _summary(repaired.profiles[key]) for key in cold.KEYS},
        "interaction_before": baseline["interaction"],
        "interaction_after": repaired.profiles["interaction"].identifier.digest.hex(),
    }
