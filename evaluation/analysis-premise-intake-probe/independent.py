from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


FIELDS = {
    "root": {"format", "question", "subject", "protocol_outcome_lanes", "subject_outcome_partition", "premises", "cases"},
    "subject": {"core_id", "fresh_protocol_id", "family_id"},
    "premise": {"name", "kind", "coordinate", "bound_model_or_hypothesis", "source", "evidence_depth", "model_scope"},
    "coordinate": {"owner", "subject", "path"},
    "bound": {"form", "value"},
    "source": {"kind", "reference"},
    "case": {"regime", "oracle_model_id", "exact_subjects", "requirements", "bindings"},
    "requirement": {"slot", "kind", "coordinate"},
}
KINDS = {
    "FreshPublicCoinDistribution", "FiatShamirSamplerAdequacy", "FiatShamirOracleProcess",
    "ProviderOutcomeCarrierMap", "RelationPredicate", "WitnessType", "ProverPrivateState",
    "HonestCommit", "HonestRespond"
}
LANES = ["Accepted", "Rejected", "Aborted", "InterpretationFailed", "StrategyStopped", "OperationalNoncompletion"]
FRESH_PARTITION = ["Accepted", "Rejected", "Aborted", "StrategyStopped", "OperationalNoncompletion"]


def _bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("ascii")


def _hash(domain: str, value: Any) -> str:
    return hashlib.sha256(domain.encode("ascii") + b"\x00" + _bytes(value)).hexdigest()


def _require_fields(value: dict[str, Any], label: str) -> None:
    if set(value) != FIELDS[label]:
        raise ValueError(f"independent {label} fields differ")


def _premise_body(item: dict[str, Any]) -> dict[str, Any]:
    return {key: item[key] for key in (
        "kind", "coordinate", "bound_model_or_hypothesis", "source", "evidence_depth", "model_scope"
    )}


def _load(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    _require_fields(data, "root")
    _require_fields(data["subject"], "subject")
    if (data["format"] != "zkc.analysis-premise-intake-probe.v0"
            or data["protocol_outcome_lanes"] != LANES
            or data["subject_outcome_partition"] != FRESH_PARTITION):
        raise ValueError("independent root contract differs")
    names: set[str] = set()
    ids: set[str] = set()
    for item in data["premises"]:
        _require_fields(item, "premise")
        _require_fields(item["coordinate"], "coordinate")
        _require_fields(item["bound_model_or_hypothesis"], "bound")
        _require_fields(item["source"], "source")
        scope = item["model_scope"]
        scope_fields = {
            "FreshChallengeOnly": {"kind"},
            "OracleModelOnly": {"kind", "distribution_profile_id"},
            "ExactSubjectsOnly": {"kind", "exact_subjects"},
            "RebindRequired": {"kind"},
        }
        if not isinstance(scope, dict) or scope.get("kind") not in scope_fields or set(scope) != scope_fields[scope["kind"]]:
            raise ValueError("independent model scope differs")
        if item["kind"] not in KINDS or item["evidence_depth"] not in {"T1", "T2", "T3"}:
            raise ValueError("independent premise enum differs")
        if item["bound_model_or_hypothesis"]["form"] not in {"Model", "Hypothesis", "ProviderMap"}:
            raise ValueError("independent bound form differs")
        if scope["kind"] == "OracleModelOnly" and not scope["distribution_profile_id"]:
            raise ValueError("independent empty oracle-model scope")
        if scope["kind"] == "ExactSubjectsOnly" and (
            not scope["exact_subjects"] or scope["exact_subjects"] != sorted(set(scope["exact_subjects"]))
        ):
            raise ValueError("independent exact-subject scope differs")
        if item["kind"] == "ProviderOutcomeCarrierMap":
            value = item["bound_model_or_hypothesis"]["value"]
            if item["bound_model_or_hypothesis"]["form"] != "ProviderMap" or set(value) != {"carrier", "map"} or list(value["map"]) != FRESH_PARTITION:
                raise ValueError("independent provider map not total")
        premise_id = "premisev0:" + _hash("analysis.named-premise.v0", _premise_body(item))
        if item["name"] in names or premise_id in ids:
            raise ValueError("independent duplicate premise")
        item["_id"] = premise_id
        names.add(item["name"])
        ids.add(premise_id)
    for case in data["cases"].values():
        _require_fields(case, "case")
        if not case["oracle_model_id"] or not case["exact_subjects"] or case["exact_subjects"] != sorted(set(case["exact_subjects"])):
            raise ValueError("independent case scope differs")
        slots = []
        for requirement in case["requirements"]:
            _require_fields(requirement, "requirement")
            _require_fields(requirement["coordinate"], "coordinate")
            if requirement["kind"] not in KINDS or requirement["slot"] in slots:
                raise ValueError("independent invalid requirement")
            slots.append(requirement["slot"])
        if set(case["bindings"]) != set(slots) or not set(case["bindings"].values()) <= names:
            raise ValueError("independent default binding coverage differs")
    return data


def _scope_admits(item: dict[str, Any], case: dict[str, Any]) -> bool:
    scope = item["model_scope"]
    if scope["kind"] == "FreshChallengeOnly":
        return case["regime"] == "Fresh"
    if scope["kind"] == "OracleModelOnly":
        return case["oracle_model_id"] == scope["distribution_profile_id"]
    if scope["kind"] == "ExactSubjectsOnly":
        return case["exact_subjects"] == scope["exact_subjects"]
    return False


def _intake(data: dict[str, Any], case_name: str, supplied: dict[str, str] | None = None) -> dict[str, Any]:
    case = data["cases"][case_name]
    bindings = dict(case["bindings"] if supplied is None else supplied)
    requirements = {item["slot"]: item for item in case["requirements"]}
    missing = sorted(set(requirements) - set(bindings))
    if missing:
        return {"outcome": "CannotAnswer", "code": "API-C-MISSING-PREMISE", "missing": missing}
    extra = sorted(set(bindings) - set(requirements))
    if extra:
        return {"outcome": "Malformed", "code": "API-M-EXTRA-PREMISE", "extra": extra}
    by_name = {item["name"]: item for item in data["premises"]}
    selected = []
    for slot in sorted(requirements):
        if bindings[slot] not in by_name:
            return {"outcome": "CannotAnswer", "code": "API-C-PREMISE-NOT-IN-CATALOG", "slot": slot}
        item = by_name[bindings[slot]]
        wanted = requirements[slot]
        if item["kind"] != wanted["kind"] or item["coordinate"] != wanted["coordinate"]:
            return {"outcome": "Refused", "code": "API-R-PREMISE-COORDINATE", "slot": slot}
        if not _scope_admits(item, case):
            return {
                "outcome": "Refused", "code": "API-R-MODEL-SCOPE",
                "slot": slot, "scope": item["model_scope"]["kind"],
            }
        selected.append(item["_id"])
    selected.sort()
    identity = {
        "core_id": data["subject"]["core_id"], "case": case_name, "regime": case["regime"],
        "requirements": case["requirements"], "named_premise_ids": selected
    }
    return {
        "outcome": "Affirmative", "code": "API-A-INTAKE-ADMITTED",
        "named_premise_ids": selected, "hypothesis_set": selected,
        "judgment_id": "judgmentv0:" + _hash("analysis.premise-bearing-judgment.v0", identity)
    }


def evaluate(path: Path) -> dict[str, Any]:
    data = _load(path)
    complete = _intake(data, "schnorr-fresh-property")
    bindings = dict(data["cases"]["schnorr-fresh-property"]["bindings"])
    omissions = {}
    for slot in sorted(bindings):
        reduced = {key: value for key, value in bindings.items() if key != slot}
        result = _intake(data, "schnorr-fresh-property", reduced)
        omissions[slot] = result["outcome"] + "/" + result["code"]
    mutated = json.loads(json.dumps(data))
    for item in mutated["premises"]:
        if item["name"] == "fresh-public-coin-distribution":
            item["coordinate"]["path"] = "declarations[pir.public-coin-law][1]"
            item["_id"] = "premisev0:" + _hash("analysis.named-premise.v0", _premise_body(item))
    alternate = dict(bindings)
    alternate["outcome-carrier"] = "provider-outcome-tagged"
    extra = dict(bindings)
    extra["unexpected"] = "fresh-public-coin-distribution"
    scope_results = {}
    for scope_kind, case_name, mutation in (
        ("FreshChallengeOnly", "fresh-challenge", "case-regime"),
        ("OracleModelOnly", "fiat-shamir-challenge", "case-oracle"),
        ("ExactSubjectsOnly", "schnorr-fresh-property", "case-subjects"),
        ("RebindRequired", "fresh-challenge", "premise-rebind"),
    ):
        changed = json.loads(json.dumps(data))
        if mutation == "case-regime":
            changed["cases"][case_name]["regime"] = "FiatShamirClassicalRandomOracle"
        elif mutation == "case-oracle":
            changed["cases"][case_name]["oracle_model_id"] = "proposal:analysis.distribution:different"
        elif mutation == "case-subjects":
            changed["cases"][case_name]["exact_subjects"] = ["proposal:analysis.subject:different"]
        else:
            for item in changed["premises"]:
                if item["name"] == "fresh-public-coin-distribution":
                    item["model_scope"] = {"kind": "RebindRequired"}
                    item["_id"] = "premisev0:" + _hash("analysis.named-premise.v0", _premise_body(item))
        scope_results[scope_kind] = _intake(changed, case_name)
    return {
        "premise_ids": {item["name"]: item["_id"] for item in sorted(data["premises"], key=lambda row: row["name"])},
        "depth_counts": {depth: sum(item["evidence_depth"] == depth for item in data["premises"]) for depth in ("T1", "T2", "T3")},
        "complete": complete,
        "fresh": _intake(data, "fresh-challenge"),
        "fiat_shamir": _intake(data, "fiat-shamir-challenge"),
        "omissions": omissions,
        "wrong_coordinate": _intake(mutated, "schnorr-fresh-property"),
        "extra_key": _intake(data, "schnorr-fresh-property", extra),
        "scope_mismatches": scope_results,
        "alternate_provider": _intake(data, "schnorr-fresh-property", alternate),
        "catalog_digest": _hash("analysis.premise-catalog.v0", [{k: v for k, v in item.items() if k != "_id"} for item in data["premises"]]),
    }
