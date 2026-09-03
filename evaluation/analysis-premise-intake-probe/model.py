from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping


ROOT_FIELDS = {
    "format", "question", "subject", "protocol_outcome_lanes",
    "subject_outcome_partition", "premises", "cases"
}
SUBJECT_FIELDS = {"core_id", "fresh_protocol_id", "family_id"}
PREMISE_FIELDS = {
    "name", "kind", "coordinate", "bound_model_or_hypothesis", "source",
    "evidence_depth", "regime_transport"
}
COORDINATE_FIELDS = {"owner", "subject", "path"}
BOUND_FIELDS = {"form", "value"}
SOURCE_FIELDS = {"kind", "reference"}
TRANSPORT_FIELDS = {"mode", "regimes"}
CASE_FIELDS = {"regime", "requirements", "bindings"}
REQUIREMENT_FIELDS = {"slot", "kind", "coordinate"}

KINDS = {
    "FreshPublicCoinDistribution", "FiatShamirSamplerAdequacy",
    "FiatShamirOracleProcess", "ProviderOutcomeCarrierMap",
    "RelationPredicate", "WitnessType", "ProverPrivateState",
    "HonestCommit", "HonestRespond"
}
DEPTHS = {"T1", "T2", "T3"}
TRANSPORT_MODES = {"ExactRegimeOnly", "ExactCoordinateOnly", "RebindRequired"}
FORMS = {"Model", "Hypothesis", "ProviderMap"}
LANES = (
    "Accepted", "Rejected", "Aborted", "InterpretationFailed",
    "StrategyStopped", "OperationalNoncompletion"
)


class ProbeError(ValueError):
    pass


def canonical(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def digest(domain: str, value: Any) -> str:
    h = hashlib.sha256()
    h.update(domain.encode("ascii"))
    h.update(b"\x00")
    h.update(canonical(value))
    return h.hexdigest()


def _exact_fields(value: Mapping[str, Any], expected: set[str], label: str) -> None:
    if set(value) != expected:
        raise ProbeError(f"{label} fields differ")


@dataclass(frozen=True)
class NamedPremise:
    name: str
    kind: str
    coordinate: Mapping[str, str]
    bound_model_or_hypothesis: Mapping[str, Any]
    source: Mapping[str, str]
    evidence_depth: str
    regime_transport: Mapping[str, Any]

    @classmethod
    def parse(cls, raw: Mapping[str, Any], lanes: tuple[str, ...]) -> "NamedPremise":
        _exact_fields(raw, PREMISE_FIELDS, "premise")
        _exact_fields(raw["coordinate"], COORDINATE_FIELDS, "coordinate")
        _exact_fields(raw["bound_model_or_hypothesis"], BOUND_FIELDS, "bound")
        _exact_fields(raw["source"], SOURCE_FIELDS, "source")
        _exact_fields(raw["regime_transport"], TRANSPORT_FIELDS, "transport")
        if raw["kind"] not in KINDS:
            raise ProbeError("unknown premise kind")
        if raw["evidence_depth"] not in DEPTHS:
            raise ProbeError("unknown evidence depth")
        if raw["bound_model_or_hypothesis"]["form"] not in FORMS:
            raise ProbeError("unknown premise bound form")
        if raw["regime_transport"]["mode"] not in TRANSPORT_MODES:
            raise ProbeError("unknown transport mode")
        if not raw["regime_transport"]["regimes"]:
            raise ProbeError("empty transport regime set")
        if raw["kind"] == "ProviderOutcomeCarrierMap":
            bound = raw["bound_model_or_hypothesis"]
            if bound["form"] != "ProviderMap":
                raise ProbeError("provider map has wrong bound form")
            if set(bound["value"]) != {"carrier", "map"}:
                raise ProbeError("provider map fields differ")
            if tuple(bound["value"]["map"].keys()) != lanes:
                raise ProbeError("provider map is not total in lane order")
        return cls(**raw)

    def body(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "coordinate": dict(self.coordinate),
            "bound_model_or_hypothesis": dict(self.bound_model_or_hypothesis),
            "source": dict(self.source),
            "evidence_depth": self.evidence_depth,
            "regime_transport": dict(self.regime_transport),
        }

    @property
    def premise_id(self) -> str:
        return "premisev0:" + digest("analysis.named-premise.v0", self.body())


@dataclass(frozen=True)
class Catalog:
    raw: Mapping[str, Any]
    premises: Mapping[str, NamedPremise]
    lanes: tuple[str, ...]

    @classmethod
    def load(cls, path: Path) -> "Catalog":
        raw = json.loads(path.read_text(encoding="utf-8"))
        _exact_fields(raw, ROOT_FIELDS, "root")
        _exact_fields(raw["subject"], SUBJECT_FIELDS, "subject")
        if raw["format"] != "zkc.analysis-premise-intake-probe.v0":
            raise ProbeError("unsupported fixture format")
        all_lanes = tuple(raw["protocol_outcome_lanes"])
        if all_lanes != LANES:
            raise ProbeError("outcome lane partition differs")
        lanes = tuple(raw["subject_outcome_partition"])
        if lanes != tuple(lane for lane in LANES if lane != "InterpretationFailed"):
            raise ProbeError("subject outcome partition differs")
        premises: dict[str, NamedPremise] = {}
        ids: set[str] = set()
        for item in raw["premises"]:
            premise = NamedPremise.parse(item, lanes)
            if premise.name in premises or premise.premise_id in ids:
                raise ProbeError("duplicate premise")
            premises[premise.name] = premise
            ids.add(premise.premise_id)
        for case_name, case in raw["cases"].items():
            _exact_fields(case, CASE_FIELDS, f"case {case_name}")
            slots: set[str] = set()
            for requirement in case["requirements"]:
                _exact_fields(requirement, REQUIREMENT_FIELDS, "requirement")
                _exact_fields(requirement["coordinate"], COORDINATE_FIELDS, "requirement coordinate")
                if requirement["kind"] not in KINDS or requirement["slot"] in slots:
                    raise ProbeError("invalid requirement")
                slots.add(requirement["slot"])
            if set(case["bindings"]) != slots:
                raise ProbeError("default bindings do not exactly cover requirements")
            for name in case["bindings"].values():
                if name not in premises:
                    raise ProbeError("default binding names absent premise")
        return cls(raw=raw, premises=premises, lanes=lanes)


def intake(
    catalog: Catalog,
    case_name: str,
    bindings: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    case = catalog.raw["cases"][case_name]
    supplied = dict(case["bindings"] if bindings is None else bindings)
    requirements = {r["slot"]: r for r in case["requirements"]}
    missing = sorted(set(requirements) - set(supplied))
    if missing:
        return {"outcome": "CannotAnswer", "code": "API-C-MISSING-PREMISE", "missing": missing}
    extra = sorted(set(supplied) - set(requirements))
    if extra:
        return {"outcome": "Refused", "code": "API-R-EXTRA-PREMISE", "extra": extra}
    selected: list[NamedPremise] = []
    for slot in sorted(requirements):
        name = supplied[slot]
        if name not in catalog.premises:
            return {"outcome": "CannotAnswer", "code": "API-C-PREMISE-NOT-IN-CATALOG", "slot": slot}
        premise = catalog.premises[name]
        requirement = requirements[slot]
        if premise.kind != requirement["kind"] or dict(premise.coordinate) != requirement["coordinate"]:
            return {"outcome": "Refused", "code": "API-R-PREMISE-COORDINATE", "slot": slot}
        selected.append(premise)
    premise_ids = sorted(p.premise_id for p in selected)
    identity_body = {
        "core_id": catalog.raw["subject"]["core_id"],
        "case": case_name,
        "regime": case["regime"],
        "requirements": case["requirements"],
        "named_premise_ids": premise_ids,
    }
    return {
        "outcome": "Affirmative",
        "code": "API-A-INTAKE-ADMITTED",
        "named_premise_ids": premise_ids,
        "hypothesis_set": premise_ids,
        "judgment_id": "judgmentv0:" + digest("analysis.premise-bearing-judgment.v0", identity_body),
    }


def evaluate(path: Path) -> dict[str, Any]:
    catalog = Catalog.load(path)
    complete = intake(catalog, "schnorr-fresh-property")
    fresh = intake(catalog, "fresh-challenge")
    fiat_shamir = intake(catalog, "fiat-shamir-challenge")

    omission_results: dict[str, str] = {}
    bindings = dict(catalog.raw["cases"]["schnorr-fresh-property"]["bindings"])
    for slot in sorted(bindings):
        reduced = dict(bindings)
        del reduced[slot]
        result = intake(catalog, "schnorr-fresh-property", reduced)
        omission_results[slot] = result["outcome"] + "/" + result["code"]

    mutated = json.loads(json.dumps(catalog.raw))
    for premise in mutated["premises"]:
        if premise["name"] == "fresh-public-coin-distribution":
            premise["coordinate"]["path"] = "declarations[pir.public-coin-law][1]"
    raw_catalog = Catalog(
        raw=mutated,
        premises={
            p.name: p
            for p in (
                NamedPremise.parse(item, tuple(mutated["subject_outcome_partition"]))
                for item in mutated["premises"]
            )
        },
        lanes=tuple(mutated["subject_outcome_partition"]),
    )
    wrong_coordinate = intake(raw_catalog, "schnorr-fresh-property")

    alternate_bindings = dict(bindings)
    alternate_bindings["outcome-carrier"] = "provider-outcome-tagged"
    alternate_provider = intake(catalog, "schnorr-fresh-property", alternate_bindings)

    return {
        "premise_ids": {name: p.premise_id for name, p in sorted(catalog.premises.items())},
        "depth_counts": {
            depth: sum(p.evidence_depth == depth for p in catalog.premises.values())
            for depth in sorted(DEPTHS)
        },
        "complete": complete,
        "fresh": fresh,
        "fiat_shamir": fiat_shamir,
        "omissions": omission_results,
        "wrong_coordinate": wrong_coordinate,
        "alternate_provider": alternate_provider,
        "catalog_digest": digest("analysis.premise-catalog.v0", catalog.raw["premises"]),
    }
