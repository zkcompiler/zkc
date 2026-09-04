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
    "evidence_depth", "model_scope"
}
COORDINATE_FIELDS = {"owner", "subject", "path"}
BOUND_FIELDS = {"form", "value"}
SOURCE_FIELDS = {"kind", "reference"}
CASE_FIELDS = {"regime", "oracle_model_id", "exact_subjects", "requirements", "bindings"}
REQUIREMENT_FIELDS = {"slot", "kind", "coordinate"}

KINDS = {
    "FreshPublicCoinDistribution", "FiatShamirSamplerAdequacy",
    "FiatShamirOracleProcess", "ProviderOutcomeCarrierMap",
    "OperationalCompletion",
    "RelationPredicate", "WitnessType", "ProverPrivateState",
    "HonestCommit", "HonestRespond"
}
DEPTHS = {"T1", "T2", "T3"}
MODEL_SCOPE_KINDS = {
    "FreshChallengeOnly", "OracleModelOnly", "ExactSubjectsOnly", "RebindRequired"
}
FORMS = {"Model", "Hypothesis", "ProviderMap"}
OWNER_DECLARATIONS = {
    "FreshPublicCoinDistribution": ("FreshSamplingHypothesis", 2),
    "FiatShamirSamplerAdequacy": ("FamilySamplerAdequacyHypothesis", 3),
    "FiatShamirOracleProcess": ("FamilyOracleProcessHypothesis", 2),
    "OperationalCompletion": ("OperationalCompletionHypothesis", 2),
    "RelationPredicate": ("RelationPredicateBindingLaw", 2),
    "WitnessType": ("WitnessTypeBindingLaw", 2),
    "ProverPrivateState": ("ProverPrivateStateBindingLaw", 2),
    "HonestCommit": ("HonestCommitHypothesis", 1),
    "HonestRespond": ("HonestRespondHypothesis", 1),
}
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
class ProviderDeclaration:
    system: str
    source_pin: str
    toolchain: str
    modelled_lanes: tuple[str, ...]

    @classmethod
    def parse(cls, raw: Mapping[str, Any]) -> "ProviderDeclaration":
        _exact_fields(
            raw,
            {"system", "source_pin", "toolchain", "modelled_lanes"},
            "provider declaration",
        )
        lanes = tuple(raw["modelled_lanes"])
        if (
            not raw["system"]
            or not raw["toolchain"]
            or len(raw["source_pin"]) != 64
            or any(character not in "0123456789abcdef" for character in raw["source_pin"])
            or lanes != tuple(sorted(set(lanes)))
            or not set(lanes) <= set(LANES)
        ):
            raise ProbeError("provider declaration is not canonical")
        return cls(
            raw["system"], raw["source_pin"], raw["toolchain"], lanes
        )

    def body(self) -> dict[str, Any]:
        return {
            "system": self.system,
            "source_pin": self.source_pin,
            "toolchain": self.toolchain,
            "modelled_lanes": list(self.modelled_lanes),
        }


@dataclass(frozen=True)
class ProviderLaneImage:
    form: str
    value: Any = None

    @classmethod
    def parse(cls, raw: Mapping[str, Any]) -> "ProviderLaneImage":
        if raw.get("form") == "Image":
            _exact_fields(raw, {"form", "value"}, "provider lane image")
            return cls("Image", raw["value"])
        if raw.get("form") == "Unmodelled":
            _exact_fields(raw, {"form"}, "provider lane image")
            return cls("Unmodelled")
        raise ProbeError("unknown provider lane image")


@dataclass(frozen=True)
class NamedPremise:
    name: str
    kind: str
    coordinate: Mapping[str, str]
    bound_model_or_hypothesis: Mapping[str, Any]
    source: Mapping[str, Any]
    evidence_depth: str
    model_scope: Mapping[str, Any]

    @classmethod
    def parse(cls, raw: Mapping[str, Any], lanes: tuple[str, ...]) -> "NamedPremise":
        _exact_fields(raw, PREMISE_FIELDS, "premise")
        _exact_fields(raw["coordinate"], COORDINATE_FIELDS, "coordinate")
        _exact_fields(raw["bound_model_or_hypothesis"], BOUND_FIELDS, "bound")
        _exact_fields(raw["source"], SOURCE_FIELDS, "source")
        scope = raw["model_scope"]
        if not isinstance(scope, dict) or scope.get("kind") not in MODEL_SCOPE_KINDS:
            raise ProbeError("unknown model scope")
        scope_fields = {
            "FreshChallengeOnly": {"kind"},
            "OracleModelOnly": {"kind", "distribution_profile_id"},
            "ExactSubjectsOnly": {"kind", "exact_subjects"},
            "RebindRequired": {"kind"},
        }[scope["kind"]]
        _exact_fields(scope, scope_fields, "model scope")
        if raw["kind"] not in KINDS:
            raise ProbeError("unknown premise kind")
        if raw["evidence_depth"] not in DEPTHS:
            raise ProbeError("unknown evidence depth")
        if raw["bound_model_or_hypothesis"]["form"] not in FORMS:
            raise ProbeError("unknown premise bound form")
        if raw["kind"] != "ProviderOutcomeCarrierMap":
            value = raw["bound_model_or_hypothesis"]["value"]
            if not isinstance(value, dict) or set(value) != {
                "law_ref", "canonical_arguments", "statement"
            }:
                raise ProbeError("owner declaration binding fields differ")
            law_ref, arity = OWNER_DECLARATIONS[raw["kind"]]
            arguments = value["canonical_arguments"]
            if (
                value["law_ref"] != law_ref
                or not isinstance(arguments, list)
                or len(arguments) != arity
                or arguments[0] != "coordinate"
                or not value["statement"]
            ):
                raise ProbeError("hypothesis reference names no owner declaration")
            if raw["kind"] == "FreshPublicCoinDistribution" and arguments[1] != (
                "proposal:analysis.distribution:fresh-uniform"
            ):
                raise ProbeError("Fresh distribution argument differs")
            if raw["kind"] in {
                "FiatShamirSamplerAdequacy", "FiatShamirOracleProcess"
            } and arguments[1] != raw["model_scope"].get("distribution_profile_id"):
                raise ProbeError("oracle distribution argument differs")
            if raw["kind"] in {
                "RelationPredicate", "WitnessType", "ProverPrivateState"
            } and arguments[1] != raw["coordinate"]["subject"]:
                raise ProbeError("model-binding subject argument differs")
        if scope["kind"] == "OracleModelOnly" and not scope["distribution_profile_id"]:
            raise ProbeError("empty oracle-model scope")
        if scope["kind"] == "ExactSubjectsOnly":
            subjects = scope["exact_subjects"]
            if not subjects or subjects != sorted(set(subjects)):
                raise ProbeError("noncanonical exact-subject scope")
        if raw["kind"] == "ProviderOutcomeCarrierMap":
            bound = raw["bound_model_or_hypothesis"]
            if bound["form"] != "ProviderMap":
                raise ProbeError("provider map has wrong bound form")
            if set(bound["value"]) != {"provider", "carrier", "map"}:
                raise ProbeError("provider map fields differ")
            provider = ProviderDeclaration.parse(bound["value"]["provider"])
            if tuple(bound["value"]["map"].keys()) != lanes:
                raise ProbeError("provider map is not total in lane order")
            images = {
                lane: ProviderLaneImage.parse(image)
                for lane, image in bound["value"]["map"].items()
            }
            if any(
                (images[lane].form == "Image") != (lane in provider.modelled_lanes)
                for lane in lanes
            ):
                raise ProbeError("provider lane image disagrees with modelled lanes")
            if bound["value"]["carrier"] == "Bool" and any(
                type(image.value) is not bool
                for image in images.values()
                if image.form == "Image"
            ):
                raise ProbeError("Boolean provider map has a non-Boolean image")
            if (
                raw["source"]["kind"] != "ProviderDeclarationSource"
                or raw["source"]["reference"] != provider.body()
            ):
                raise ProbeError("provider-map source names another declaration")
        if raw["kind"] == "OperationalCompletion":
            if raw["bound_model_or_hypothesis"]["form"] != "Hypothesis":
                raise ProbeError("operational completion has wrong bound form")
            if raw["source"]["kind"] != "ProviderDeclarationSource":
                raise ProbeError("operational completion has wrong source form")
            provider = ProviderDeclaration.parse(raw["source"]["reference"])
            if raw["bound_model_or_hypothesis"]["value"]["canonical_arguments"][1] != provider.body():
                raise ProbeError("operational completion provider argument differs")
        return cls(**raw)

    def body(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "coordinate": dict(self.coordinate),
            "bound_model_or_hypothesis": dict(self.bound_model_or_hypothesis),
            "source": dict(self.source),
            "evidence_depth": self.evidence_depth,
            "model_scope": dict(self.model_scope),
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
            if not case["oracle_model_id"]:
                raise ProbeError("empty case oracle model")
            if not case["exact_subjects"] or case["exact_subjects"] != sorted(set(case["exact_subjects"])):
                raise ProbeError("noncanonical case subjects")
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

    @classmethod
    def from_raw(cls, raw: Mapping[str, Any]) -> "Catalog":
        lanes = tuple(raw["subject_outcome_partition"])
        premises = {
            premise.name: premise
            for premise in (NamedPremise.parse(item, lanes) for item in raw["premises"])
        }
        return cls(raw=raw, premises=premises, lanes=lanes)


def _scope_admits(premise: NamedPremise, case: Mapping[str, Any]) -> bool:
    scope = premise.model_scope
    kind = scope["kind"]
    if kind == "FreshChallengeOnly":
        return case["regime"] == "Fresh"
    if kind == "OracleModelOnly":
        return case["oracle_model_id"] == scope["distribution_profile_id"]
    if kind == "ExactSubjectsOnly":
        return case["exact_subjects"] == scope["exact_subjects"]
    return False


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
        return {"outcome": "Malformed", "code": "API-M-EXTRA-PREMISE", "extra": extra}
    selected: list[NamedPremise] = []
    for slot in sorted(requirements):
        name = supplied[slot]
        if name not in catalog.premises:
            return {"outcome": "CannotAnswer", "code": "API-C-PREMISE-NOT-IN-CATALOG", "slot": slot}
        premise = catalog.premises[name]
        requirement = requirements[slot]
        if premise.kind != requirement["kind"] or dict(premise.coordinate) != requirement["coordinate"]:
            return {"outcome": "Refused", "code": "API-R-PREMISE-COORDINATE", "slot": slot}
        if not _scope_admits(premise, case):
            return {
                "outcome": "Refused", "code": "API-R-MODEL-SCOPE",
                "slot": slot, "scope": premise.model_scope["kind"],
            }
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
    provider_map = intake(catalog, "provider-outcome-map")
    provider_completion = intake(catalog, "provider-completeness")

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

    extra_bindings = dict(bindings)
    extra_bindings["unexpected"] = "fresh-public-coin-distribution"
    extra_key = intake(catalog, "schnorr-fresh-property", extra_bindings)

    scope_results: dict[str, dict[str, Any]] = {}
    scope_mutations = {
        "FreshChallengeOnly": ("fresh-challenge", "case-regime"),
        "OracleModelOnly": ("fiat-shamir-challenge", "case-oracle"),
        "ExactSubjectsOnly": ("schnorr-fresh-property", "case-subjects"),
        "RebindRequired": ("fresh-challenge", "premise-rebind"),
    }
    for scope_kind, (case_name, mutation) in scope_mutations.items():
        changed = json.loads(json.dumps(catalog.raw))
        if mutation == "case-regime":
            changed["cases"][case_name]["regime"] = "FiatShamirClassicalRandomOracle"
        elif mutation == "case-oracle":
            changed["cases"][case_name]["oracle_model_id"] = "proposal:analysis.distribution:different"
        elif mutation == "case-subjects":
            changed["cases"][case_name]["exact_subjects"] = ["proposal:analysis.subject:different"]
        else:
            for premise in changed["premises"]:
                if premise["name"] == "fresh-public-coin-distribution":
                    premise["model_scope"] = {"kind": "RebindRequired"}
        scope_results[scope_kind] = intake(Catalog.from_raw(changed), case_name)

    provider_bindings = dict(catalog.raw["cases"]["provider-outcome-map"]["bindings"])
    alternate_bindings = dict(provider_bindings)
    alternate_bindings["outcome-carrier"] = "provider-outcome-tagged"
    alternate_provider = intake(catalog, "provider-outcome-map", alternate_bindings)

    collapsed = json.loads(json.dumps(catalog.raw))
    for premise in collapsed["premises"]:
        if premise["name"] == "provider-outcome-bool":
            premise["bound_model_or_hypothesis"]["value"]["map"][
                "OperationalNoncompletion"
            ] = {"form": "Image", "value": False}
    try:
        Catalog.from_raw(collapsed)
    except ProbeError:
        bool_noncompletion_collapse = {
            "outcome": "Malformed",
            "code": "API-M-PROVIDER-LANE-IMAGE",
        }
    else:  # pragma: no cover - required negative control
        bool_noncompletion_collapse = {
            "outcome": "Affirmative",
            "code": "API-A-UNEXPECTED-PROVIDER-COLLAPSE",
        }
    absent_declaration = json.loads(json.dumps(catalog.raw))
    next(
        item for item in absent_declaration["premises"]
        if item["name"] == "honest-commit"
    )["bound_model_or_hypothesis"]["value"]["law_ref"] = "AbsentOwnerDeclaration"
    try:
        Catalog.from_raw(absent_declaration)
    except ProbeError:
        missing_owner_declaration = {
            "outcome": "CannotAnswer",
            "code": "API-C-HYPOTHESIS-DECLARATION-ABSENT",
        }
    else:  # pragma: no cover - required negative control
        missing_owner_declaration = {
            "outcome": "Affirmative",
            "code": "API-A-UNEXPECTED-UNDECLARED-HYPOTHESIS",
        }

    return {
        "premise_ids": {name: p.premise_id for name, p in sorted(catalog.premises.items())},
        "depth_counts": {
            depth: sum(p.evidence_depth == depth for p in catalog.premises.values())
            for depth in sorted(DEPTHS)
        },
        "complete": complete,
        "fresh": fresh,
        "fiat_shamir": fiat_shamir,
        "provider_map": provider_map,
        "provider_completion": provider_completion,
        "omissions": omission_results,
        "wrong_coordinate": wrong_coordinate,
        "extra_key": extra_key,
        "scope_mismatches": scope_results,
        "alternate_provider": alternate_provider,
        "bool_noncompletion_collapse": bool_noncompletion_collapse,
        "missing_owner_declaration": missing_owner_declaration,
        "catalog_digest": digest("analysis.premise-catalog.v0", catalog.raw["premises"]),
    }
