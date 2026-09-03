#!/usr/bin/env python3
"""Executable constructor-closure census for F0-V2B2A."""

from __future__ import annotations

import argparse
import copy
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
from types import ModuleType
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
INVENTORY_PATH = HERE / "inventory.json"
EXPECTED_PATH = HERE / "expected-findings.json"
OWNER_PAGE = ROOT / "docs-next/pir/interactive-core.md"
B1_SOURCE = ROOT / "evaluation/formal-source-view-bodies-f0v2b1/normalized-schema.json"
PUBLICATION_REFERENCE = (
    ROOT / "evaluation/semantic-profile-publication/reference_model.py"
)
PUBLICATION_INDEPENDENT = (
    ROOT / "evaluation/semantic-profile-publication/independent.py"
)
F1R1B_MODEL = ROOT / "evaluation/formal-source-target-core-f1r1b/reference_model.py"

VIEWS = {
    "PublicBindingView",
    "StrategyDecisionView",
    "PublicCoinView",
    "EffectView",
    "ClaimReductionView",
    "ExecutionView",
}

EXPECTED_CANONICAL_CASES = {
    "ValueRefBody": [
        "PublicInput",
        "VerifierPrivateInput",
        "Constant",
        "Derived",
        "OccurrenceOutput",
    ],
    "ScopeOpeningBody": ["Initially", "BeforeOccurrence"],
    "PublicBindingClassBody": ["Statement", "SessionContext", "PublicParameter"],
    "CoinCorrelationBody": ["Independent", "JointMember"],
    "ReductionUsePolicyBody": ["Exclusive", "Shared"],
    "OracleOriginBody": ["InitialOracle", "ProverOracle"],
    "OraclePublicationModeBody": [
        "FullCanonicalOracle",
        "PublicBinding",
        "LogicalAccess",
    ],
    "ClaimUsageBody": ["Linear", "Reusable"],
    "ClaimSourceBody": ["InitialClaim", "ReductionOutput"],
    "TerminalVerdictBody": ["Accept", "Reject", "Abort"],
    "GuardBody": ["Always", "EvaluateBoolean"],
    "OracleEffectBody": ["PublishOracle", "QueryOracle", "AnswerOracle"],
    "CoreEffectBody": [
        "ProverMessage",
        "DeterministicVerifierMessage",
        "Challenge",
        "InvokeCheck",
        "ApplyReduction",
        "ReachTerminal",
        "StandardOracle",
        "ModuleEffect",
    ],
    "ChallengeInterpretationBody": ["Fresh", "FiatShamir"],
    "PCNodeBody": [
        "PublicInputNode",
        "VerifierPrivateInputNode",
        "ConstantNode",
        "DerivedValueNode",
        "ScopeOpeningNode",
        "BindingObservationNode",
        "OccurrenceActivityNode",
        "OccurrenceEffectNode",
        "OccurrenceOutputNode",
        "ClaimStateNode",
        "ReductionStateNode",
        "TerminalDecisionNode",
        "ModuleControlNode",
        "ModuleOutputNode",
    ],
}

EXPECTED_DERIVED_CASES = {
    "ClaimDisposition": ["Consume", "Discharge"],
    "OracleQueryVisibility": ["Public", "VerifierOnly"],
    "ModuleDecisionClass": ["NoProverDecision", "ProverDecision", "ProverPublication"],
    "ProverDecisionKind": ["SupplyMessage", "SupplyOracle", "ModuleDecision"],
    "InteractiveCoreProverReadCoordinate": [
        "StaticConstant",
        "PublicInvocationInput",
        "OpenedBinding",
        "ObservedMessage",
        "ObservedChallenge",
        "ObservedOraclePublication",
        "ObservedOracleQuery",
        "ObservedOracleAnswer",
        "ObservedModuleValue",
        "PriorOwnMove",
    ],
    "PCClass": ["StaticPublic", "PublicHistory", "VerifierPrivate", "Invalid"],
}

B1_REQUIRED_VARIANTS = {
    "CoinCorrelation": {0, 1},
    "ReductionUse": {0, 1},
    "CoreEffect": set(range(8)),
    "PCNode": set(range(14)),
    "ProverMoveType": {0, 1, 2},
    "ReadCoordinate": set(range(10)),
}

REQUIRED_REPAIRS = {
    "joint-correlation-and-shared-reduction-use",
    "deterministic-verifier-message-effect",
    "apply-reduction-effect",
    "standard-oracle-effect-and-lifecycle",
    "admitted-module-effect-atom",
    "all-fourteen-pcnode-cases",
    "oracle-and-module-prover-moves",
    "all-ten-prover-read-coordinates",
    "challenge-reduction-consumers",
    "oracle-lifecycle-view-entries",
    "supported-extension-view-entries",
    "claim-creation-use-and-reduction-entries",
    "terminal-claim-dispositions",
    "runtime-oracle-receipt-schema",
}

REQUIRED_PRESSURE_FAMILIES = {
    "verifier-private-dependency",
    "constant-and-derived-value",
    "child-scope-and-nontrivial-guard",
    "deterministic-verifier-message",
    "oracle-initial-full",
    "oracle-initial-binding",
    "oracle-initial-logical",
    "oracle-prover-full",
    "oracle-prover-binding",
    "oracle-prover-logical",
    "oracle-query-public",
    "oracle-query-verifier-only",
    "claim-initial-linear",
    "claim-reduction-output-reusable",
    "reduction-publication-before-after",
    "joint-challenge-group",
    "shared-challenge-consumers",
    "module-no-decision",
    "module-prover-decision",
    "module-prover-publication",
    "terminal-abort-consume-discharge",
    "pcgraph-invalid-private-logical",
    "fresh-runtime-oracle-receipts",
}

REQUIRED_SHORTCUT_REFUSALS = {
    "generic-any-or-host-reflection-schema",
    "promote-maximum-zero-b1-identities",
    "carrier-formation-without-offline-admission",
    "eligibility-boolean-without-retained-pcgraph",
    "module-effect-without-authenticated-owner-law",
    "logical-access-without-acceptance-influence-check",
    "single-integrated-fixture-without-isolation-carriers",
    "token-catalog-as-owner-schema-authority",
}

F1R1B_BOUNDED_CONTROLS = (
    "oracles: tuple[object, ...]",
    "reductions: tuple[object, ...]",
    "Effect: TypeAlias = ProverMessageEffect | ChallengeEffect | CheckEffect | TerminalEffect",
    "F1R1B-U-JOINT-COINS",
    "F1R1B-U-OUTSIDE-SLICE",
)


class CensusError(ValueError):
    """The source census or proposed B2 program is incomplete or malformed."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def datum(self) -> dict[str, str]:
        return {"name": self.name, "outcome": self.outcome, "code": self.code}


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise CensusError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _read_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(
            path.read_text(encoding="utf-8"), object_pairs_hook=_strict_object
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CensusError(f"cannot read strict JSON at {path}") from error
    if type(value) is not dict:
        raise CensusError(f"JSON root at {path} is not an object")
    return value


def _load_module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _fragment(page: bytes, name: str) -> bytes:
    start = f"<!-- zkc-profile-source:{name}:start -->".encode()
    end = f"<!-- zkc-profile-source:{name}:end -->".encode()
    if page.count(start) != 1 or page.count(end) != 1:
        raise CensusError(f"source fragment {name} does not have unique markers")
    left = page.index(start) + len(start)
    right = page.index(end)
    if left >= right:
        raise CensusError(f"source fragment {name} markers are reversed")
    return page[left:right]


def _profile_evidence(owner: dict[str, Any]) -> dict[str, Any]:
    reference = _load_module(
        "_zkc_f0v2b2a_publication_reference", PUBLICATION_REFERENCE
    )
    independent = _load_module(
        "_zkc_f0v2b2a_publication_independent", PUBLICATION_INDEPENDENT
    )
    first = reference.identity_table(reference.compile_repository())
    second = independent.identity_table(independent.compile_repository())
    key = owner["key"]
    try:
        left = first["profiles"][key]
        right = second["profiles"][key]
    except (KeyError, TypeError) as error:
        raise CensusError(
            "Interaction profile is absent from publication evidence"
        ) from error
    if left != right:
        raise CensusError("profile publication implementations disagree")
    expected = {
        "profile_digest": owner["profile_digest"],
        "body_sha256": owner["profile_body_sha256"],
        "revision": owner["revision"],
    }
    actual = {key: left[key] for key in expected}
    if actual != expected:
        raise CensusError(
            "constructor census is pinned to the wrong Interaction profile"
        )
    return actual


def _core_fields(kernel: str) -> list[str]:
    start = "InteractiveCore = {"
    if kernel.count(start) != 1:
        raise CensusError("InteractiveCore root is not unique in the kernel fragment")
    block = kernel.split(start, 1)[1].split("\n}", 1)[0]
    return re.findall(r"^  ([a-z_]+):", block, flags=re.MULTILINE)


def _variant_tags(grammar: str, entry: dict[str, Any]) -> list[int]:
    start = entry["start"]
    if grammar.count(start) != 1:
        raise CensusError(f"canonical table {entry['name']} is not unique")
    tail = grammar.split(start, 1)[1]
    if entry.get("line_only") is True:
        block = tail.splitlines()[0]
    else:
        end = entry.get("end")
        if type(end) is not str or tail.count(end) != 1:
            raise CensusError(f"canonical table {entry['name']} has no exact end")
        block = tail.split(end, 1)[0]
    return [int(value) for value in re.findall(r"V\((\d+)", block)]


def _empty_references(schema: dict[str, Any]) -> list[str]:
    result: list[str] = []

    def walk(value: Any, path: str) -> None:
        if value == {"ref": "Empty"}:
            result.append(path)
        if type(value) is dict:
            for key, child in value.items():
                walk(child, f"{path}/{key}")
        elif type(value) is list:
            for index, child in enumerate(value):
                walk(child, f"{path}/{index}")

    definitions = schema.get("definitions")
    if type(definitions) is not dict:
        raise CensusError("B1 schema has no definition catalog")
    for name, value in definitions.items():
        walk(value, name)
    return sorted(result)


def _missing_variant_tags(schema: dict[str, Any]) -> dict[str, list[int]]:
    definitions = schema.get("definitions")
    if type(definitions) is not dict:
        raise CensusError("B1 schema has no definition catalog")
    result: dict[str, list[int]] = {}
    for name, required in B1_REQUIRED_VARIANTS.items():
        try:
            entries = definitions[name]["variant"]
            present = {entry[0] for entry in entries}
        except (KeyError, TypeError, IndexError) as error:
            raise CensusError(f"B1 schema variant {name} is malformed") from error
        if any(type(tag) is not int for tag in present):
            raise CensusError(f"B1 schema variant {name} has a non-integer tag")
        extra = present - required
        if extra:
            raise CensusError(f"B1 schema variant {name} has unexpected tags")
        result[name] = sorted(required - present)
    return result


def _validate_inventory(inventory: dict[str, Any]) -> dict[str, Any]:
    expected_keys = {
        "format",
        "owner_profile",
        "core_fields",
        "canonical_variant_tables",
        "derived_semantic_algebras",
        "b1_gap",
        "required_pressure_families",
        "reuse_boundaries",
        "stages",
        "prohibited_shortcuts",
    }
    if set(inventory) != expected_keys:
        raise CensusError("inventory outer shape is not exact")
    if (
        inventory["format"]
        != "zkc.formal-source-constructor-closure-f0v2b2a.inventory.v0"
    ):
        raise CensusError("inventory format is not F0-V2B2A v0")

    owner = inventory["owner_profile"]
    if type(owner) is not dict or set(owner) != {
        "key",
        "revision",
        "profile_digest",
        "profile_body_sha256",
    }:
        raise CensusError("owner-profile pin is malformed")
    if owner["key"] != "interaction" or owner["revision"] != 2:
        raise CensusError("constructor census is not pinned to Interaction revision 2")
    for key in ("profile_digest", "profile_body_sha256"):
        if (
            type(owner[key]) is not str
            or re.fullmatch(r"[0-9a-f]{64}", owner[key]) is None
        ):
            raise CensusError(f"owner-profile {key} is not a digest")

    page = OWNER_PAGE.read_bytes()
    kernel_bytes = _fragment(page, "interaction-kernel")
    static_bytes = _fragment(page, "interaction-static-views")
    grammar_bytes = _fragment(page, "interaction-body-grammar")
    try:
        kernel = kernel_bytes.decode("utf-8")
        grammar = grammar_bytes.decode("utf-8")
        full_page = page.decode("utf-8")
    except UnicodeDecodeError as error:
        raise CensusError("Interaction source is not UTF-8") from error

    fields = inventory["core_fields"]
    if type(fields) is not list or fields != _core_fields(kernel):
        raise CensusError("fourteen-field Core census differs from owner source")
    if len(fields) != 14 or len(set(fields)) != 14:
        raise CensusError("Core census is not a unique fourteen-field sequence")

    tables = inventory["canonical_variant_tables"]
    if type(tables) is not list or len(tables) != 15:
        raise CensusError("canonical variant-table census is incomplete")
    table_names: set[str] = set()
    variant_case_count = 0
    for table in tables:
        required = {"name", "start", "tags", "cases"}
        allowed = required | {"end", "line_only"}
        if type(table) is not dict or not required <= set(table) <= allowed:
            raise CensusError("canonical variant-table entry is malformed")
        name = table["name"]
        tags = table["tags"]
        cases = table["cases"]
        if type(name) is not str or not name or name in table_names:
            raise CensusError("canonical variant-table names are not unique")
        table_names.add(name)
        if (
            type(tags) is not list
            or type(cases) is not list
            or not tags
            or len(tags) != len(cases)
            or tags != sorted(set(tags))
            or any(type(case) is not str or not case for case in cases)
            or len(set(cases)) != len(cases)
        ):
            raise CensusError(f"canonical variant table {name} is malformed")
        if (
            name not in EXPECTED_CANONICAL_CASES
            or cases != EXPECTED_CANONICAL_CASES[name]
        ):
            raise CensusError(
                f"canonical variant table {name} has the wrong case meanings"
            )
        if _variant_tags(grammar, table) != tags:
            raise CensusError(f"canonical variant table {name} differs from source")
        variant_case_count += len(tags)
    if table_names != set(EXPECTED_CANONICAL_CASES):
        raise CensusError("canonical variant-table names are incomplete")

    algebras = inventory["derived_semantic_algebras"]
    if type(algebras) is not list or len(algebras) != 6:
        raise CensusError("derived semantic-algebra census is incomplete")
    algebra_names: set[str] = set()
    derived_case_count = 0
    for algebra in algebras:
        if type(algebra) is not dict or set(algebra) != {
            "name",
            "source_needles",
            "cases",
        }:
            raise CensusError("derived semantic-algebra entry is malformed")
        name = algebra["name"]
        needles = algebra["source_needles"]
        cases = algebra["cases"]
        if type(name) is not str or not name or name in algebra_names:
            raise CensusError("derived semantic-algebra names are not unique")
        algebra_names.add(name)
        if (
            type(needles) is not list
            or type(cases) is not list
            or not cases
            or any(type(item) is not str or not item for item in (*needles, *cases))
            or len(set(cases)) != len(cases)
        ):
            raise CensusError(f"derived semantic algebra {name} is malformed")
        if name not in EXPECTED_DERIVED_CASES or cases != EXPECTED_DERIVED_CASES[name]:
            raise CensusError(f"derived semantic algebra {name} has the wrong cases")
        if any(needle not in full_page for needle in needles):
            raise CensusError(
                f"derived semantic algebra {name} lost an owner source clause"
            )
        derived_case_count += len(cases)
    if algebra_names != set(EXPECTED_DERIVED_CASES):
        raise CensusError("derived semantic-algebra names are incomplete")

    b1 = _read_json(B1_SOURCE)
    gap = inventory["b1_gap"]
    if type(gap) is not dict or set(gap) != {
        "missing_variant_tags",
        "empty_references",
        "required_schema_repairs",
    }:
        raise CensusError("B1 gap declaration is malformed")
    if gap["missing_variant_tags"] != _missing_variant_tags(b1):
        raise CensusError("B1 missing-variant census is not exact")
    if gap["empty_references"] != _empty_references(b1):
        raise CensusError("B1 maximum-zero reference census is not exact")
    repairs = gap["required_schema_repairs"]
    if (
        type(repairs) is not list
        or set(repairs) != REQUIRED_REPAIRS
        or len(repairs) != len(set(repairs))
    ):
        raise CensusError("B2 schema-repair set is incomplete")

    families = inventory["required_pressure_families"]
    if type(families) is not list:
        raise CensusError("pressure-family catalog is not a sequence")
    family_ids: list[str] = []
    covered_views: set[str] = set()
    for family in families:
        if type(family) is not dict or set(family) != {
            "id",
            "owner",
            "views",
            "positive_carrier",
            "negative_discriminator",
            "stage",
        }:
            raise CensusError("pressure-family entry is malformed")
        family_id = family["id"]
        views = family["views"]
        if type(family_id) is not str or not family_id:
            raise CensusError("pressure-family ID is absent")
        family_ids.append(family_id)
        if family["owner"] not in {"pir.interactive-core", "pir.protocol"}:
            raise CensusError(f"pressure family {family_id} has the wrong owner")
        if type(views) is not list or not views or not set(views) <= VIEWS:
            raise CensusError(
                f"pressure family {family_id} has an invalid view surface"
            )
        covered_views.update(views)
        for field in ("positive_carrier", "negative_discriminator"):
            if type(family[field]) is not str or not family[field].strip():
                raise CensusError(f"pressure family {family_id} lacks {field}")
        if family["stage"] not in {"B2C", "B2D"}:
            raise CensusError(f"pressure family {family_id} has an invalid stage")
    if (
        len(family_ids) != len(set(family_ids))
        or set(family_ids) != REQUIRED_PRESSURE_FAMILIES
    ):
        raise CensusError("pressure-family catalog is not exact")
    if covered_views != VIEWS:
        raise CensusError("pressure-family catalog does not cover all six views")
    if {
        "oracle-initial-full",
        "oracle-initial-binding",
        "oracle-initial-logical",
        "oracle-prover-full",
        "oracle-prover-binding",
        "oracle-prover-logical",
    } - set(family_ids):
        raise CensusError("Oracle origin/publication cross-product is incomplete")
    if {
        "module-no-decision",
        "module-prover-decision",
        "module-prover-publication",
    } - set(family_ids):
        raise CensusError("module decision-class pressure is incomplete")

    reuse = inventory["reuse_boundaries"]
    if type(reuse) is not list or len(reuse) != 4:
        raise CensusError("reuse-boundary catalog is incomplete")
    reuse_paths: set[str] = set()
    for entry in reuse:
        if type(entry) is not dict or set(entry) != {"path", "use", "nonclaim"}:
            raise CensusError("reuse-boundary entry is malformed")
        path = entry["path"]
        if type(path) is not str or path in reuse_paths or not (ROOT / path).is_file():
            raise CensusError("reuse-boundary path is absent or duplicated")
        reuse_paths.add(path)
        if any(
            type(entry[key]) is not str or not entry[key].strip()
            for key in ("use", "nonclaim")
        ):
            raise CensusError("reuse boundary lacks its use or nonclaim")
    f1r1b_source = F1R1B_MODEL.read_text(encoding="utf-8")
    if any(control not in f1r1b_source for control in F1R1B_BOUNDED_CONTROLS):
        raise CensusError(
            "F1-R1B no longer exposes the bounded controls assumed by B2A"
        )

    stages = inventory["stages"]
    if type(stages) is not list or [stage.get("id") for stage in stages] != [
        "B2A",
        "B2B",
        "B2C",
        "B2D",
    ]:
        raise CensusError("B2 stage topology is not exact")
    for stage in stages:
        if type(stage) is not dict or set(stage) != {"id", "result"}:
            raise CensusError("B2 stage entry is malformed")
        if type(stage["result"]) is not str or not stage["result"].strip():
            raise CensusError("B2 stage lacks an exit result")

    shortcuts = inventory["prohibited_shortcuts"]
    if (
        type(shortcuts) is not list
        or set(shortcuts) != REQUIRED_SHORTCUT_REFUSALS
        or len(shortcuts) != len(set(shortcuts))
    ):
        raise CensusError("prohibited-shortcut set is incomplete")

    profile = _profile_evidence(owner)
    fragment_digests = {
        "interaction_kernel_sha256": hashlib.sha256(kernel_bytes).hexdigest(),
        "interaction_static_views_sha256": hashlib.sha256(static_bytes).hexdigest(),
        "interaction_body_grammar_sha256": hashlib.sha256(grammar_bytes).hexdigest(),
    }
    return {
        "profile": profile,
        "fragments": fragment_digests,
        "core_field_count": len(fields),
        "canonical_variant_table_count": len(tables),
        "canonical_variant_case_count": variant_case_count,
        "derived_semantic_algebra_count": len(algebras),
        "derived_semantic_case_count": derived_case_count,
        "closed_case_count": variant_case_count + derived_case_count,
        "b1_missing_variant_case_count": sum(
            len(tags) for tags in gap["missing_variant_tags"].values()
        ),
        "b1_empty_reference_count": len(gap["empty_references"]),
        "required_schema_repair_count": len(repairs),
        "pressure_family_count": len(families),
        "covered_view_count": len(covered_views),
        "reuse_boundary_count": len(reuse),
        "stage_count": len(stages),
        "prohibited_shortcut_count": len(shortcuts),
        "f1r1b_bounded_control_count": len(F1R1B_BOUNDED_CONTROLS),
    }


def _mutations() -> list[tuple[str, str, Callable[[dict[str, Any]], None]]]:
    return [
        (
            "profile-key-substitution",
            "F0V2B2A-R-PROFILE-KEY",
            lambda x: x["owner_profile"].__setitem__(
                "key", "canonical-framed-fiat-shamir"
            ),
        ),
        (
            "profile-revision-substitution",
            "F0V2B2A-R-PROFILE-REVISION",
            lambda x: x["owner_profile"].__setitem__("revision", 1),
        ),
        (
            "profile-digest-substitution",
            "F0V2B2A-R-PROFILE-DIGEST",
            lambda x: x["owner_profile"].__setitem__("profile_digest", "0" * 64),
        ),
        (
            "profile-body-substitution",
            "F0V2B2A-R-PROFILE-BODY",
            lambda x: x["owner_profile"].__setitem__("profile_body_sha256", "0" * 64),
        ),
        (
            "core-field-omission",
            "F0V2B2A-R-CORE-FIELD",
            lambda x: x["core_fields"].pop(2),
        ),
        (
            "core-field-reordering",
            "F0V2B2A-R-CORE-ORDER",
            lambda x: x["core_fields"].__setitem__(
                slice(0, 2), list(reversed(x["core_fields"][:2]))
            ),
        ),
        (
            "variant-table-omission",
            "F0V2B2A-R-VARIANT-TABLE",
            lambda x: x["canonical_variant_tables"].pop(),
        ),
        (
            "variant-tag-omission",
            "F0V2B2A-R-VARIANT-TAG",
            lambda x: x["canonical_variant_tables"][0]["tags"].pop(),
        ),
        (
            "variant-case-substitution",
            "F0V2B2A-R-VARIANT-CASE",
            lambda x: x["canonical_variant_tables"][0]["cases"].__setitem__(
                0, "ForeignValue"
            ),
        ),
        (
            "semantic-algebra-omission",
            "F0V2B2A-R-SEMANTIC-ALGEBRA",
            lambda x: x["derived_semantic_algebras"].pop(),
        ),
        (
            "semantic-source-clause-substitution",
            "F0V2B2A-R-SOURCE-CLAUSE",
            lambda x: x["derived_semantic_algebras"][0]["source_needles"].__setitem__(
                0, "visibility: Ambient"
            ),
        ),
        (
            "b1-variant-gap-omission",
            "F0V2B2A-R-B1-VARIANT-GAP",
            lambda x: x["b1_gap"]["missing_variant_tags"]["PCNode"].pop(),
        ),
        (
            "b1-empty-gap-omission",
            "F0V2B2A-R-B1-EMPTY-GAP",
            lambda x: x["b1_gap"]["empty_references"].pop(),
        ),
        (
            "schema-repair-omission",
            "F0V2B2A-R-SCHEMA-REPAIR",
            lambda x: x["b1_gap"]["required_schema_repairs"].pop(),
        ),
        (
            "pressure-family-omission",
            "F0V2B2A-R-PRESSURE-FAMILY",
            lambda x: x["required_pressure_families"].pop(),
        ),
        (
            "pressure-family-duplication",
            "F0V2B2A-R-PRESSURE-DUPLICATE",
            lambda x: x["required_pressure_families"].append(
                copy.deepcopy(x["required_pressure_families"][0])
            ),
        ),
        (
            "pressure-owner-substitution",
            "F0V2B2A-R-PRESSURE-OWNER",
            lambda x: x["required_pressure_families"][0].__setitem__(
                "owner", "analysis"
            ),
        ),
        (
            "pressure-view-substitution",
            "F0V2B2A-R-PRESSURE-VIEW",
            lambda x: x["required_pressure_families"][0].__setitem__(
                "views", ["AmbientView"]
            ),
        ),
        (
            "positive-carrier-omission",
            "F0V2B2A-R-POSITIVE-CARRIER",
            lambda x: x["required_pressure_families"][0].__setitem__(
                "positive_carrier", ""
            ),
        ),
        (
            "negative-discriminator-omission",
            "F0V2B2A-R-NEGATIVE-DISCRIMINATOR",
            lambda x: x["required_pressure_families"][0].__setitem__(
                "negative_discriminator", ""
            ),
        ),
        (
            "pressure-stage-substitution",
            "F0V2B2A-R-PRESSURE-STAGE",
            lambda x: x["required_pressure_families"][0].__setitem__("stage", "B2A"),
        ),
        (
            "reuse-path-substitution",
            "F0V2B2A-R-REUSE-PATH",
            lambda x: x["reuse_boundaries"][0].__setitem__(
                "path", "evaluation/absent.py"
            ),
        ),
        (
            "reuse-nonclaim-omission",
            "F0V2B2A-R-REUSE-NONCLAIM",
            lambda x: x["reuse_boundaries"][0].__setitem__("nonclaim", ""),
        ),
        ("stage-omission", "F0V2B2A-R-STAGE", lambda x: x["stages"].pop(1)),
        (
            "stage-reordering",
            "F0V2B2A-R-STAGE-ORDER",
            lambda x: x["stages"].__setitem__(
                slice(1, 3), list(reversed(x["stages"][1:3]))
            ),
        ),
        (
            "shortcut-refusal-omission",
            "F0V2B2A-R-SHORTCUT-OMISSION",
            lambda x: x["prohibited_shortcuts"].pop(),
        ),
        (
            "shortcut-refusal-substitution",
            "F0V2B2A-R-SHORTCUT-SUBSTITUTION",
            lambda x: x["prohibited_shortcuts"].__setitem__(0, "trust-the-producer"),
        ),
        (
            "inventory-format-substitution",
            "F0V2B2A-R-FORMAT",
            lambda x: x.__setitem__(
                "format", "zkc.formal-source-constructor-closure.v1"
            ),
        ),
    ]


def observe(inventory: dict[str, Any] | None = None) -> dict[str, Any]:
    candidate = copy.deepcopy(
        inventory if inventory is not None else _read_json(INVENTORY_PATH)
    )
    evidence = _validate_inventory(candidate)
    findings = [
        Finding(
            "dual-interaction-profile-reconstruction",
            "Affirmative",
            "F0V2B2A-A-PROFILE",
        ),
        Finding(
            "fourteen-field-core-root-census", "Affirmative", "F0V2B2A-A-CORE-ROOT"
        ),
        Finding(
            "canonical-appendix-variant-census",
            "Affirmative",
            "F0V2B2A-A-CANONICAL-VARIANTS",
        ),
        Finding(
            "derived-semantic-algebra-census",
            "Affirmative",
            "F0V2B2A-A-DERIVED-ALGEBRAS",
        ),
        Finding("exact-b1-constructor-gap", "Affirmative", "F0V2B2A-A-B1-GAP"),
        Finding(
            "six-view-pressure-topology", "Affirmative", "F0V2B2A-A-PRESSURE-TOPOLOGY"
        ),
        Finding(
            "bounded-reuse-boundaries", "Affirmative", "F0V2B2A-A-REUSE-BOUNDARIES"
        ),
        Finding("staged-b2-exit-program", "Affirmative", "F0V2B2A-A-STAGED-PROGRAM"),
        Finding(
            "constructor-complete-schema-source",
            "CannotAnswer",
            "F0V2B2A-C-SCHEMA-SOURCE",
        ),
        Finding("constructor-inhabitance", "CannotAnswer", "F0V2B2A-C-INHABITANCE"),
        Finding(
            "extended-offline-owner-admission", "CannotAnswer", "F0V2B2A-C-ADMISSION"
        ),
        Finding(
            "isolation-owner-view-derivation",
            "CannotAnswer",
            "F0V2B2A-C-ISOLATION-DERIVATION",
        ),
        Finding(
            "integrated-owner-view-derivation",
            "CannotAnswer",
            "F0V2B2A-C-INTEGRATED-DERIVATION",
        ),
        Finding(
            "general-pcgraph-transfer-and-sinks", "CannotAnswer", "F0V2B2A-C-PCGRAPH"
        ),
        Finding(
            "fresh-runtime-oracle-receipt-schema",
            "CannotAnswer",
            "F0V2B2A-C-RUNTIME-SCHEMA",
        ),
        Finding(
            "target-profile-publication-and-migration",
            "CannotAnswer",
            "F0V2B2A-C-TARGET-MIGRATION",
        ),
    ]
    for name, code, mutate in _mutations():
        changed = copy.deepcopy(candidate)
        mutate(changed)
        try:
            _validate_inventory(changed)
        except (CensusError, KeyError, IndexError, TypeError, ValueError):
            findings.append(Finding(name, "Refused", code))
        else:
            raise CensusError(f"mutation {name} was not refused")
    return {
        "aggregate": {
            "outcome": "CannotAnswer",
            "code": "F0V2B2A-C-EXECUTABLE-CONSTRUCTOR-CLOSURE",
        },
        "evidence_control": evidence,
        "cases": [finding.datum() for finding in findings],
    }


def _summary(result: dict[str, Any]) -> str:
    evidence = result["evidence_control"]
    aggregate = result["aggregate"]
    return (
        "[formal-source-constructor-closure-f0v2b2a] "
        f"{len(result['cases'])}/{len(result['cases'])} findings; "
        f"{aggregate['outcome']}/{aggregate['code']}; "
        f"{evidence['closed_case_count']} closed cases, "
        f"{evidence['pressure_family_count']} pressure families"
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    try:
        result = observe()
        if args.check:
            expected = _read_json(EXPECTED_PATH)
            if result != expected:
                raise CensusError(
                    "observed findings differ from expected-findings.json"
                )
    except (CensusError, OSError) as error:
        print(
            f"[formal-source-constructor-closure-f0v2b2a] ERROR: {error}",
            file=sys.stderr,
        )
        return 1
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(_summary(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
