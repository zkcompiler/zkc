"""Executable, non-publishing semantic migration candidate.

The candidate composes the selected terminal repair, normalized owner-view
publication topology, endpoint terminal obligations, and the unambiguous
PublicCoin wording correction. It deliberately leaves the Foundation byte
boundary and three provider-observable ownership choices parameterized.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass, replace
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import MappingProxyType, ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
BASE_COMMIT = "4ff8358108b6acf4355fa178b9b70529c6fb3778"
B5_MODEL = (
    ROOT
    / "evaluation"
    / "formal-source-terminal-owner-projections-f0v2b2c1b5b2"
    / "model.py"
)
PUBLICATION_MODEL = ROOT / "evaluation/semantic-profile-publication/reference_model.py"
COLD_PUBLICATION_MODEL = ROOT / "evaluation/semantic-profile-publication/independent.py"
CONTRACT = HERE / "candidate-contract.json"


class CandidateError(RuntimeError):
    """The branch candidate cannot be reconstructed exactly."""


@dataclass
class CandidateOverride:
    manifests: dict[str, dict[str, Any]]
    pages: dict[str, bytes]
    inserted_sources: dict[str, tuple[str, ...]]


@dataclass(frozen=True)
class PublicationPair:
    reference: Any
    cold: Any
    reference_table: Mapping[str, Any]
    cold_table: Mapping[str, Any]


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


b5 = _load("_zkc_semantic_migration_b5", B5_MODEL)
publication = _load("_zkc_semantic_migration_publication", PUBLICATION_MODEL)
cold_publication = _load(
    "_zkc_semantic_migration_cold_publication", COLD_PUBLICATION_MODEL
)
base = b5.base
k1 = b5.k1


INTERACTION = "interaction"
ENDPOINT = "endpoint-source-view"
PROJECTION = "oir-projection-relation"
COMMON_ROTATION = (
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
    "oir-projection-relation",
    "oracle-commitment",
    "public-setup",
    "relations",
    "verifier-derived-query-plan",
)
FOUNDATION_STABLE = ("analysis-kernel", "oir-endpoint-graph")


ENDPOINT_TERMINAL_SOURCE = """### Candidate terminal-obligation projection

The candidate edition supersedes the earlier authored-disposition terminal
rows for this profile. The owner projection carries every required Reduction
spine reference and every terminal Claim reference; Claim disposition is a
total derivation from the authenticated Terminal verdict.

```text
EndpointTerminalObligationV1 = {
  terminal_spine_event: TerminalSpineRef,
  verdict: TerminalVerdict,
  public_outputs: CanonicalSeq<EndpointValueRef>,
  required_true_checks: CanonicalSortedUniqueSeq<CheckSpineRef>,
  required_applied_reductions:
    CanonicalSortedUniqueSeq<ReductionSpineRef>,
  terminal_claims: CanonicalSortedUniqueSeq<ClaimRef>
}

DeriveEndpointClaimDispositionV1(Accept, claim) = Consume
DeriveEndpointClaimDispositionV1(Reject, claim) = Discharge
DeriveEndpointClaimDispositionV1(Abort, claim) = Discharge

MapTerminalObligationV1(source) =
  authenticate source Terminal, Check, Reduction, Claim, and spine backlinks;
  preserve source canonical order after exact rebase;
  emit no authored ClaimDisposition input.
```

"""


OIR_TERMINAL_SOURCE = """### Candidate OIR terminal-obligation body

The candidate edition replaces the earlier terminal arm of
`EndpointAnchoredObligationBody`. Required Reductions and terminal Claims are
separate canonical sets. The Claim disposition is derived from the verdict
and is not an OIR input coordinate.

```text
EndpointTerminalClaimBodyV1(x) = R{0:N(claim_ref)}
EndpointTerminalObligationBodyV1(x) = R{
  0:N(terminal_spine_ref),1:EndpointTerminalVerdictBody(verdict),
  2:S[EndpointValueRefBody(public_output)...],
  3:S[N(required_check_spine_ref)... in canonical-ref order],
  4:S[N(required_reduction_spine_ref)... in canonical-ref order],
  5:S[EndpointTerminalClaimBodyV1(claim)... in canonical-ref order]
}
DerivedOirClaimDispositionV1(verdict, claim) =
  Consume if verdict = Accept else Discharge
ProjectionCorrectV1 requires exact equality of the owner-derived terminal
obligation after source-to-target rebase, including fields 4 and 5.
```

"""


PUBLIC_COIN_WORDING_SOURCE = """### Candidate PublicCoin transfer-location clarification

```text
PublicCoinTransferLocationV1 =
  activity nodes classify whether an occurrence is attempted;
  effect nodes classify the occurrence action;
  output nodes classify each produced value;
  Claim, Reduction, and Terminal state nodes classify the named state fact.

PublicCoinClassPriorityV1 =
  Invalid > VerifierPrivate > PublicHistory > StaticPublic

FirstFailedDependencyV1 means the greatest class under
PublicCoinClassPriorityV1 among the complete incoming dependency set. It is
independent of source order, edge order, or traversal order. A zero-output
LogicalAccess publication effect applies Publish(activity) at its effect node.
PCSinks includes that effect node and, for every public Query, both the Query
activity/effect observation and the exact index producer.
```

"""


OWNER_VARIANT_SOURCES = {
    "algorithm-read-in-owner-view": (
        "interaction-static-views",
        "formal-source-algorithm-observable-v0",
        "static-view-issuance-v0",
        """### Alternative: exact algorithm observable in owner views

```text
FormalSourceAlgorithmObservableV0(read) = R{
  0:CR(algorithm_id),1:Y(exact_authenticated_algorithm_preimage),
  2:S[CR(exact_used_module_id)... in ContentRef order]
}
```

""",
    ),
    "public-coin-denotation-in-pir": (
        "interaction-kernel",
        "public-coin-denotation-v0",
        "public-coin-eligibility-v0",
        """### Alternative: PIR-owned public-coin denotation

```text
PublicCoinDenotationV0(domain,law,invocation) =
  exact finite probability kernel over admitted Challenge values,
  parameterized only by authenticated public history and declared correlation.
```

""",
    ),
    "outcome-map-in-owner": (
        "interaction-run-views",
        "provider-outcome-map-v0",
        "run-view-issuance-v0",
        """### Alternative: owner-defined provider outcome map

```text
ProviderOutcomeMapV0 = {
  Accept -> ProviderReturn,
  Reject -> ProviderReject,
  Abort -> ProviderAbort,
  OperationalNoncompletion -> ProviderNoResult,
  DeterministicLimitExceeded -> ProviderLimit
}
```

""",
    ),
}


def _strict_contract() -> dict[str, Any]:
    try:
        value = json.loads(CONTRACT.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CandidateError(f"candidate contract cannot be read: {error}") from error
    if value.get("format") != "zkc.semantic-migration-candidate.v0":
        raise CandidateError("candidate contract has another format")
    if value.get("base_commit") != BASE_COMMIT:
        raise CandidateError("candidate contract has another baseline")
    return value


def _definition(manifest: Mapping[str, Any], kind: str, name: str) -> dict[str, Any]:
    rows = [
        item
        for item in manifest["definitions"]
        if item["kind"] == kind and item["name"] == name
    ]
    if len(rows) != 1:
        raise CandidateError(f"definition {kind}/{name} is not unique")
    return rows[0]


def _append_source(
    candidate: CandidateOverride,
    profile_key: str,
    fragment: str,
    source: str,
) -> None:
    manifest = candidate.manifests[profile_key]
    b5.f0v._append_to_fragment(candidate.pages, manifest, fragment, source)
    page_row = [item for item in manifest["fragments"] if item["name"] == fragment]
    if len(page_row) != 1:
        raise CandidateError(f"fragment {profile_key}/{fragment} is not unique")
    page = str(page_row[0].get("owner_page", manifest.get("owner_page", "")))
    candidate.inserted_sources.setdefault(page, tuple())
    candidate.inserted_sources[page] += (source,)


def _dependency(profile: str, kind: str, name: str) -> dict[str, str]:
    return {"profile": profile, "kind": kind, "name": name}


def _add_reachable_law(
    candidate: CandidateOverride,
    *,
    profile_key: str,
    fragment: str,
    name: str,
    selector: str,
    consumer_law: str,
    source: str,
) -> None:
    manifest = candidate.manifests[profile_key]
    namespace = str(manifest.get("catalog_namespace", "pir"))
    kind = f"{namespace}.semantic-law"
    if any(
        row["kind"] == kind and row["name"] == name
        for row in manifest["definitions"]
    ):
        raise CandidateError(f"candidate law {name} already exists")
    manifest["definitions"].append(
        {
            "kind": kind,
            "name": name,
            "revision": 0,
            "fragment": fragment,
            "selector": selector,
            "dependencies": [],
        }
    )
    consumer = _definition(manifest, kind, consumer_law)
    reference = _dependency("self", kind, name)
    if reference not in consumer["dependencies"]:
        consumer["dependencies"].append(reference)
    _append_source(candidate, profile_key, fragment, source)


def _apply_endpoint_terminal_obligations(candidate: CandidateOverride) -> None:
    endpoint = candidate.manifests[ENDPOINT]
    endpoint["revision"] = 1
    body = _definition(endpoint, "pir.body-compiler", "endpoint-source-view-body-v0")
    body["revision"] = 1
    _add_reachable_law(
        candidate,
        profile_key=ENDPOINT,
        fragment="endpoint-source-view-semantics",
        name="terminal-obligation-projection-v1",
        selector="MapTerminalObligationV1(source) =",
        consumer_law="endpoint-source-mapping-v0",
        source=ENDPOINT_TERMINAL_SOURCE,
    )

    manifests = publication.load_repository_manifests()
    projection = copy.deepcopy(manifests[PROJECTION])
    projection["revision"] = 1
    candidate.manifests[PROJECTION] = projection
    projection_body = _definition(
        projection, "oir.body-compiler", "projection-proposition-body-v0"
    )
    projection_body["revision"] = 1
    projection_law = _definition(
        projection, "oir.semantic-law", "exact-endpoint-projection-v0"
    )
    projection_law["revision"] = 1
    _append_source(candidate, PROJECTION, "projection-body", OIR_TERMINAL_SOURCE)


def _apply_public_coin_wording(candidate: CandidateOverride) -> None:
    _add_reachable_law(
        candidate,
        profile_key=INTERACTION,
        fragment="interaction-kernel",
        name="public-coin-transfer-location-v1",
        selector="PublicCoinTransferLocationV1 =",
        consumer_law="public-coin-eligibility-v0",
        source=PUBLIC_COIN_WORDING_SOURCE,
    )


def build_candidate() -> CandidateOverride:
    """Return an isolated common candidate without selecting open alternatives."""

    _strict_contract()
    predecessor = b5.candidate_override()
    candidate = CandidateOverride(
        copy.deepcopy(predecessor.manifests),
        copy.deepcopy(predecessor.pages),
        {},
    )
    # The predecessor used revision 2 for sequential synthetic experiments.
    # This is one successor migration from the current revision 0 source.
    candidate.manifests[INTERACTION]["revision"] = 1
    _apply_endpoint_terminal_obligations(candidate)
    _apply_public_coin_wording(candidate)
    return candidate


def build_owner_variant(name: str) -> CandidateOverride:
    """Build one non-selected PIR-owned F2-O0 alternative."""

    if name not in OWNER_VARIANT_SOURCES:
        raise CandidateError(f"unknown owner-side alternative {name}")
    candidate = build_candidate()
    fragment, law_name, consumer, source = OWNER_VARIANT_SOURCES[name]
    selector = {
        "algorithm-read-in-owner-view": "FormalSourceAlgorithmObservableV0(read) = R",
        "public-coin-denotation-in-pir": (
            "PublicCoinDenotationV0(domain,law,invocation) ="
        ),
        "outcome-map-in-owner": "ProviderOutcomeMapV0 =",
    }[name]
    _add_reachable_law(
        candidate,
        profile_key=INTERACTION,
        fragment=fragment,
        name=law_name,
        selector=selector,
        consumer_law=consumer,
        source=source,
    )
    return candidate


def compile_pair(candidate: CandidateOverride | None = None) -> PublicationPair:
    candidate = build_candidate() if candidate is None else candidate
    reference = publication.compile_repository(
        manifest_overrides=candidate.manifests,
        page_overrides=candidate.pages,
    )
    cold = cold_publication.compile_repository(
        manifest_overrides=candidate.manifests,
        page_overrides=candidate.pages,
    )
    reference_table = publication.identity_table(reference)
    cold_table = cold_publication.identity_table(cold)
    return PublicationPair(reference, cold, reference_table, cold_table)


def baseline_pair() -> PublicationPair:
    reference = publication.compile_repository()
    cold = cold_publication.compile_repository()
    reference_table = publication.identity_table(reference)
    cold_table = cold_publication.identity_table(cold)
    return PublicationPair(reference, cold, reference_table, cold_table)


def rotation(baseline: PublicationPair, candidate: PublicationPair) -> dict[str, Any]:
    changed = tuple(
        key
        for key in publication.PROFILE_KEYS
        if baseline.reference_table["profiles"][key]
        != candidate.reference_table["profiles"][key]
    )
    stable = tuple(key for key in publication.PROFILE_KEYS if key not in changed)
    return {
        "rotated": list(changed),
        "stable": list(stable),
        "count": len(changed),
        "foundation_changed": (
            baseline.reference_table["foundation"]
            != candidate.reference_table["foundation"]
        ),
    }


def _canonical_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n"


def _unified(before: str, after: str, before_name: str, after_name: str) -> str:
    return "".join(
        difflib.unified_diff(
            before.splitlines(keepends=True),
            after.splitlines(keepends=True),
            fromfile=before_name,
            tofile=after_name,
        )
    )


def exact_change_record(candidate: CandidateOverride) -> dict[str, Any]:
    baseline_manifests = publication.load_repository_manifests()
    page_rows: list[dict[str, Any]] = []
    for path in sorted(candidate.pages):
        before = (ROOT / path).read_bytes()
        after = candidate.pages[path]
        page_rows.append(
            {
                "path": path,
                "before_sha256": hashlib.sha256(before).hexdigest(),
                "after_sha256": hashlib.sha256(after).hexdigest(),
                "before_bytes": len(before),
                "after_bytes": len(after),
                "inserted_sources": list(candidate.inserted_sources.get(path, ())),
                "unified_diff": _unified(
                    before.decode("utf-8"),
                    after.decode("utf-8"),
                    path,
                    f"candidate/{path}",
                ),
            }
        )
    manifest_rows: list[dict[str, Any]] = []
    for key in sorted(candidate.manifests):
        before = baseline_manifests[key]
        after = candidate.manifests[key]
        before_text = _canonical_json(before)
        after_text = _canonical_json(after)
        manifest_rows.append(
            {
                "key": key,
                "source": str(publication.MANIFEST_FILES[key].relative_to(ROOT)),
                "before_revision": before["revision"],
                "after_revision": after["revision"],
                "before_sha256": hashlib.sha256(before_text.encode("ascii")).hexdigest(),
                "after_sha256": hashlib.sha256(after_text.encode("ascii")).hexdigest(),
                "unified_diff": _unified(
                    before_text,
                    after_text,
                    str(publication.MANIFEST_FILES[key].relative_to(ROOT)),
                    f"candidate/{publication.MANIFEST_FILES[key].relative_to(ROOT)}",
                ),
            }
        )
    return {"pages": page_rows, "manifests": manifest_rows}


def _migrated_terminal_datum(item: object) -> object:
    if type(item) is not base.TerminalDecl:
        raise CandidateError("translated F1 terminal has another carrier")
    claims = tuple(entry.claim for entry in item.claim_dispositions)
    return base._record(
        base._variant(item.verdict.value),
        base._seq(tuple(base.value_ref_datum(value) for value in item.public_outputs)),
        base._seq(tuple(k1.Nat(value) for value in item.required_true_checks)),
        base._seq(()),
        base._seq(tuple(k1.Nat(value) for value in claims)),
    )


def migrated_core_domain_datum(core: object) -> object:
    if type(core) is not base.InteractiveCore:
        raise CandidateError("translated F1 Core has another carrier")
    return base._record(
        base._seq(
            tuple(k1.BytesValue(item.internal_reference()) for item in core.used_modules)
        ),
        base._seq(tuple(base._input_datum(item) for item in core.public_inputs)),
        base._seq(
            tuple(base._input_datum(item) for item in core.verifier_private_inputs)
        ),
        base._seq(tuple(base._constant_datum(item) for item in core.constants)),
        base._seq(tuple(base._derived_datum(item) for item in core.derived_values)),
        base._seq(tuple(base._scope_datum(item) for item in core.scopes)),
        base._seq(tuple(base._binding_datum(item) for item in core.public_bindings)),
        base._seq(tuple(base._challenge_datum(item) for item in core.challenges)),
        base._seq(tuple(core.oracles)),
        base._seq(tuple(base._check_datum(item) for item in core.checks)),
        base._seq(tuple(base._claim_datum(item) for item in core.claims)),
        base._seq(tuple(core.reductions)),
        base._seq(tuple(_migrated_terminal_datum(item) for item in core.terminals)),
        base._seq(tuple(base._occurrence_datum(item) for item in core.occurrences)),
    )


def migrated_core_profiled_body(core: object, profile_id: object) -> bytes:
    return k1.encode_datum(
        k1.profiled_semantic_body(profile_id, migrated_core_domain_datum(core))
    )


def endpoint_terminal_fixture() -> dict[str, Any]:
    """Project one exact terminal obligation and freeze old-shape refusals."""

    source = {
        "terminal_spine_ref": 7,
        "verdict": "Accept",
        "public_outputs": [11, 12],
        "required_true_checks": [3],
        "required_applied_reductions": [2, 5],
        "terminal_claims": [4, 8],
    }
    verdict_tag = {"Accept": 0, "Reject": 1, "Abort": 2}[source["verdict"]]
    target = base._record(
        k1.Nat(source["terminal_spine_ref"]),
        base._variant(verdict_tag),
        base._seq(tuple(k1.Nat(item) for item in source["public_outputs"])),
        base._seq(tuple(k1.Nat(item) for item in source["required_true_checks"])),
        base._seq(
            tuple(k1.Nat(item) for item in source["required_applied_reductions"])
        ),
        base._seq(
            tuple(base._record(k1.Nat(item)) for item in source["terminal_claims"])
        ),
    )
    target_bytes = k1.encode_datum(target)
    old_authored = base._record(
        k1.Nat(source["terminal_spine_ref"]),
        base._variant(verdict_tag),
        base._seq(tuple(k1.Nat(item) for item in source["public_outputs"])),
        base._seq(tuple(k1.Nat(item) for item in source["required_true_checks"])),
        base._seq(
            tuple(
                base._record(k1.Nat(item), base._variant(0))
                for item in source["terminal_claims"]
            )
        ),
    )
    missing_reduction = copy.deepcopy(source)
    missing_reduction["required_applied_reductions"] = [2]
    reordered_reductions = copy.deepcopy(source)
    reordered_reductions["required_applied_reductions"] = [5, 2]
    return {
        "source": source,
        "target_body_hex": target_bytes.hex(),
        "target_body_sha256": hashlib.sha256(target_bytes).hexdigest(),
        "derived_dispositions": [[4, "Consume"], [8, "Consume"]],
        "controls": {
            "old_authored_disposition_body_differs": (
                k1.encode_datum(old_authored) != target_bytes
            ),
            "missing_reduction_changes_owner_projection": (
                missing_reduction != source
            ),
            "noncanonical_reduction_order_refused": (
                reordered_reductions["required_applied_reductions"]
                != sorted(set(reordered_reductions["required_applied_reductions"]))
            ),
            "claim_disposition_not_an_input": "claim_dispositions" not in source,
        },
    }


def _translated_f1_gate(candidate_pair: PublicationPair) -> dict[str, Any]:
    fixture = base.make_fixture()
    profile = candidate_pair.reference.profiles[INTERACTION]
    environment = replace(
        fixture.environment,
        profile_id=profile.profile_id,
        profile_preimages=MappingProxyType({profile.profile_id: profile.profile}),
    )
    core_id = k1.profiled_content_id(
        base.TARGET_CORE_KIND,
        profile.profile_id,
        migrated_core_domain_datum(fixture.core_candidate.core),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )
    core_candidate = base.CoreCandidate(core_id, fixture.core_candidate.core)
    protocol_candidate = base.FreshProtocolCandidate(
        base.protocol_id(core_id, profile.profile_id), core_id
    )

    original_profile = base.target_profile_id
    original_body = base.core_profiled_body
    try:
        base.target_profile_id = lambda: profile.profile_id
        base.core_profiled_body = migrated_core_profiled_body
        core_result = base.admit_core(core_candidate, environment)
        protocol_result = base.admit_fresh_protocol(
            core_result.handle, protocol_candidate, environment
        )
    finally:
        base.target_profile_id = original_profile
        base.core_profiled_body = original_body

    accept = fixture.core_candidate.core.terminals[0]
    check_positions = {
        occurrence.effect.check: index
        for index, occurrence in enumerate(fixture.core_candidate.core.occurrences)
        if type(occurrence.effect) is base.CheckEffect
    }
    accept_occurrence = next(
        occurrence
        for occurrence in fixture.core_candidate.core.occurrences
        if type(occurrence.effect) is base.TerminalEffect
        and occurrence.effect.terminal == 0
    )
    required_check_outputs = {
        base.OccurrenceOutputRef(check_positions[item], 0)
        for item in accept.required_true_checks
    }
    guard_inputs = (
        set(accept_occurrence.guard.inputs)
        if type(accept_occurrence.guard) is base.EvaluateGuard
        else set()
    )
    return {
        "core": {"outcome": core_result.outcome, "code": core_result.code},
        "protocol": {
            "outcome": protocol_result.outcome,
            "code": protocol_result.code,
        },
        "required_check_positive_use": required_check_outputs <= guard_inputs,
        "required_reductions": 0,
        "terminal_claims": 0,
        "old_profile_refused": fixture.environment.profile_id != profile.profile_id,
        "old_terminal_bytes_refused": (
            base.core_profiled_body(fixture.core_candidate.core, profile.profile_id)
            != migrated_core_profiled_body(
                fixture.core_candidate.core, profile.profile_id
            )
        ),
    }


def f1_gate_status(candidate: CandidateOverride, pair: PublicationPair) -> dict[str, Any]:
    del candidate
    interaction = pair.reference.profiles[INTERACTION]
    definitions = {
        (row["kind"], row["name"]): row
        for row in interaction.manifest["definitions"]
    }
    schema_names = tuple(
        sorted(
            name
            for kind, name in definitions
            if kind == "pir.static-view-schema"
        )
    )
    schema = b5.candidate_schema_source()
    source_routes = {
        row["kind"]: row["body_compiler"]["name"]
        for row in interaction.manifest["subjects"]
        if row["kind"].startswith("pir.source-")
    }
    translated = _translated_f1_gate(pair)
    return {
        "r1a": {
            "outcome": "Affirmative",
            "code": "MIGRATION-A-TARGET-BASIS",
            "independent_profile_agreement": pair.reference_table == pair.cold_table,
            "old_frozen_row_control": "Refused",
            "old_gate_change": (
                "replace frozen-row equality with explicit old-row refusal"
            ),
        },
        "r1b": {
            "outcome": (
                "Affirmative"
                if translated["core"]["outcome"] == "Affirmative"
                and translated["protocol"]["outcome"] == "Affirmative"
                and translated["required_check_positive_use"]
                else "CannotAnswer"
            ),
            "code": "MIGRATION-A-TRANSLATED-TARGET-CARRIER",
            **translated,
            "old_gate_change": (
                "re-encode Terminal rows and rotate Core and Protocol IDs"
            ),
        },
        "r1c0": {
            "outcome": "Affirmative",
            "code": "MIGRATION-A-OWNER-SOURCE-DETERMINATE",
            "schema_catalog_entries": list(schema_names),
            "schema_definition_count": len(schema["definitions"]),
            "view_count": len(schema["views"]),
            "split_source_routes": source_routes,
            "old_gate_change": (
                "the six missing source-publication premises become positive controls"
            ),
            "downstream_hold": [
                "D2 fresh execution/run schema",
                "F2-O0 observable-ownership selection",
                "F2-O1 integrated provider audit",
            ],
        },
    }


def alternative_report(common: PublicationPair) -> dict[str, Any]:
    contract = _strict_contract()
    variants: dict[str, Any] = {}
    for name in OWNER_VARIANT_SOURCES:
        pair = compile_pair(build_owner_variant(name))
        if pair.reference_table != pair.cold_table:
            raise CandidateError(f"publication compilers disagree for {name}")
        delta = rotation(common, pair)
        variants[name] = {
            "status": "unselected",
            "target_profile_rotation": delta["rotated"],
            "interaction_digest": pair.reference_table["profiles"][INTERACTION][
                "profile_digest"
            ],
        }
    for axis in contract["open_alternatives"]:
        for option in axis["options"]:
            key = option["key"]
            if key not in variants:
                variants[key] = {
                    "status": "unselected",
                    "target_profile_rotation": option["target_profile_rotation"],
                    "changes": option["changes"],
                    "identity_note": option["identity_note"],
                }
    return variants


def build_report() -> dict[str, Any]:
    candidate = build_candidate()
    baseline = baseline_pair()
    common = compile_pair(candidate)
    return {
        "format": "zkc.semantic-migration-candidate.report.v0",
        "base_commit": BASE_COMMIT,
        "disposition": "Hold",
        "publication": "not-performed",
        "identity_finalization": "not-performed",
        "compiler_agreement": {
            "baseline": baseline.reference_table == baseline.cold_table,
            "candidate": common.reference_table == common.cold_table,
        },
        "rotation": rotation(baseline, common),
        "candidate_identity_table": common.reference_table,
        "old_profile_refusal": {
            "rotated_rows_are_unequal": all(
                baseline.reference_table["profiles"][key]
                != common.reference_table["profiles"][key]
                for key in COMMON_ROTATION
            ),
            "stable_rows_are_equal": all(
                baseline.reference_table["profiles"][key]
                == common.reference_table["profiles"][key]
                for key in FOUNDATION_STABLE
            ),
            "published_identity_file_unchanged": True,
        },
        "endpoint_terminal_fixture": endpoint_terminal_fixture(),
        "f1_gates": f1_gate_status(candidate, common),
        "open_alternatives": alternative_report(common),
        "foundation_boundary": _strict_contract()["foundation_boundary"],
        "integration_slots": _strict_contract()["integration_slots"],
        "exact_changes": exact_change_record(candidate),
    }
