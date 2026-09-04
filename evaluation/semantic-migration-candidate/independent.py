"""Independent structural audit of the direct refreeze rehearsal report."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CONTRACT = HERE / "candidate-contract.json"
INDEX = ROOT / "docs-next/foundation/semantic-profile-manifests.json"


class IndependentError(RuntimeError):
    """The report differs from the direct source graph or its pins."""


def _strict_json(path: Path) -> Any:
    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise IndependentError(f"duplicate key {key!r} in {path}")
            result[key] = value
        return result

    try:
        return json.loads(path.read_bytes(), object_pairs_hook=object_pairs)
    except (OSError, json.JSONDecodeError) as error:
        raise IndependentError(f"cannot read {path}: {error}") from error


def _sha256(path: Path) -> str:
    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError as error:
        raise IndependentError(f"cannot hash {path}") from error


def _manifest_table() -> dict[str, Mapping[str, Any]]:
    index = _strict_json(INDEX)
    rows = index.get("manifests")
    if not isinstance(rows, list):
        raise IndependentError("profile index omits manifests")
    result: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        key = row["key"]
        if key in result:
            raise IndependentError(f"duplicate profile key {key}")
        result[key] = _strict_json(ROOT / row["source"])
    return result


def _interaction_cone(manifests: Mapping[str, Mapping[str, Any]]) -> set[str]:
    reached = {"interaction"}
    while True:
        updated = reached | {
            key
            for key, manifest in manifests.items()
            if any(item in reached for item in manifest["expected_imports"])
        }
        if updated == reached:
            return reached
        reached = updated


def verify(report: Mapping[str, Any]) -> dict[str, Any]:
    contract = _strict_json(CONTRACT)
    manifests = _manifest_table()
    source_inventory = report["source_inventory"]
    if len(source_inventory["owner_pages"]) != 6:
        raise IndependentError("report does not carry six owner-page pins")
    if len(source_inventory["profile_manifests"]) != 8:
        raise IndependentError("report does not carry eight manifest pins")
    for key in ("owner_pages", "profile_manifests"):
        if source_inventory[key] != contract[key]:
            raise IndependentError(f"reported {key} differ from the contract")
        for row in source_inventory[key]:
            if _sha256(ROOT / row["path"]) != row["sha256"]:
                raise IndependentError(f"direct source pin drifted for {row['path']}")

    publication = report["publication"]
    table = publication["candidate_identity_table"]["profiles"]
    if set(table) != set(manifests):
        raise IndependentError("identity table differs from the indexed manifest graph")
    if not publication["compiler_agreement"]:
        raise IndependentError("report does not retain dual-compiler agreement")
    if len(publication["rotated_profiles"]) != 18:
        raise IndependentError("Analysis-head rotation is not eighteen profiles")
    if publication["stable_profiles"]:
        raise IndependentError("Analysis head unexpectedly leaves a stable profile")
    migration_table = publication["migration_identity_table"]["profiles"]
    if set(migration_table) != set(manifests):
        raise IndependentError("migration-head identity table differs from the index")
    if len(publication["migration_rotated_profiles"]) != 17:
        raise IndependentError("migration-head rotation is not seventeen profiles")
    if publication["migration_stable_profiles"] != ["analysis-kernel"]:
        raise IndependentError(
            "analysis-kernel is not the migration head's sole stable profile"
        )
    if publication["analysis_branch_rotated_profiles"] != [
        "analysis-kernel",
        "analysis-cryptographic-property",
        "analysis-afk-transport",
        "analysis-afk-theorem-source-validation",
        "analysis-incremental-composition",
        "analysis-incremental-composition-source-validation",
    ]:
        raise IndependentError("Analysis branch rotation cone differs")
    interaction_cone = _interaction_cone(manifests)
    if len(interaction_cone) != 16:
        raise IndependentError("raw import graph does not have a sixteen-profile Interaction cone")
    if not interaction_cone <= set(publication["migration_rotated_profiles"]):
        raise IndependentError("one Interaction-dependent profile failed to rotate")
    if "oir-endpoint-graph" not in publication["migration_rotated_profiles"]:
        raise IndependentError("the independent endpoint graph did not rotate")
    if not all(publication["legacy_profile_refusals"].values()):
        raise IndependentError("one legacy profile refusal control failed")

    gates = report["prerequisite_gates"]
    if gates["target_core"]["passed"] != gates["target_core"]["total"]:
        raise IndependentError("target-core prerequisite did not close")
    if gates["owner_views"]["passed"] != gates["owner_views"]["total"]:
        raise IndependentError("owner-view prerequisite did not finish")
    if gates["owner_views"]["aggregate"] != {
        "outcome": "Affirmative",
        "code": "F1R1C-A-SOURCE-DETERMINACY",
    }:
        raise IndependentError("owner-view source determinacy did not close")
    if gates["owner_views"]["law_field_selection"] != {
        "ExecutionView.generated_execution_law": "execution-and-replay-v0",
        "ExecutionView.relation_run_view_issuance_law": "run-view-issuance-v0",
        "ExecutionView.replay_qualification_law": "replay-qualification-v0",
        "ExecutionView.visible_history_law": "visible-history-v0",
        "StrategyDecisionView.prover_view_formation_law": "prover-view-formation-v0",
    }:
        raise IndependentError("owner-view law-field selection differs")
    hidden = gates["terminal_contract"]["hidden_gating_counterexample"]
    if hidden.get("violation") != "linear-claim-consumed-twice":
        raise IndependentError("hidden-gating refusal witness drifted")

    if (
        report["published_identity_sha256_before"]
        != report["published_identity_sha256_after"]
        or report["identity_finalization"] != "not-performed"
        or report["publication_disposition"] != "Hold"
    ):
        raise IndependentError("rehearsal claims or performs publication")
    return {
        "indexed_profiles": len(manifests),
        "interaction_cone": len(interaction_cone),
        "rotated_profiles": len(publication["rotated_profiles"]),
        "stable_profiles": len(publication["stable_profiles"]),
        "migration_rotated_profiles": len(
            publication["migration_rotated_profiles"]
        ),
        "migration_stable_profiles": len(
            publication["migration_stable_profiles"]
        ),
        "analysis_branch_rotated_profiles": len(
            publication["analysis_branch_rotated_profiles"]
        ),
        "owner_pages": len(source_inventory["owner_pages"]),
        "profile_manifests": len(source_inventory["profile_manifests"]),
        "legacy_profile_controls": len(publication["legacy_profile_refusals"]),
    }
