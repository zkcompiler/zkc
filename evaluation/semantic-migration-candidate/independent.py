"""Independent structural audit of the semantic migration report.

This path does not construct candidate profiles. It checks the report against
the raw manifest graph, current owner bytes, and the explicit candidate
contract, providing a differently structured control around the two profile
compilers used by ``model.py``.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
INDEX = ROOT / "docs-next/foundation/semantic-profile-manifests.json"
CONTRACT = HERE / "candidate-contract.json"


class IndependentError(RuntimeError):
    """The report differs from the raw source graph or candidate contract."""


def _strict_json(path: Path) -> Any:
    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        value: dict[str, Any] = {}
        for key, item in pairs:
            if key in value:
                raise IndependentError(f"duplicate key {key!r} in {path}")
            value[key] = item
        return value

    try:
        return json.loads(path.read_bytes(), object_pairs_hook=object_pairs)
    except (OSError, json.JSONDecodeError) as error:
        raise IndependentError(f"cannot read {path}: {error}") from error


def _manifest_table() -> dict[str, Mapping[str, Any]]:
    index = _strict_json(INDEX)
    rows = index.get("manifests")
    if not isinstance(rows, list):
        raise IndependentError("profile index omits manifests")
    result: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        key = row["key"]
        source = ROOT / row["source"]
        if key in result:
            raise IndependentError(f"duplicate profile key {key}")
        result[key] = _strict_json(source)
    return result


def _interaction_cone(manifests: Mapping[str, Mapping[str, Any]]) -> tuple[str, ...]:
    imports = {
        key: tuple(str(item) for item in manifest["expected_imports"])
        for key, manifest in manifests.items()
    }
    reached = {"interaction"}
    changed = True
    while changed:
        changed = False
        for key, dependencies in imports.items():
            if key not in reached and any(item in reached for item in dependencies):
                reached.add(key)
                changed = True
    return tuple(key for key in manifests if key in reached)


def verify(report: Mapping[str, Any]) -> dict[str, Any]:
    contract = _strict_json(CONTRACT)
    manifests = _manifest_table()
    expected_cone = _interaction_cone(manifests)
    rotation = report["rotation"]
    if set(rotation["rotated"]) != set(expected_cone):
        raise IndependentError("reported rotation differs from raw import closure")
    if len(rotation["rotated"]) != 16 or len(rotation["stable"]) != 2:
        raise IndependentError("candidate does not expose the expected 16/2 split")
    if rotation["foundation_changed"]:
        raise IndependentError("common candidate unexpectedly rotates Foundation")

    pages = report["exact_changes"]["pages"]
    manifests_changed = report["exact_changes"]["manifests"]
    expected_pages = {
        "docs-next/oir/projection-contract.md",
        "docs-next/pir/duplex-sponge-fiat-shamir.md",
        "docs-next/pir/endpoint-projection-views.md",
        "docs-next/pir/fiat-shamir.md",
        "docs-next/pir/interactive-core.md",
        "docs-next/pir/interfaces-and-plans.md",
    }
    expected_manifests = {
        "canonical-framed-fiat-shamir",
        "duplex-sponge-fiat-shamir",
        "endpoint-source-view",
        "interaction",
        "interface-plan",
        "oir-projection-relation",
        "public-setup",
    }
    if {row["path"] for row in pages} != expected_pages:
        raise IndependentError("owner-page change set drifted")
    if {row["key"] for row in manifests_changed} != expected_manifests:
        raise IndependentError("profile-manifest change set drifted")
    for row in pages:
        current = (ROOT / row["path"]).read_bytes()
        if hashlib.sha256(current).hexdigest() != row["before_sha256"]:
            raise IndependentError(f"owner baseline drifted for {row['path']}")
        if row["before_sha256"] == row["after_sha256"] or not row["unified_diff"]:
            raise IndependentError(f"owner candidate is empty for {row['path']}")
    for row in manifests_changed:
        if row["before_sha256"] == row["after_sha256"] or not row["unified_diff"]:
            raise IndependentError(f"manifest candidate is empty for {row['key']}")

    refusal = report["old_profile_refusal"]
    if not all(
        (
            refusal["rotated_rows_are_unequal"],
            refusal["stable_rows_are_equal"],
            refusal["published_identity_file_unchanged"],
        )
    ):
        raise IndependentError("old-profile refusal control is incomplete")

    fixture = report["endpoint_terminal_fixture"]
    source = fixture["source"]
    if source["required_applied_reductions"] != [2, 5]:
        raise IndependentError("terminal fixture loses the required Reduction set")
    if source["terminal_claims"] != [4, 8]:
        raise IndependentError("terminal fixture loses the terminal Claim set")
    if fixture["derived_dispositions"] != [[4, "Consume"], [8, "Consume"]]:
        raise IndependentError("terminal fixture does not derive Accept dispositions")
    if not all(fixture["controls"].values()):
        raise IndependentError("terminal projection refusal control failed")

    gates = report["f1_gates"]
    if tuple(gates[key]["outcome"] for key in ("r1a", "r1b", "r1c0")) != (
        "Affirmative",
        "Affirmative",
        "Affirmative",
    ):
        raise IndependentError("migrated F1 prerequisite gate did not reclose")
    if not gates["r1b"]["old_profile_refused"]:
        raise IndependentError("translated R1B accepts the old profile")
    if not gates["r1b"]["old_terminal_bytes_refused"]:
        raise IndependentError("translated R1B accepts the old Terminal bytes")
    if len(gates["r1c0"]["schema_catalog_entries"]) != 6:
        raise IndependentError("R1C0 does not publish six owner-view schemas")

    alternatives = report["open_alternatives"]
    contract_options = {
        option["key"]
        for axis in contract["open_alternatives"]
        for option in axis["options"]
    }
    if set(alternatives) != contract_options:
        raise IndependentError("alternative inventory differs from the contract")
    if any(row["status"] != "unselected" for row in alternatives.values()):
        raise IndependentError("an open alternative was silently selected")
    owner_variants = (
        "algorithm-read-in-owner-view",
        "public-coin-denotation-in-pir",
        "outcome-map-in-owner",
    )
    if any(len(alternatives[key]["target_profile_rotation"]) != 16 for key in owner_variants):
        raise IndependentError("an owner-side alternative has another rotation cone")
    if len({alternatives[key]["interaction_digest"] for key in owner_variants}) != 3:
        raise IndependentError("owner-side alternatives collapse to one identity")
    package_variants = contract_options - set(owner_variants)
    if any(alternatives[key]["target_profile_rotation"] for key in package_variants):
        raise IndependentError("an Analysis/package alternative rotates PIR")

    if report["foundation_boundary"]["selection"] is not None:
        raise IndependentError("the active M1 decision was preselected")
    if len(report["integration_slots"]) != 5:
        raise IndependentError("active-lane integration slots drifted")
    if report["publication"] != "not-performed" or report["identity_finalization"] != "not-performed":
        raise IndependentError("candidate claims publication or identity finalization")

    return {
        "raw_profiles": len(manifests),
        "interaction_cone": list(expected_cone),
        "owner_pages": len(pages),
        "manifest_overrides": len(manifests_changed),
        "alternatives": len(alternatives),
        "integration_slots": len(report["integration_slots"]),
        "endpoint_terminal_controls": len(fixture["controls"]),
    }
