#!/usr/bin/env python3
"""Independent Python decision path for normalized Terminal carriers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any


@dataclass
class PathState:
    decisions: dict[int, bool]
    live_claims: list[int]
    valid: bool = True


def _positions(carrier: dict[str, Any], kind: str) -> dict[int, list[int]]:
    result: dict[int, list[int]] = {}
    for index, occurrence in enumerate(carrier["schedule"]):
        effect = occurrence["effect"]
        if effect["kind"] == kind:
            result.setdefault(effect["reference"], []).append(index)
    return result


def _unique_position(positions: dict[int, list[int]], reference: int) -> int | None:
    rows = positions.get(reference, [])
    return rows[0] if len(rows) == 1 else None


def _attempted_whenever(
    carrier: dict[str, Any], later: int, earlier: int
) -> bool:
    if not 0 <= earlier < later < len(carrier["schedule"]):
        return False
    earlier_guard = carrier["schedule"][earlier]["guard_atom"]
    later_guard = carrier["schedule"][later]["guard_atom"]
    return earlier_guard is None or earlier_guard == later_guard


def _must_when_true(term: dict[str, Any] | None) -> tuple[bool, set[int]]:
    if term is None:
        return False, set()
    if term["kind"] == "identity":
        return False, {int(term["input"])}
    if term["kind"] == "conjunction":
        return False, {int(item) for item in term["inputs"]}
    if term["kind"] == "true":
        return False, set()
    if term["kind"] == "false":
        return True, set()
    raise ValueError(f"unknown compact guard term {term!r}")


def _guard_branches(guard: int | None, path: PathState) -> list[tuple[bool, PathState]]:
    if guard is None:
        return [(True, path)]
    if guard in path.decisions:
        return [(path.decisions[guard], path)]
    left = PathState({**path.decisions, guard: True}, list(path.live_claims), path.valid)
    right = PathState({**path.decisions, guard: False}, list(path.live_claims), path.valid)
    return [(True, left), (False, right)]


def _forward_claims(carrier: dict[str, Any]) -> dict[str, Any]:
    paths = [PathState({}, list(carrier["initial_claims"]))]
    visits: dict[int, list[tuple[list[int], bool]]] = {}
    linear = set(carrier["linear_claims"])
    reductions = carrier["reductions"]
    for occurrence in carrier["schedule"]:
        next_paths: list[PathState] = []
        for path in paths:
            for active, branch in _guard_branches(occurrence["guard_atom"], path):
                if not active:
                    next_paths.append(branch)
                    continue
                effect = occurrence["effect"]
                if effect["kind"] == "terminal":
                    visits.setdefault(effect["reference"], []).append(
                        (list(branch.live_claims), branch.valid)
                    )
                elif effect["kind"] == "reduction":
                    reference = effect["reference"]
                    if not 0 <= reference < len(reductions):
                        branch.valid = False
                        next_paths.append(branch)
                        continue
                    transfer = reductions[reference]
                    branch.valid = branch.valid and all(
                        claim in branch.live_claims for claim in transfer["inputs"]
                    )
                    branch.live_claims = [
                        claim
                        for claim in branch.live_claims
                        if not (claim in linear and claim in transfer["inputs"])
                    ]
                    for claim in transfer["outputs"]:
                        if claim not in branch.live_claims:
                            branch.live_claims.append(claim)
                    next_paths.append(branch)
                else:
                    next_paths.append(branch)
        paths = next_paths
    all_valid = all(path.valid for path in paths) and all(
        valid for rows in visits.values() for _claims, valid in rows
    )
    return {"running": paths, "visits": visits, "all_valid": all_valid}


def _strictly_increasing(values: list[int]) -> bool:
    return all(left < right for left, right in zip(values, values[1:]))


def _terminal_contract(
    carrier: dict[str, Any], terminal: dict[str, Any], forward: dict[str, Any]
) -> tuple[bool, list[str]]:
    failures: list[str] = []
    terminal_positions = _positions(carrier, "terminal")
    check_positions = _positions(carrier, "check")
    reduction_positions = _positions(carrier, "reduction")
    terminal_position = _unique_position(terminal_positions, terminal["reference"])
    if terminal_position is None:
        return False, ["terminal backlink is not unique"]

    for label in ("required_checks", "required_reductions", "terminal_claims"):
        if not _strictly_increasing(terminal[label]):
            failures.append(f"{label} is not sorted-unique")

    impossible, positives = _must_when_true(terminal["guard_term"])
    for check in terminal["required_checks"]:
        check_position = _unique_position(check_positions, check)
        if check_position is None:
            failures.append(f"required Check {check} has no unique occurrence")
            continue
        if not _attempted_whenever(carrier, terminal_position, check_position):
            failures.append(f"required Check {check} is not attempted whenever the terminal is")
        if terminal["guard_term"] is None:
            failures.append(f"required Check {check} has no terminal GuardTerm")
        elif impossible:
            failures.append(f"required Check {check} lies under Impossible MustWhenTrue")
        direct = any(
            source.get("kind") == "occurrence-output"
            and source.get("occurrence") == check_position
            and source.get("output") == 0
            and ordinal in positives
            for ordinal, source in enumerate(terminal["guard_inputs"])
        )
        if not direct:
            failures.append(f"required Check {check} lacks a direct positive Guard input")

    for reduction in terminal["required_reductions"]:
        reduction_position = _unique_position(reduction_positions, reduction)
        if reduction_position is None:
            failures.append(f"required Reduction {reduction} has no unique occurrence")
        elif not _attempted_whenever(carrier, terminal_position, reduction_position):
            failures.append(
                f"required Reduction {reduction} is not attempted whenever the terminal is"
            )

    for live_claims, valid in forward["visits"].get(terminal["reference"], []):
        if not valid:
            failures.append("terminal path carries an invalid claim transfer")
        if live_claims != terminal["terminal_claims"]:
            failures.append(
                f"live claims {live_claims} differ from authored {terminal['terminal_claims']}"
            )
    return not failures, failures


def decide_carrier(carrier: dict[str, Any]) -> dict[str, Any]:
    if not carrier.get("representable", False):
        return {
            "name": carrier["name"],
            "outcome": "CannotAnswer",
            "admitted": None,
            "reason": carrier["cannot_answer"],
            "predecessor_outcome": carrier["predecessor_outcome"],
        }
    forward = _forward_claims(carrier)
    failures: list[str] = []
    terminal_positions = _positions(carrier, "terminal")
    declared = {terminal["reference"] for terminal in carrier["terminals"]}
    if set(terminal_positions) != declared or any(
        len(rows) != 1 for rows in terminal_positions.values()
    ):
        failures.append("terminal backlinks are not exact and one-to-one")
    if not carrier["schedule"]:
        failures.append("schedule is empty")
    else:
        final = carrier["schedule"][-1]
        if final["effect"]["kind"] != "terminal" or final["guard_atom"] is not None:
            failures.append("final occurrence is not an unconditional fallback terminal")
    if not forward["all_valid"]:
        failures.append("forward claim state contains an invalid transfer")
    terminal_rows: list[dict[str, Any]] = []
    for terminal in carrier["terminals"]:
        passed, terminal_failures = _terminal_contract(carrier, terminal, forward)
        terminal_rows.append(
            {
                "reference": terminal["reference"],
                "passed": passed,
                "failures": terminal_failures,
                "active_live_claims": [
                    claims
                    for claims, _valid in forward["visits"].get(terminal["reference"], [])
                ],
            }
        )
        failures.extend(
            f"terminal {terminal['reference']}: {failure}" for failure in terminal_failures
        )
    admitted = not failures
    return {
        "name": carrier["name"],
        "outcome": "Affirmative" if admitted else "Refused",
        "admitted": admitted,
        "failures": failures,
        "terminals": terminal_rows,
        "forward_states": len(forward["running"]) + sum(
            len(rows) for rows in forward["visits"].values()
        ),
        "predecessor_outcome": carrier["predecessor_outcome"],
    }


def evaluate(vectors: dict[str, Any]) -> list[dict[str, Any]]:
    return [decide_carrier(carrier) for carrier in vectors["carriers"]]
