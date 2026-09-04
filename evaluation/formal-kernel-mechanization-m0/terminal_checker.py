#!/usr/bin/env python3
"""Independent closed-state decision path for normalized Terminal carriers."""

from __future__ import annotations

from itertools import product
from typing import Any, Iterable


Literal = tuple[bool, int]
FactSet = frozenset[Literal] | None
MustResult = tuple[FactSet, FactSet]


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


def _attempted_whenever(carrier: dict[str, Any], later: int, earlier: int) -> bool:
    if not 0 <= earlier < later < len(carrier["schedule"]):
        return False
    earlier_guard = carrier["schedule"][earlier]["guard_atom"]
    later_guard = carrier["schedule"][later]["guard_atom"]
    return earlier_guard is None or earlier_guard == later_guard


def _union(left: FactSet, right: FactSet) -> FactSet:
    if left is None or right is None:
        return None
    merged = left | right
    if any((not polarity, ordinal) in merged for polarity, ordinal in merged):
        return None
    return merged


def _meet(left: FactSet, right: FactSet) -> FactSet:
    if left is None:
        return right
    if right is None:
        return left
    return left & right


def _conditional(condition: MustResult, when_true: MustResult, when_false: MustResult) -> MustResult:
    return (
        _meet(_union(condition[0], when_true[0]), _union(condition[1], when_false[0])),
        _meet(_union(condition[0], when_true[1]), _union(condition[1], when_false[1])),
    )


def _input_must(ordinal: int, is_boolean: bool) -> MustResult:
    if not is_boolean:
        return frozenset(), frozenset()
    return frozenset({(True, ordinal)}), frozenset({(False, ordinal)})


def _false_must() -> MustResult:
    return None, frozenset()


def _true_must() -> MustResult:
    return frozenset(), None


def _conjunction_must(inputs: list[int], kinds: list[bool]) -> MustResult:
    if not inputs:
        return _true_must()
    ordinal = inputs[0]
    condition = _input_must(ordinal, kinds[ordinal] if ordinal < len(kinds) else False)
    if len(inputs) == 1:
        return condition
    return _conditional(condition, _conjunction_must(inputs[1:], kinds), _false_must())


def _must(term: dict[str, Any] | None, kinds: list[bool]) -> MustResult:
    if term is None:
        return frozenset(), frozenset()
    kind = term["kind"]
    if kind == "identity":
        ordinal = int(term["input"])
        return _input_must(ordinal, kinds[ordinal] if ordinal < len(kinds) else False)
    if kind == "conjunction":
        return _conjunction_must([int(item) for item in term["inputs"]], kinds)
    if kind == "true":
        return _true_must()
    if kind == "false":
        return _false_must()
    if kind == "contradiction":
        ordinal = int(term["input"])
        variable = _input_must(ordinal, kinds[ordinal] if ordinal < len(kinds) else False)
        negation = _conditional(variable, _false_must(), _true_must())
        return _conditional(variable, negation, _false_must())
    raise ValueError(f"unknown compact guard term {term!r}")


def _region(carrier: dict[str, Any], occurrence: int) -> dict[str, Any]:
    schedule = carrier["schedule"]
    if not 0 <= occurrence < len(schedule):
        return {"required_true": set(), "required_false": set(), "impossible": True}
    guard = schedule[occurrence]["guard_atom"]
    required_true = set() if guard is None else {guard}
    required_false: set[int] = set()
    earlier_always = False
    for row in schedule[:occurrence]:
        if row["effect"]["kind"] != "terminal":
            continue
        if row["guard_atom"] is None:
            earlier_always = True
        else:
            required_false.add(row["guard_atom"])
    return {
        "required_true": required_true,
        "required_false": required_false,
        "impossible": earlier_always or bool(required_true & required_false),
    }


def _boundary_region(carrier: dict[str, Any], opening: dict[str, Any]) -> dict[str, Any]:
    if opening["kind"] == "initially":
        return {"required_true": set(), "required_false": set(), "impossible": False}
    if opening["kind"] != "before-occurrence":
        raise ValueError(f"unknown scope opening {opening!r}")
    occurrence = int(opening["occurrence"])
    required_false: set[int] = set()
    earlier_always = False
    for row in carrier["schedule"][:occurrence]:
        if row["effect"]["kind"] != "terminal":
            continue
        if row["guard_atom"] is None:
            earlier_always = True
        else:
            required_false.add(row["guard_atom"])
    return {
        "required_true": set(),
        "required_false": required_false,
        "impossible": earlier_always,
    }


def _implies(left: dict[str, Any], right: dict[str, Any]) -> bool:
    return right["required_true"] <= left["required_true"] and right["required_false"] <= left["required_false"]


def _disjoint(left: dict[str, Any], right: dict[str, Any]) -> bool:
    return bool(
        left["required_true"] & right["required_false"]
        or right["required_true"] & left["required_false"]
    )


def _available_claims(carrier: dict[str, Any], occurrence: int) -> list[dict[str, Any]]:
    def available(claim: dict[str, Any]) -> bool:
        source = claim["source"]
        if source["kind"] == "reduction-output":
            return source["occurrence"] < occurrence
        if source["kind"] != "initial-claim":
            raise ValueError(f"unknown claim source {source!r}")
        opening = source["opening"]
        return opening["kind"] == "initially" or opening["occurrence"] <= occurrence

    return [claim for claim in carrier["claims"] if available(claim)]


def _source_region(carrier: dict[str, Any], claim: dict[str, Any]) -> dict[str, Any]:
    source = claim["source"]
    if source["kind"] == "initial-claim":
        return _boundary_region(carrier, source["opening"])
    if source["kind"] == "reduction-output":
        return _region(carrier, source["occurrence"])
    raise ValueError(f"unknown claim source {source!r}")


def _occurrence_coercion_source_region(
    carrier: dict[str, Any], claim: dict[str, Any]
) -> dict[str, Any]:
    source = claim["source"]
    if source["kind"] == "initial-claim":
        opening = source["opening"]
        if opening["kind"] == "initially":
            return _boundary_region(carrier, opening)
        return _region(carrier, opening["occurrence"])
    return _region(carrier, source["occurrence"])


def _earlier_consumers(claim: dict[str, Any], occurrence: int) -> list[int]:
    return [consumer for consumer in claim["linear_consumers"] if consumer < occurrence]


def _claim_status_with_source(
    carrier: dict[str, Any],
    claim: dict[str, Any],
    occurrence: int,
    source_region: dict[str, Any],
) -> str:
    target = _region(carrier, occurrence)
    consumers = [_region(carrier, row) for row in _earlier_consumers(claim, occurrence)]
    live = _implies(target, source_region) and all(
        _disjoint(target, consumer) for consumer in consumers
    )
    if live:
        return "Live"
    dead = _disjoint(target, source_region) or any(
        _implies(target, consumer) for consumer in consumers
    )
    return "Dead" if dead else "Unknown"


def _claim_status(carrier: dict[str, Any], claim: dict[str, Any], occurrence: int) -> str:
    return _claim_status_with_source(
        carrier, claim, occurrence, _source_region(carrier, claim)
    )


def _occurrence_coercion_claim_status(
    carrier: dict[str, Any], claim: dict[str, Any], occurrence: int
) -> str:
    return _claim_status_with_source(
        carrier, claim, occurrence, _occurrence_coercion_source_region(carrier, claim)
    )


def _claim_well_formed(carrier: dict[str, Any], claim: dict[str, Any], occurrence: int) -> bool:
    source = claim["source"]
    if source["kind"] == "reduction-output":
        source_ok = (
            0 <= source["occurrence"] < occurrence
            and source["occurrence"] < len(carrier["schedule"])
        )
    elif source["kind"] == "initial-claim":
        opening = source["opening"]
        if opening["kind"] == "initially":
            source_ok = source["scope"] == 0
        else:
            boundary = opening["occurrence"]
            source_ok = (
                0 <= boundary <= occurrence
                and boundary < len(carrier["schedule"])
                and source["scope"] in carrier["schedule"][boundary]["openings_before"]
            )
    else:
        source_ok = False
    consumers_ok = all(
        0 <= consumer < len(carrier["schedule"])
        for consumer in _earlier_consumers(claim, occurrence)
    )
    return source_ok and consumers_ok


def _strictly_increasing(values: list[int]) -> bool:
    return all(left < right for left, right in zip(values, values[1:]))


def _guard_holds(guard: int | None, valuation: dict[int, bool]) -> bool:
    return guard is None or valuation[guard]


def _attempted(carrier: dict[str, Any], occurrence: int, valuation: dict[int, bool]) -> bool:
    if not 0 <= occurrence < len(carrier["schedule"]):
        return False
    row = carrier["schedule"][occurrence]
    return _guard_holds(row["guard_atom"], valuation) and not any(
        prior["effect"]["kind"] == "terminal"
        and _guard_holds(prior["guard_atom"], valuation)
        for prior in carrier["schedule"][:occurrence]
    )


def _valuations(carrier: dict[str, Any]) -> Iterable[dict[int, bool]]:
    atoms = sorted(
        {row["guard_atom"] for row in carrier["schedule"] if row["guard_atom"] is not None}
    )
    for values in product((False, True), repeat=len(atoms)):
        yield dict(zip(atoms, values, strict=True))


def _region_holds(region: dict[str, Any], valuation: dict[int, bool]) -> bool:
    return not region["impossible"] and all(
        valuation[atom] for atom in region["required_true"]
    ) and all(not valuation[atom] for atom in region["required_false"])


def _boundary_reached(
    carrier: dict[str, Any], opening: dict[str, Any], valuation: dict[int, bool]
) -> bool:
    if opening["kind"] == "initially":
        return True
    occurrence = int(opening["occurrence"])
    return not any(
        prior["effect"]["kind"] == "terminal"
        and _guard_holds(prior["guard_atom"], valuation)
        for prior in carrier["schedule"][:occurrence]
    )


def _source_exists(
    carrier: dict[str, Any], claim: dict[str, Any], valuation: dict[int, bool]
) -> bool:
    source = claim["source"]
    if source["kind"] == "initial-claim":
        return _boundary_reached(carrier, source["opening"], valuation)
    return _attempted(carrier, source["occurrence"], valuation)


def _claim_live_at(
    carrier: dict[str, Any], claim: dict[str, Any], occurrence: int, valuation: dict[int, bool]
) -> bool:
    return _source_exists(carrier, claim, valuation) and not any(
        _attempted(carrier, consumer, valuation)
        for consumer in _earlier_consumers(claim, occurrence)
    )


def _finite_soundness(carrier: dict[str, Any]) -> dict[str, bool]:
    valuations = list(_valuations(carrier))
    region_exact = True
    unreachable_exact = True
    for occurrence in range(len(carrier["schedule"])):
        region = _region(carrier, occurrence)
        attempted_values = [_attempted(carrier, occurrence, valuation) for valuation in valuations]
        region_exact &= all(
            attempted == _region_holds(region, valuation)
            for attempted, valuation in zip(attempted_values, valuations, strict=True)
        )
        unreachable_exact &= region["impossible"] == (not any(attempted_values))
    boundary_exact = True
    source_region_exact = True
    live_sound = True
    dead_sound = True
    for claim in carrier["claims"]:
        source = claim["source"]
        if source["kind"] == "initial-claim":
            boundary_exact &= all(
                _boundary_reached(carrier, source["opening"], valuation)
                == _region_holds(_boundary_region(carrier, source["opening"]), valuation)
                for valuation in valuations
            )
        source_region_exact &= all(
            _source_exists(carrier, claim, valuation)
            == _region_holds(_source_region(carrier, claim), valuation)
            for valuation in valuations
        )
    terminal_positions = _positions(carrier, "terminal")
    for terminal in carrier["terminals"]:
        occurrence = _unique_position(terminal_positions, terminal["reference"])
        if occurrence is None:
            continue
        for claim in _available_claims(carrier, occurrence):
            status = _claim_status(carrier, claim, occurrence)
            attempted_valuations = [
                valuation for valuation in valuations if _attempted(carrier, occurrence, valuation)
            ]
            if status == "Live":
                live_sound &= all(
                    _claim_live_at(carrier, claim, occurrence, valuation)
                    for valuation in attempted_valuations
                )
            elif status == "Dead":
                dead_sound &= all(
                    not _claim_live_at(carrier, claim, occurrence, valuation)
                    for valuation in attempted_valuations
                )
    return {
        "region_exact": region_exact,
        "unreachable_exact": unreachable_exact,
        "boundary_region_exact": boundary_exact,
        "claim_source_region_exact": source_region_exact,
        "claim_live_sound": live_sound,
        "claim_dead_sound": dead_sound,
    }


def _terminal_contract(
    carrier: dict[str, Any], terminal: dict[str, Any]
) -> tuple[bool, list[str], dict[str, Any]]:
    failures: list[str] = []
    terminal_positions = _positions(carrier, "terminal")
    check_positions = _positions(carrier, "check")
    reduction_positions = _positions(carrier, "reduction")
    terminal_position = _unique_position(terminal_positions, terminal["reference"])
    if terminal_position is None:
        failures.append("terminal backlink is not unique")
        terminal_position = len(carrier["schedule"]) + terminal["reference"] + 1

    local_claims = _available_claims(carrier, terminal_position)
    if len(terminal["guard_inputs"]) != len(terminal["guard_input_is_boolean"]):
        failures.append("guard input type coordinates do not match the input arity")
    for label in ("required_checks", "required_reductions", "terminal_claims"):
        if not _strictly_increasing(terminal[label]):
            failures.append(f"{label} is not sorted-unique")
    if not _strictly_increasing([claim["reference"] for claim in local_claims]):
        failures.append("claim references are not sorted-unique")
    if any(not _strictly_increasing(claim["linear_consumers"]) for claim in local_claims):
        failures.append("claim consumer coordinates are not sorted-unique")
    if any(not _claim_well_formed(carrier, claim, terminal_position) for claim in local_claims):
        failures.append("claim binding is not well formed at the terminal")

    region = _region(carrier, terminal_position)
    when_true, _when_false = _must(
        terminal["guard_term"], terminal["guard_input_is_boolean"]
    )
    if region["impossible"]:
        failures.append("terminal Region is Impossible")
    if terminal["guard_term"] is not None and when_true is None:
        failures.append("terminal GuardTerm has Impossible MustWhenTrue")

    positives = set() if when_true is None else {
        ordinal for polarity, ordinal in when_true if polarity
    }
    for check in terminal["required_checks"]:
        check_position = _unique_position(check_positions, check)
        if check_position is None:
            failures.append(f"required Check {check} has no unique occurrence")
            continue
        if not _attempted_whenever(carrier, terminal_position, check_position):
            failures.append(f"required Check {check} is not attempted whenever the terminal is")
        if terminal["guard_term"] is None:
            failures.append(f"required Check {check} has no terminal GuardTerm")
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

    valuations = list(_valuations(carrier))
    reaching = [
        valuation
        for valuation in valuations
        if _attempted(carrier, terminal_position, valuation)
    ]
    statuses = [
        {
            "reference": claim["reference"],
            "status": _claim_status(carrier, claim, terminal_position),
            "occurrence_coercion_status": _occurrence_coercion_claim_status(
                carrier, claim, terminal_position
            ),
            "reaching_paths": len(reaching),
            "live_paths": sum(
                _claim_live_at(carrier, claim, terminal_position, valuation)
                for valuation in reaching
            ),
        }
        for claim in local_claims
    ]
    if any(row["status"] == "Unknown" for row in statuses):
        failures.append("at least one claim has Unknown ClaimStatus")
    live_claims = [row["reference"] for row in statuses if row["status"] == "Live"]
    if live_claims != terminal["terminal_claims"]:
        failures.append(f"live claims {live_claims} differ from authored {terminal['terminal_claims']}")
    details = {
        "region_impossible": region["impossible"],
        "claim_bindings_well_formed": all(
            _claim_well_formed(carrier, claim, terminal_position) for claim in local_claims
        ),
        "live_claims": live_claims,
        "claim_statuses": statuses,
    }
    return not failures, failures, details


def decide_carrier(carrier: dict[str, Any]) -> dict[str, Any]:
    if not carrier.get("representable", False):
        return {
            "name": carrier["name"],
            "outcome": "CannotAnswer",
            "admitted": None,
            "reason": carrier["cannot_answer"],
            "predecessor_outcome": carrier["predecessor_outcome"],
        }
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
    terminal_rows: list[dict[str, Any]] = []
    for terminal in carrier["terminals"]:
        passed, terminal_failures, details = _terminal_contract(carrier, terminal)
        terminal_rows.append(
            {
                "reference": terminal["reference"],
                "passed": passed,
                "failures": terminal_failures,
                **details,
            }
        )
        failures.extend(
            f"terminal {terminal['reference']}: {failure}" for failure in terminal_failures
        )
    soundness = _finite_soundness(carrier)
    if not all(soundness.values()):
        failures.append("finite independent soundness oracle disagrees with the closed laws")
    admitted = not failures
    return {
        "name": carrier["name"],
        "outcome": "Affirmative" if admitted else "Refused",
        "admitted": admitted,
        "failures": failures,
        "terminals": terminal_rows,
        "soundness": soundness,
        "predecessor_outcome": carrier["predecessor_outcome"],
    }


def evaluate(vectors: dict[str, Any]) -> list[dict[str, Any]]:
    return [decide_carrier(carrier) for carrier in vectors["carriers"]]
