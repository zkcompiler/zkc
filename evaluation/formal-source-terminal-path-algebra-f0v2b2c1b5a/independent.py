"""Assignment-enumerating oracle for the bounded B5A terminal fragment.

This module intentionally does not import ``model.py``.  Enumeration is used
only as an independent finite oracle for the research fixtures; it is not the
candidate target admission algorithm.
"""

from __future__ import annotations

from itertools import product
from typing import Any


MAX_ITEMS = 1 << 14


class OracleError(ValueError):
    pass


def _dict(value: object, keys: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != keys:
        raise OracleError(f"{label} shape differs")
    return value


def _list(value: object, label: str) -> list[Any]:
    if type(value) is not list or len(value) > MAX_ITEMS:
        raise OracleError(f"{label} is not bounded list")
    return value


def _ref(value: object, label: str) -> int:
    if type(value) is not int or value < 0:
        raise OracleError(f"{label} is not natural reference")
    return value


def _guard(value: object) -> str | None:
    if value is None:
        return None
    if type(value) is not str or not value or len(value) > 128:
        raise OracleError("guard differs")
    return value


def _parse(value: object) -> dict[str, Any]:
    root = _dict(
        value,
        {"claims", "reductions", "checks", "terminals", "occurrences"},
        "program",
    )
    claims: list[dict[str, Any]] = []
    for raw in _list(root["claims"], "claims"):
        item = _dict(raw, {"usage", "source"}, "claim")
        if item["usage"] not in {"Linear", "Reusable"}:
            raise OracleError("claim usage differs")
        source = _dict(item["source"], {"kind", "reduction", "output"}, "source")
        if source["kind"] == "Initial":
            if source["reduction"] is not None or source["output"] is not None:
                raise OracleError("Initial source carries fields")
            parsed_source = {"kind": "Initial", "reduction": None, "output": None}
        elif source["kind"] == "ReductionOutput":
            parsed_source = {
                "kind": "ReductionOutput",
                "reduction": _ref(source["reduction"], "source reduction"),
                "output": _ref(source["output"], "source output"),
            }
        else:
            raise OracleError("claim source differs")
        claims.append({"usage": item["usage"], "source": parsed_source})

    reductions: list[dict[str, Any]] = []
    for raw in _list(root["reductions"], "reductions"):
        item = _dict(raw, {"inputs", "outputs"}, "reduction")
        inputs = [
            _ref(entry, "reduction input") for entry in _list(item["inputs"], "inputs")
        ]
        outputs = [
            _ref(entry, "reduction output")
            for entry in _list(item["outputs"], "outputs")
        ]
        if (
            not inputs
            or len(set(inputs)) != len(inputs)
            or len(set(outputs)) != len(outputs)
        ):
            raise OracleError("reduction aggregate differs")
        reductions.append({"inputs": inputs, "outputs": outputs})

    checks: list[dict[str, str]] = []
    for raw in _list(root["checks"], "checks"):
        item = _dict(raw, {"label"}, "check")
        if type(item["label"]) is not str or not item["label"]:
            raise OracleError("check label differs")
        checks.append({"label": item["label"]})

    terminals: list[dict[str, Any]] = []
    for raw in _list(root["terminals"], "terminals"):
        item = _dict(
            raw,
            {"verdict", "public_outputs", "required_true_checks", "dispositions"},
            "terminal",
        )
        if item["verdict"] not in {"Accept", "Reject", "Abort"}:
            raise OracleError("terminal verdict differs")
        outputs = _list(item["public_outputs"], "public outputs")
        if any(type(entry) is not str or not entry for entry in outputs):
            raise OracleError("public output differs")
        required = [
            _ref(entry, "required check")
            for entry in _list(item["required_true_checks"], "required checks")
        ]
        dispositions: list[tuple[int, str]] = []
        for raw_entry in _list(item["dispositions"], "dispositions"):
            entry = _list(raw_entry, "disposition")
            if len(entry) != 2 or entry[1] not in {"Consume", "Discharge"}:
                raise OracleError("disposition differs")
            dispositions.append((_ref(entry[0], "disposed claim"), entry[1]))
        terminals.append(
            {
                "verdict": item["verdict"],
                "public_outputs": list(outputs),
                "required_true_checks": required,
                "dispositions": dispositions,
            }
        )

    occurrences: list[dict[str, Any]] = []
    for raw in _list(root["occurrences"], "occurrences"):
        item = _dict(raw, {"guard", "effect"}, "occurrence")
        effect = _dict(item["effect"], {"kind", "ref"}, "effect")
        if effect["kind"] not in {"Check", "Reduction", "Terminal"}:
            raise OracleError("effect differs")
        occurrences.append(
            {
                "guard": _guard(item["guard"]),
                "effect": {
                    "kind": effect["kind"],
                    "ref": _ref(effect["ref"], "effect reference"),
                },
            }
        )
    if not terminals or not occurrences:
        raise OracleError("terminal and occurrence tables must be nonempty")
    return {
        "claims": claims,
        "reductions": reductions,
        "checks": checks,
        "terminals": terminals,
        "occurrences": occurrences,
    }


def _static_validate(program: dict[str, Any]) -> None:
    positions = {
        "Check": {index: [] for index in range(len(program["checks"]))},
        "Reduction": {index: [] for index in range(len(program["reductions"]))},
        "Terminal": {index: [] for index in range(len(program["terminals"]))},
    }
    for position, occurrence in enumerate(program["occurrences"]):
        effect = occurrence["effect"]
        table = positions[effect["kind"]]
        if effect["ref"] not in table:
            raise OracleError("effect reference is absent")
        table[effect["ref"]].append(position)
    if any(len(items) != 1 for table in positions.values() for items in table.values()):
        raise OracleError("backlink is not one-to-one")
    final = program["occurrences"][-1]
    if final["guard"] is not None or final["effect"]["kind"] != "Terminal":
        raise OracleError("final fallback differs")

    output_sources: dict[tuple[int, int], int] = {}
    for claim_ref, claim in enumerate(program["claims"]):
        source = claim["source"]
        if source["kind"] == "Initial":
            continue
        reduction_ref = source["reduction"]
        output = source["output"]
        if reduction_ref >= len(program["reductions"]):
            raise OracleError("claim source reduction is absent")
        reduction = program["reductions"][reduction_ref]
        if (
            output >= len(reduction["outputs"])
            or reduction["outputs"][output] != claim_ref
        ):
            raise OracleError("claim source coordinate differs")
        coordinate = (reduction_ref, output)
        if coordinate in output_sources:
            raise OracleError("claim output aliases")
        output_sources[coordinate] = claim_ref
    expected = {
        (reduction_ref, output): claim_ref
        for reduction_ref, reduction in enumerate(program["reductions"])
        for output, claim_ref in enumerate(reduction["outputs"])
    }
    if output_sources != expected:
        raise OracleError("claim output closure differs")
    for reduction in program["reductions"]:
        if any(
            reference >= len(program["claims"])
            for reference in (*reduction["inputs"], *reduction["outputs"])
        ):
            raise OracleError("reduction claim reference is absent")
    for terminal in program["terminals"]:
        disposition_refs = [entry[0] for entry in terminal["dispositions"]]
        if any(reference >= len(program["claims"]) for reference in disposition_refs):
            raise OracleError("disposition reference is absent")
        if len(set(disposition_refs)) != len(disposition_refs):
            raise OracleError("disposition repeats")
        if any(
            reference >= len(program["checks"])
            for reference in terminal["required_true_checks"]
        ):
            raise OracleError("required check is absent")


def _execute(
    program: dict[str, Any],
    guards: dict[str, bool],
    check_values: dict[int, bool],
) -> tuple[bool, str, str | None]:
    live = {
        index
        for index, claim in enumerate(program["claims"])
        if claim["source"]["kind"] == "Initial"
    }
    produced = set(live)
    check_outcomes: dict[int, bool] = {}
    for occurrence in program["occurrences"]:
        atom = occurrence["guard"]
        if atom is not None and not guards[atom]:
            continue
        effect = occurrence["effect"]
        reference = effect["ref"]
        if effect["kind"] == "Check":
            check_outcomes[reference] = check_values[reference]
            continue
        if effect["kind"] == "Reduction":
            reduction = program["reductions"][reference]
            if any(claim not in live for claim in reduction["inputs"]):
                return False, "reduction-input-not-live", None
            for claim_ref in reduction["inputs"]:
                if program["claims"][claim_ref]["usage"] == "Linear":
                    live.remove(claim_ref)
            for claim_ref in reduction["outputs"]:
                if claim_ref in produced:
                    return False, "claim-produced-twice", None
                produced.add(claim_ref)
                live.add(claim_ref)
            continue
        terminal = program["terminals"][reference]
        if any(
            check_outcomes.get(check_ref) is not True
            for check_ref in terminal["required_true_checks"]
        ):
            return False, "required-check-not-true", terminal["verdict"]
        dispositions = [entry[0] for entry in terminal["dispositions"]]
        if len(set(dispositions)) != len(dispositions) or set(dispositions) != live:
            return False, "terminal-claim-closure", terminal["verdict"]
        return True, "terminal", terminal["verdict"]
    return False, "no-terminal", None


def evaluate_all(program_value: object) -> dict[str, Any]:
    """Enumerate the finite fixture semantics and retain one counterexample."""

    try:
        program = _parse(program_value)
        _static_validate(program)
    except OracleError as error:
        return {
            "valid": False,
            "assignments": 0,
            "violations": ["static:" + str(error)],
            "terminal_counts": {},
            "first_counterexample": None,
        }

    atoms = sorted(
        {
            occurrence["guard"]
            for occurrence in program["occurrences"]
            if occurrence["guard"] is not None
        }
    )
    required_checks = sorted(
        {
            check_ref
            for terminal in program["terminals"]
            for check_ref in terminal["required_true_checks"]
        }
    )
    violations: set[str] = set()
    terminal_counts: dict[str, int] = {}
    first_counterexample: dict[str, Any] | None = None
    assignments = 0
    for guard_bits in product((False, True), repeat=len(atoms)):
        guards = dict(zip(atoms, guard_bits, strict=True))
        for check_bits in product((False, True), repeat=len(required_checks)):
            checks = {index: True for index in range(len(program["checks"]))}
            checks.update(dict(zip(required_checks, check_bits, strict=True)))
            assignments += 1
            valid, reason, terminal = _execute(program, guards, checks)
            if valid:
                assert terminal is not None
                terminal_counts[terminal] = terminal_counts.get(terminal, 0) + 1
                continue
            violations.add(reason)
            if first_counterexample is None:
                first_counterexample = {
                    "guards": guards,
                    "checks": {str(key): value for key, value in checks.items()},
                    "reason": reason,
                    "terminal": terminal,
                }
    return {
        "valid": not violations,
        "assignments": assignments,
        "violations": sorted(violations),
        "terminal_counts": dict(sorted(terminal_counts.items())),
        "first_counterexample": first_counterexample,
    }
