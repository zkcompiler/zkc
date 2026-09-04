"""Independent exhaustive oracle for the bounded B5B1 Terminal contracts.

This file intentionally imports neither ``model.py`` nor a predecessor
analyzer.  It evaluates the raw fixture carrier by assignment enumeration.
Enumeration is an oracle for finite research cases, not the selected target
admission algorithm.
"""

from __future__ import annotations

from itertools import product
from typing import Any


MAX_ITEMS = 1 << 14


class OracleError(ValueError):
    pass


def _object(value: object, keys: set[str], label: str) -> dict[str, Any]:
    if type(value) is not dict or set(value) != keys:
        raise OracleError(f"{label} shape differs")
    return value


def _list(value: object, label: str) -> list[Any]:
    if type(value) is not list or len(value) > MAX_ITEMS:
        raise OracleError(f"{label} is not one bounded list")
    return value


def _ref(value: object, label: str) -> int:
    if type(value) is not int or value < 0:
        raise OracleError(f"{label} is not a natural reference")
    return value


def _canonical_refs(value: object, label: str) -> list[int]:
    result = [_ref(item, label) for item in _list(value, label)]
    if result != sorted(set(result)):
        raise OracleError(f"{label} is not ascending and unique")
    return result


def _eval_term(value: object, environment: tuple[bool, ...]) -> bool:
    if type(value) is not dict or type(value.get("tag")) is not str:
        raise OracleError("term has no exact tag")
    tag = value["tag"]
    if tag == "Literal":
        item = _object(value, {"tag", "value"}, "Literal")
        if type(item["value"]) is not bool:
            raise OracleError("literal is not Boolean")
        return item["value"]
    if tag == "Variable":
        item = _object(value, {"tag", "index"}, "Variable")
        index = _ref(item["index"], "variable index")
        if index >= len(environment):
            raise OracleError("variable is outside its environment")
        return environment[index]
    if tag == "Let":
        item = _object(value, {"tag", "bound", "body"}, "Let")
        bound = _eval_term(item["bound"], environment)
        return _eval_term(item["body"], (bound, *environment))
    if tag == "Conditional":
        item = _object(
            value,
            {"tag", "condition", "when_true", "when_false"},
            "Conditional",
        )
        condition = _eval_term(item["condition"], environment)
        branch = item["when_true"] if condition else item["when_false"]
        return _eval_term(branch, environment)
    if tag == "PrimitiveCall":
        item = _object(value, {"tag", "primitive", "arguments"}, "PrimitiveCall")
        arguments = tuple(
            _eval_term(argument, environment)
            for argument in _list(item["arguments"], "primitive arguments")
        )
        if item["primitive"] == "foundation.bool-and-v0" and len(arguments) == 2:
            return arguments[0] and arguments[1]
        if item["primitive"] == "foundation.bool-or-v0" and len(arguments) == 2:
            return arguments[0] or arguments[1]
        if item["primitive"] == "foundation.bool-xor-v0" and len(arguments) == 2:
            return arguments[0] != arguments[1]
        raise OracleError("primitive denotation is absent from the finite oracle")
    raise OracleError("term tag is outside the finite oracle")


def exact_boolean_facts(algorithm_value: object) -> dict[str, Any]:
    """Compute extensional must-literals for one small Boolean algorithm."""

    algorithm = _object(
        algorithm_value,
        {"algorithm_kind", "ordered_inputs", "term"},
        "algorithm",
    )
    input_count = _ref(algorithm["ordered_inputs"], "ordered input count")
    if input_count > 8:
        raise OracleError("finite Boolean oracle is capped at eight inputs")
    outputs: dict[bool, list[tuple[bool, ...]]] = {False: [], True: []}
    for assignment in product((False, True), repeat=input_count):
        outputs[_eval_term(algorithm["term"], assignment)].append(assignment)
    result: dict[str, Any] = {}
    for outcome, key in ((True, "when_true"), (False, "when_false")):
        rows = outputs[outcome]
        literals: list[list[object]] = []
        for index in range(input_count):
            if rows and all(row[index] for row in rows):
                literals.append([index, True])
            elif rows and all(not row[index] for row in rows):
                literals.append([index, False])
        result[key] = {"possible": bool(rows), "literals": literals}
    result["assignments"] = 1 << input_count
    return result


def _parse(value: object) -> dict[str, Any]:
    root = _object(
        value,
        {"claims", "reductions", "checks", "terminals", "occurrences"},
        "program",
    )
    claims: list[dict[str, Any]] = []
    for raw in _list(root["claims"], "claims"):
        item = _object(raw, {"usage", "source"}, "claim")
        if item["usage"] not in {"Linear", "Reusable"}:
            raise OracleError("claim usage differs")
        source = _object(item["source"], {"kind", "reduction", "output"}, "source")
        if source["kind"] == "Initial":
            if source["reduction"] is not None or source["output"] is not None:
                raise OracleError("Initial source carries fields")
            parsed_source = {"kind": "Initial", "reduction": None, "output": None}
        elif source["kind"] == "ReductionOutput":
            parsed_source = {
                "kind": "ReductionOutput",
                "reduction": _ref(source["reduction"], "source Reduction"),
                "output": _ref(source["output"], "source output"),
            }
        else:
            raise OracleError("claim source differs")
        claims.append({"usage": item["usage"], "source": parsed_source})

    reductions: list[dict[str, list[int]]] = []
    for raw in _list(root["reductions"], "reductions"):
        item = _object(raw, {"inputs", "outputs"}, "Reduction")
        inputs = [
            _ref(entry, "Reduction input") for entry in _list(item["inputs"], "inputs")
        ]
        outputs = [
            _ref(entry, "Reduction output")
            for entry in _list(item["outputs"], "outputs")
        ]
        if (
            not inputs
            or len(set(inputs)) != len(inputs)
            or len(set(outputs)) != len(outputs)
        ):
            raise OracleError("Reduction aggregate differs")
        reductions.append({"inputs": inputs, "outputs": outputs})

    checks: list[dict[str, str]] = []
    for raw in _list(root["checks"], "checks"):
        item = _object(raw, {"label"}, "Check")
        if type(item["label"]) is not str or not item["label"]:
            raise OracleError("Check label differs")
        checks.append({"label": item["label"]})

    terminals: list[dict[str, Any]] = []
    for raw in _list(root["terminals"], "terminals"):
        item = _object(
            raw,
            {
                "verdict",
                "public_outputs",
                "required_true_checks",
                "required_applied_reductions",
                "terminal_claims",
            },
            "Terminal",
        )
        if item["verdict"] not in {"Accept", "Reject", "Abort"}:
            raise OracleError("Terminal verdict differs")
        outputs = _list(item["public_outputs"], "public outputs")
        if any(type(entry) is not str or not entry for entry in outputs):
            raise OracleError("public output differs")
        terminals.append(
            {
                "verdict": item["verdict"],
                "public_outputs": outputs,
                "required_true_checks": _canonical_refs(
                    item["required_true_checks"], "required Check set"
                ),
                "required_applied_reductions": _canonical_refs(
                    item["required_applied_reductions"], "required Reduction set"
                ),
                "terminal_claims": _canonical_refs(
                    item["terminal_claims"], "terminal Claim set"
                ),
            }
        )

    occurrences: list[dict[str, Any]] = []
    for raw in _list(root["occurrences"], "occurrences"):
        item = _object(raw, {"guard", "effect"}, "occurrence")
        effect = _object(item["effect"], {"kind", "ref"}, "effect")
        if effect["kind"] not in {"Check", "Reduction", "Terminal"}:
            raise OracleError("effect kind differs")
        guard = item["guard"]
        if guard is not None:
            guard = _object(
                guard, {"algorithm", "evaluation_contract", "inputs"}, "guard"
            )
            algorithm = _object(
                guard["algorithm"],
                {"algorithm_kind", "ordered_inputs", "term"},
                "guard algorithm",
            )
            inputs: list[dict[str, Any]] = []
            for source in _list(guard["inputs"], "guard inputs"):
                source = _object(source, {"kind", "ref"}, "guard input")
                if source["kind"] not in {"PublicBoolean", "CheckOutput"}:
                    raise OracleError("guard input kind differs")
                inputs.append(
                    {"kind": source["kind"], "ref": _ref(source["ref"], "guard input")}
                )
            if algorithm["ordered_inputs"] != len(inputs):
                raise OracleError("guard ABI differs")
            guard = {"algorithm": algorithm, "inputs": inputs}
        occurrences.append(
            {
                "guard": guard,
                "effect": {
                    "kind": effect["kind"],
                    "ref": _ref(effect["ref"], "effect ref"),
                },
            }
        )
    if not terminals or not occurrences:
        raise OracleError("Terminal and occurrence tables must be nonempty")
    return {
        "claims": claims,
        "reductions": reductions,
        "checks": checks,
        "terminals": terminals,
        "occurrences": occurrences,
    }


def _positions(program: dict[str, Any]) -> dict[str, dict[int, int]]:
    positions: dict[str, dict[int, list[int]]] = {
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
    if any(len(rows) != 1 for table in positions.values() for rows in table.values()):
        raise OracleError("backlink is not one-to-one")
    return {
        kind: {reference: rows[0] for reference, rows in table.items()}
        for kind, table in positions.items()
    }


def _static_validate(program: dict[str, Any]) -> None:
    positions = _positions(program)
    final = program["occurrences"][-1]
    if final["guard"] is not None or final["effect"]["kind"] != "Terminal":
        raise OracleError("final fallback differs")
    expected_outputs: dict[tuple[int, int], int] = {}
    for reduction_ref, reduction in enumerate(program["reductions"]):
        if any(
            reference >= len(program["claims"])
            for reference in (*reduction["inputs"], *reduction["outputs"])
        ):
            raise OracleError("Reduction Claim reference is absent")
        for output, claim_ref in enumerate(reduction["outputs"]):
            expected_outputs[(reduction_ref, output)] = claim_ref
    actual_outputs: dict[tuple[int, int], int] = {}
    for claim_ref, claim in enumerate(program["claims"]):
        source = claim["source"]
        if source["kind"] == "Initial":
            continue
        coordinate = (source["reduction"], source["output"])
        if coordinate in actual_outputs:
            raise OracleError("Claim output aliases")
        actual_outputs[coordinate] = claim_ref
    if actual_outputs != expected_outputs:
        raise OracleError("Claim output closure differs")
    for terminal in program["terminals"]:
        if any(
            reference >= len(program["checks"])
            for reference in terminal["required_true_checks"]
        ):
            raise OracleError("required Check is absent")
        if any(
            reference >= len(program["reductions"])
            for reference in terminal["required_applied_reductions"]
        ):
            raise OracleError("required Reduction is absent")
        if any(
            reference >= len(program["claims"])
            for reference in terminal["terminal_claims"]
        ):
            raise OracleError("terminal Claim is absent")
    for position, occurrence in enumerate(program["occurrences"]):
        guard = occurrence["guard"]
        if guard is None:
            continue
        for source in guard["inputs"]:
            if source["kind"] == "CheckOutput" and (
                source["ref"] not in positions["Check"]
                or positions["Check"][source["ref"]] >= position
            ):
                raise OracleError("guard Check output is unavailable")


def _guard_value(
    guard: dict[str, Any] | None,
    public_values: dict[int, bool],
    check_outcomes: dict[int, bool],
) -> bool:
    if guard is None:
        return True
    values: list[bool] = []
    for source in guard["inputs"]:
        if source["kind"] == "PublicBoolean":
            values.append(public_values[source["ref"]])
        elif source["ref"] in check_outcomes:
            values.append(check_outcomes[source["ref"]])
        else:
            raise OracleError("guard reads an inactive Check")
    return _eval_term(guard["algorithm"]["term"], tuple(values))


def _execute(
    program: dict[str, Any],
    public_values: dict[int, bool],
    assigned_checks: dict[int, bool],
) -> tuple[bool, str, str | None]:
    live = {
        index
        for index, claim in enumerate(program["claims"])
        if claim["source"]["kind"] == "Initial"
    }
    produced = set(live)
    applied: set[int] = set()
    check_outcomes: dict[int, bool] = {}
    try:
        for occurrence in program["occurrences"]:
            if not _guard_value(occurrence["guard"], public_values, check_outcomes):
                continue
            effect = occurrence["effect"]
            reference = effect["ref"]
            if effect["kind"] == "Check":
                check_outcomes[reference] = assigned_checks[reference]
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
                applied.add(reference)
                continue
            terminal = program["terminals"][reference]
            if any(
                check_outcomes.get(check_ref) is not True
                for check_ref in terminal["required_true_checks"]
            ):
                return False, "required-check-not-true", terminal["verdict"]
            if any(
                reduction_ref not in applied
                for reduction_ref in terminal["required_applied_reductions"]
            ):
                return False, "required-reduction-not-applied", terminal["verdict"]
            if terminal["terminal_claims"] != sorted(live):
                return False, "terminal-claim-closure", terminal["verdict"]
            return True, "terminal", terminal["verdict"]
    except (KeyError, OracleError) as error:
        return False, "runtime:" + str(error), None
    return False, "no-terminal", None


def evaluate_all(program_value: object) -> dict[str, Any]:
    """Exhaust the finite public-input and Check-result assignments."""

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
    public_refs = sorted(
        {
            source["ref"]
            for occurrence in program["occurrences"]
            if occurrence["guard"] is not None
            for source in occurrence["guard"]["inputs"]
            if source["kind"] == "PublicBoolean"
        }
    )
    check_refs = list(range(len(program["checks"])))
    violations: set[str] = set()
    counts: dict[str, int] = {}
    first_counterexample: dict[str, Any] | None = None
    assignments = 0
    for public_bits in product((False, True), repeat=len(public_refs)):
        public_values = dict(zip(public_refs, public_bits, strict=True))
        for check_bits in product((False, True), repeat=len(check_refs)):
            check_values = dict(zip(check_refs, check_bits, strict=True))
            assignments += 1
            valid, reason, terminal = _execute(program, public_values, check_values)
            if valid:
                assert terminal is not None
                counts[terminal] = counts.get(terminal, 0) + 1
                continue
            violations.add(reason)
            if first_counterexample is None:
                first_counterexample = {
                    "public": {str(key): value for key, value in public_values.items()},
                    "checks": {str(key): value for key, value in check_values.items()},
                    "reason": reason,
                    "terminal": terminal,
                }
    return {
        "valid": not violations,
        "assignments": assignments,
        "violations": sorted(violations),
        "terminal_counts": dict(sorted(counts.items())),
        "first_counterexample": first_counterexample,
    }


def hidden_gating_counterexample() -> dict[str, bool | str]:
    """Return the minimal linearity failure caused by implicit Check gating.

    The old authored guard ``g`` lets Reduction 0 consume the linear Claim.
    An implementation then secretly selects Accept only under ``g AND check``.
    With ``g=true`` and ``check=false``, execution falls through and attempts
    the otherwise-unconditional alternative Reduction 1 on the dead Claim.
    """

    return {
        "g": True,
        "check": False,
        "reduction_0_applied": True,
        "accept_selected": False,
        "reduction_1_attempted": True,
        "violation": "linear-claim-consumed-twice",
    }
