"""Independent arithmetic and source-read oracle for the representative cases.

This file deliberately imports neither ``model`` nor any PIR evaluator.  It
reads the fixture, applies the four source-shaped formulas directly, and emits
the expected values and leaf-query traces.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
FIXTURE = HERE / "cases" / "representative-witness.json"


class IndependentError(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise IndependentError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def _reject_float(value: str) -> Any:
    raise IndependentError(f"floating-point value is unsupported: {value}")


def load_fixture(path: Path = FIXTURE) -> dict[str, Any]:
    value = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_strict_object,
        parse_float=_reject_float,
        parse_constant=_reject_float,
    )
    if type(value) is not dict or value.get("schema") != (
        "zkc.verifier-derived-query-plan-witness.v0"
    ):
        raise IndependentError("unexpected representative fixture schema")
    if set(value) != {"schema", "field_modulus", "inputs", "oracles"}:
        raise IndependentError("representative fixture has unknown or missing fields")
    return value


def _oracles(fixture: dict[str, Any]) -> dict[str, dict[int, int]]:
    result: dict[str, dict[int, int]] = {}
    for name, entries in fixture["oracles"].items():
        table: dict[int, int] = {}
        for entry in entries:
            if type(entry) is not list or len(entry) != 2:
                raise IndependentError("oracle entry is not an index/value pair")
            index, value = entry
            if type(index) is not int or type(value) is not int or index in table:
                raise IndependentError("oracle entry is malformed or repeated")
            table[index] = value
        result[name] = table
    return result


def _inverse(value: int, modulus: int) -> int:
    value %= modulus
    if value == 0:
        raise IndependentError("zero denominator in independent oracle")
    return pow(value, -1, modulus)


def _interpolate(
    x: int, points: tuple[int, ...], answers: tuple[int, ...], modulus: int
) -> int:
    if not points or len(points) != len(answers) or len(set(points)) != len(points):
        raise IndependentError("invalid interpolation assignment")
    result = 0
    for ordinal, point in enumerate(points):
        numerator = 1
        denominator = 1
        for other_ordinal, other in enumerate(points):
            if ordinal == other_ordinal:
                continue
            numerator = numerator * (x - other) % modulus
            denominator = denominator * (point - other) % modulus
        result += answers[ordinal] * numerator * _inverse(denominator, modulus)
    return result % modulus


def _quotient(
    source_value: int,
    x: int,
    points: tuple[int, ...],
    answers: tuple[int, ...],
    modulus: int,
) -> int:
    interpolation = _interpolate(x, points, answers, modulus)
    denominator = 1
    for point in points:
        denominator = denominator * (x - point) % modulus
    return (source_value - interpolation) * _inverse(denominator, modulus) % modulus


def evaluate(path: Path = FIXTURE) -> dict[str, Any]:
    fixture = load_fixture(path)
    modulus = fixture["field_modulus"]
    inputs = fixture["inputs"]
    oracle = _oracles(fixture)

    circle_x = inputs["circle-index"]
    coefficient = inputs["circle-coefficient"]
    circle_values = (
        oracle["circle-first"][circle_x],
        oracle["circle-second"][circle_x],
        oracle["circle-third"][circle_x],
    )
    circle = (
        circle_values[0]
        + coefficient * circle_values[1]
        + coefficient * coefficient * circle_values[2]
    ) % modulus

    deep_x = inputs["deep-index"]
    deep_first = _quotient(
        oracle["deep-first"][deep_x],
        deep_x,
        tuple(inputs["deep-points-first"]),
        tuple(inputs["deep-answers-first"]),
        modulus,
    )
    deep_second = _quotient(
        oracle["deep-second"][deep_x],
        deep_x,
        tuple(inputs["deep-points-second"]),
        tuple(inputs["deep-answers-second"]),
        modulus,
    )

    stir_points = tuple(inputs["stir-points"])
    stir_answers = tuple(inputs["stir-answers"])

    def stir_value(x: int) -> tuple[int, tuple[str, int]]:
        if x in stir_points:
            return oracle["stir-fill"][x], ("stir-fill", x)
        return (
            _quotient(
                oracle["stir-source"][x],
                x,
                stir_points,
                stir_answers,
                modulus,
            ),
            ("stir-source", x),
        )

    stir_x = inputs["stir-index"]
    stir_negative_x = (-stir_x) % modulus
    stir_positive, stir_positive_query = stir_value(stir_x)
    stir_negative, stir_negative_query = stir_value(stir_negative_x)
    stir_even = (stir_positive + stir_negative) * _inverse(2, modulus) % modulus
    stir_odd = (
        (stir_positive - stir_negative)
        * _inverse(2 * stir_x, modulus)
        % modulus
    )
    stir_fold = (
        stir_even + inputs["stir-challenge"] * stir_odd
    ) % modulus

    whir_indices = tuple(
        (inputs["whir-index"] + offset) % modulus
        for offset in (0, inputs["offset-one"], inputs["offset-two"], inputs["offset-three"])
    )
    whir_values = tuple(oracle["whir-source"][index] for index in whir_indices)
    alpha0 = inputs["whir-alpha-zero"]
    alpha1 = inputs["whir-alpha-one"]
    low = (whir_values[0] * (1 - alpha0) + whir_values[1] * alpha0) % modulus
    high = (whir_values[2] * (1 - alpha0) + whir_values[3] * alpha0) % modulus
    whir = (low * (1 - alpha1) + high * alpha1) % modulus

    return {
        "values": {
            "circle-batch": circle,
            "deep-first-quotient": deep_first,
            "deep-second-quotient": deep_second,
            "stir-fold": stir_fold,
            "whir-grouped-fold": whir,
        },
        "queries": {
            "circle-batch": [
                ["circle-first", circle_x],
                ["circle-second", circle_x],
                ["circle-third", circle_x],
            ],
            "deep-first-quotient": [["deep-first", deep_x]],
            "deep-second-quotient": [["deep-second", deep_x]],
            "stir-fold": [list(stir_positive_query), list(stir_negative_query)],
            "whir-grouped-fold": [
                ["whir-source", index] for index in whir_indices
            ],
        },
    }


if __name__ == "__main__":
    print(json.dumps(evaluate(), indent=2, sort_keys=True))
