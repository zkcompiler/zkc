"""Independent flat-Core body for the activation-and-prior-result plan.

This module imports neither the query-plan model nor its elaborator.  It emits
plain immutable records for one target Core containing activation and a prior
logical result used only as arithmetic data.  The test adapter turns these
records into the model's carrier before independent Core admission.
"""

from __future__ import annotations

from typing import Any


def activation_and_prior_result_events() -> tuple[dict[str, Any], ...]:
    active = ("activation:plan-input:active",)
    return (
        {
            "kind": "Route",
            "path": ("first-read",),
            "guard_path": (),
            "details": (("algorithm", "always"), ("inputs", ())),
        },
        {
            "kind": "QueryOracle",
            "path": ("first-read", "only", "source-value", "query"),
            "guard_path": ("read-word:only",),
            "details": (
                ("source_oracle", "first-source"),
                ("index", "plan-input:first-index"),
            ),
        },
        {
            "kind": "AnswerOracle",
            "path": ("first-read", "only", "source-value", "answer"),
            "guard_path": ("read-word:only",),
            "details": (
                ("source_oracle", "first-source"),
                ("query_path", "first-read/only/source-value/query"),
                ("output", "first-read/only/source-value"),
            ),
        },
        {
            "kind": "ReturnDerivedValue",
            "path": ("first-read", "only", "return"),
            "guard_path": ("read-word:only",),
            "details": (("value", "first-read/only/source-value"),),
        },
        {
            "kind": "Route",
            "path": ("second-combination",),
            "guard_path": active,
            "details": (("algorithm", "always"), ("inputs", ())),
        },
        {
            "kind": "QueryOracle",
            "path": (
                "second-combination",
                "only",
                "source-value",
                "query",
            ),
            "guard_path": active + ("value-only-combination:only",),
            "details": (
                ("source_oracle", "second-source"),
                ("index", "plan-input:second-index"),
            ),
        },
        {
            "kind": "AnswerOracle",
            "path": (
                "second-combination",
                "only",
                "source-value",
                "answer",
            ),
            "guard_path": active + ("value-only-combination:only",),
            "details": (
                ("source_oracle", "second-source"),
                (
                    "query_path",
                    "second-combination/only/source-value/query",
                ),
                ("output", "second-combination/only/source-value"),
            ),
        },
        {
            "kind": "DerivedValue",
            "path": ("second-combination", "only", "combined"),
            "guard_path": active + ("value-only-combination:only",),
            "details": (
                ("algorithm", "field-add"),
                (
                    "inputs",
                    (
                        "second-combination/only/source-value",
                        "first-read/only/source-value",
                    ),
                ),
                ("output", "second-combination/only/combined"),
            ),
        },
        {
            "kind": "ReturnDerivedValue",
            "path": ("second-combination", "only", "return"),
            "guard_path": active + ("value-only-combination:only",),
            "details": (("value", "second-combination/only/combined"),),
        },
    )
