#!/usr/bin/env python3
"""Validate the F0-V2B2C1A exact owner-view value codec."""

from __future__ import annotations

import argparse
import copy
from dataclasses import asdict, dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Callable


HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"
INDEPENDENT = HERE / "independent.py"
EXPECTED = HERE / "expected-findings.json"
AGGREGATE = "F0V2B2C1A-A-EXACT-VIEW-VALUE-CODEC"


class GateFailure(RuntimeError):
    """The executable package no longer satisfies its frozen contract."""


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str
    detail: str


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GateFailure(detail)


def _finding(name: str, outcome: str, code: str, detail: str) -> Finding:
    return Finding(name, outcome, code, detail)


def _rejects(
    operation: Callable[[], object],
    expected: type[BaseException],
) -> bool:
    try:
        operation()
    except expected:
        return True
    return False


def _both_reject(
    model: ModuleType,
    cold: ModuleType,
    schema: dict[str, Any],
    value: object,
    label: str,
) -> None:
    _require(
        _rejects(lambda: model.encode_value(schema, value), model.CodecError),
        f"reference codec accepted {label}",
    )
    _require(
        _rejects(lambda: cold.encode_value(schema, value), cold.ColdCodecError),
        f"cold codec accepted {label}",
    )


def _law_source_check(model: ModuleType, samples: dict[str, Any]) -> None:
    fixture = model.owner.make_fixture()
    context = model.k1.effective_semantic_context(
        fixture.environment.profile_id,
        dict(fixture.environment.profile_preimages),
        semantic_regime=model.k1.SEMANTIC_REGIME_ID,
    )
    for name, ordinal in model.LAW_ORDINALS.items():
        body = model.k1.resolve_profile_declaration(
            context,
            model.k1.ProfileLocalDeclarationRef("pir.semantic-law", ordinal),
        )
        _require(
            type(body) is model.k1.DatumRecord
            and tuple(item[0] for item in body.fields) == (0, 1, 2, 3, 4)
            and type(body.fields[0][1]) is model.k1.Symbol
            and body.fields[0][1].value == name,
            f"law ordinal {ordinal} no longer resolves to {name}",
        )
    _require(samples["compiler_count"] == 22, "atom compiler sample count drifted")


def _module_source_check(model: ModuleType, samples: dict[str, Any]) -> None:
    module = samples["codec_module"]
    resolved = model.k1.resolve_module_declaration(module, "pir.core-effect", 0)
    _require(
        type(resolved) is model.k1.DatumRecord
        and type(resolved.fields[0][1]) is model.k1.Symbol
        and resolved.fields[0][1].value == "codec-only-effect",
        "codec-only module effect declaration no longer resolves exactly",
    )


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2c1a_model", MODEL)
    cold = _load("_zkc_f0v2b2c1a_independent", INDEPENDENT)
    schemas, owners, stats = model.b2b.compile_current()
    cold_schemas, cold_owners, cold_stats = cold.b2b.compile_current()
    _require(schemas == cold_schemas, "B2B schema compilers disagree")
    _require(owners == cold_owners, "B2B owner catalogs disagree")
    _require(
        stats["definition_count"] == cold_stats["definition_count"]
        and stats["source_node_count"] == cold_stats["source_node_count"],
        "B2B source census disagrees",
    )

    source = model.b2b.load_source()
    samples = model.sample_catalog()
    _require(
        set(samples["canonical"]) == set(source["body_compilers"]),
        "the exact atom compiler registry is incomplete or contains extras",
    )
    _law_source_check(model, samples)
    _module_source_check(model, samples)

    findings = [
        _finding(
            "constructor-schema-source-agreement",
            "Affirmative",
            "F0V2B2C1A-A-SCHEMA-SOURCE",
            "recursive and topological B2B compilers supply identical six-view schemas",
        ),
        _finding(
            "exact-atom-compiler-registry",
            "Affirmative",
            "F0V2B2C1A-A-ATOM-REGISTRY",
            "all 22 candidate leaf compilers have one exact decodable sample body",
        ),
        _finding(
            "exact-profile-law-bodies",
            "Affirmative",
            "F0V2B2C1A-A-LAW-BODIES",
            "all three used laws resolve to exact profile-local declaration bodies",
        ),
        _finding(
            "module-effect-atom-framing",
            "Affirmative",
            "F0V2B2C1A-A-MODULE-FRAMING",
            "one authenticated module/declaration pair frames a payload as one opaque atom",
        ),
    ]

    encoded_count = 0
    roundtrip_count = 0
    per_view: dict[str, dict[str, Any]] = {}
    first_values: dict[str, object] = {}
    for view in source["view_order"]:
        schema = schemas[view]
        raw_values = model.b2b.inhabitants(schema)
        digests: list[str] = []
        for index, raw_value in enumerate(raw_values):
            value = model.materialize(schema, raw_value, samples)
            if index == 0:
                first_values[view] = value
            model.b2b.validate(schema, value)
            cold.b2b.validate(schema, value)
            reference_body = model.encode_value(schema, value)
            cold_body = cold.encode_value(schema, value)
            _require(reference_body == cold_body, f"{view} codec paths disagree")
            decoded = model.k1.decode_datum(reference_body)
            _require(
                model.k1.encode_datum(decoded) == reference_body,
                f"{view} exact value did not round-trip",
            )
            encoded_count += 1
            roundtrip_count += 1
            digests.append(hashlib.sha256(reference_body).hexdigest())
        per_view[view] = {
            "values": len(raw_values),
            "first_body_sha256": digests[0],
            "distinct_body_count": len(set(digests)),
        }
    _require(encoded_count == 302, "B2B inhabitant total drifted")
    findings.extend(
        (
            _finding(
                "dual-exact-value-codecs",
                "Affirmative",
                "F0V2B2C1A-A-DUAL-CODEC",
                "recursive and iterative codecs agree on all 302 materialized inhabitants",
            ),
            _finding(
                "six-view-root-coverage",
                "Affirmative",
                "F0V2B2C1A-A-SIX-ROOTS",
                "every constructor-complete view root has exact encoded witnesses",
            ),
            _finding(
                "exact-value-roundtrip",
                "Affirmative",
                "F0V2B2C1A-A-ROUNDTRIP",
                "all 302 exact view bodies decode fully and re-encode byte-identically",
            ),
        )
    )

    order = model.exact_pcnode_order_probe(schemas, samples)
    target_reference = model.encode_value(order["sequence_schema"], order["target"])
    target_cold = cold.encode_value(order["sequence_schema"], order["target"])
    _require(
        target_reference == target_cold, "target PCNode sequence encodings disagree"
    )
    _require(
        order["target_cases"] == [2, 10] and order["diagnostic_cases"] == [10, 2],
        "the target-versus-diagnostic order discriminator drifted",
    )
    _require(
        _rejects(
            lambda: model.b2b.validate(order["sequence_schema"], order["target"]),
            model.b2b.SchemaError,
        )
        and _rejects(
            lambda: cold.b2b.validate(order["sequence_schema"], order["target"]),
            cold.b2b.IndependentError,
        ),
        "a diagnostic validator unexpectedly accepted target order",
    )
    model.b2b.validate(order["sequence_schema"], order["diagnostic"])
    cold.b2b.validate(order["sequence_schema"], order["diagnostic"])
    findings.extend(
        (
            _finding(
                "target-body-sorted-unique-order",
                "Affirmative",
                "F0V2B2C1A-A-TARGET-ORDER",
                "both exact codecs accept PCNode cases 2 then 10 under K1 body order",
            ),
            _finding(
                "diagnostic-order-inapplicability",
                "Affirmative",
                "F0V2B2C1A-A-DIAGNOSTIC-INVERSION",
                "JSON orders the same PCNodes 10 then 2 and cannot validate target sets",
            ),
        )
    )

    core_schema = model.record_field(schemas["PublicBindingView"], 0)
    fixture = model.owner.make_fixture()
    legacy_raw_reference = {
        "compiler": "core-id-body-v0",
        "body": fixture.core_candidate.asserted_id.internal_reference().hex(),
    }
    _both_reject(
        model,
        cold,
        core_schema,
        legacy_raw_reference,
        "the B1 raw internal-reference atom",
    )
    corrected_reference = samples["canonical"]["core-id-body-v0"]
    _require(
        model.encode_value(core_schema, corrected_reference)
        == cold.encode_value(core_schema, corrected_reference),
        "correctly wrapped CoreId atom disagrees",
    )
    findings.append(
        _finding(
            "content-reference-atom-wrapper",
            "Affirmative",
            "F0V2B2C1A-A-CONTENT-REF-WRAPPER",
            "raw ContentRefV0 bytes refuse; exact MetaBytes wrapping forms the atom body",
        )
    )

    module_schema = {"node": "atom", "atom": {"kind": "admitted-module-effect"}}
    _require(
        model.encode_value(module_schema, samples["module_effect"])
        == cold.encode_value(module_schema, samples["module_effect"]),
        "module-effect atom codecs disagree",
    )

    wrong_compiler = copy.deepcopy(corrected_reference)
    wrong_compiler["compiler"] = "protocol-id-body-v0"
    _both_reject(model, cold, core_schema, wrong_compiler, "compiler substitution")
    findings.append(
        _finding(
            "compiler-substitution",
            "Refused",
            "F0V2B2C1A-R-COMPILER-SUBSTITUTION",
            "a well-formed body under another leaf compiler cannot substitute",
        )
    )

    malformed_hex = copy.deepcopy(corrected_reference)
    malformed_hex["body"] = "0z"
    _both_reject(model, cold, core_schema, malformed_hex, "malformed hexadecimal")
    findings.append(
        _finding(
            "malformed-atom-hex",
            "Malformed",
            "F0V2B2C1A-M-ATOM-HEX",
            "a non-hexadecimal canonical-body payload refuses",
        )
    )

    trailing_atom = copy.deepcopy(corrected_reference)
    trailing_atom["body"] += "00"
    _both_reject(model, cold, core_schema, trailing_atom, "trailing atom bytes")
    findings.append(
        _finding(
            "trailing-atom-body",
            "Malformed",
            "F0V2B2C1A-M-ATOM-TRAILING",
            "a canonical atom body must consume all bytes",
        )
    )

    binding_schema = schemas["PublicBindingView"]
    missing_field = copy.deepcopy(first_values["PublicBindingView"])
    del missing_field[2]
    _both_reject(model, cold, binding_schema, missing_field, "missing root field")
    findings.append(
        _finding(
            "missing-record-field",
            "Malformed",
            "F0V2B2C1A-M-RECORD-FIELD",
            "the exact root record refuses an omitted field",
        )
    )

    unknown_variant = {"case": 99, "value": None}
    _both_reject(
        model, cold, order["node_schema"], unknown_variant, "unknown PCNode case"
    )
    findings.append(
        _finding(
            "unknown-variant-case",
            "Malformed",
            "F0V2B2C1A-M-VARIANT-CASE",
            "an absent PCNode constructor cannot encode",
        )
    )

    duplicate = [copy.deepcopy(order["target"][0]), copy.deepcopy(order["target"][0])]
    _both_reject(
        model, cold, order["sequence_schema"], duplicate, "duplicate PCNode set"
    )
    findings.append(
        _finding(
            "duplicate-sorted-unique-element",
            "Malformed",
            "F0V2B2C1A-M-DUPLICATE",
            "equal exact element bodies cannot occur twice in a sorted-unique sequence",
        )
    )

    _both_reject(
        model,
        cold,
        order["sequence_schema"],
        order["diagnostic"],
        "diagnostic order as target order",
    )
    findings.append(
        _finding(
            "diagnostic-order-substitution",
            "Malformed",
            "F0V2B2C1A-M-TARGET-ORDER",
            "JSON-sorted PCNodes refuse under exact target-body ordering",
        )
    )

    law_schema = model.record_field(schemas["StrategyDecisionView"], 2)
    law_value = copy.deepcopy(first_values["StrategyDecisionView"][2])
    law_value["name"] = "execution-and-replay-v0"
    _both_reject(model, cold, law_schema, law_value, "law substitution")
    findings.append(
        _finding(
            "law-substitution",
            "Refused",
            "F0V2B2C1A-R-LAW-SUBSTITUTION",
            "another existing semantic-law declaration cannot satisfy a fixed law atom",
        )
    )

    profile_value = copy.deepcopy(first_values["StrategyDecisionView"][2])
    profile_value["profile"] = "00" * 32
    _both_reject(model, cold, law_schema, profile_value, "profile substitution")
    findings.append(
        _finding(
            "law-profile-substitution",
            "KindMismatch",
            "F0V2B2C1A-K-LAW-PROFILE",
            "a law diagnostic from another profile cannot select the local law body",
        )
    )

    trailing_module = copy.deepcopy(samples["module_effect"])
    trailing_module["payload_body"] += "00"
    _both_reject(model, cold, module_schema, trailing_module, "trailing module payload")
    findings.append(
        _finding(
            "module-payload-trailing-bytes",
            "Malformed",
            "F0V2B2C1A-M-MODULE-PAYLOAD",
            "an opaque module payload is still one exact fully consumed datum",
        )
    )

    findings.extend(
        (
            _finding(
                "isolated-owner-projections",
                "CannotAnswer",
                "F0V2B2C1A-C-OWNER-PROJECTIONS",
                "the 21 B2C pressure families still require admitted carriers and dual projection",
            ),
            _finding(
                "target-publication-and-migration",
                "CannotAnswer",
                "F0V2B2C1A-C-TARGET-PUBLICATION",
                "the codec registry and schemas remain research inputs until F0-V2C",
            ),
        )
    )
    _require(len(findings) == 22, "finding census drifted")
    evidence = {
        "aggregate": AGGREGATE,
        "schema_source_sha256": hashlib.sha256(
            model.b2b.SOURCE.read_bytes()
        ).hexdigest(),
        "schema_definition_count": stats["definition_count"],
        "schema_source_nodes": stats["source_node_count"],
        "body_compiler_count": samples["compiler_count"],
        "law_ordinals": model.LAW_ORDINALS,
        "encoded_inhabitants": encoded_count,
        "roundtrip_inhabitants": roundtrip_count,
        "per_view": per_view,
        "pcnode_target_order": order["target_cases"],
        "pcnode_diagnostic_order": order["diagnostic_cases"],
        "target_order_body_sha256": hashlib.sha256(target_reference).hexdigest(),
        "finding_counts": {
            outcome: sum(item.outcome == outcome for item in findings)
            for outcome in sorted({item.outcome for item in findings})
        },
    }
    return findings, evidence


def _load_expected() -> list[dict[str, str]]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read expected B2C1A findings") from error
    if type(value) is not list or any(
        type(item) is not dict or set(item) != {"name", "outcome", "code", "detail"}
        for item in value
    ):
        raise GateFailure("expected B2C1A findings have another shape")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--print-findings", action="store_true")
    parser.add_argument("--print-evidence", action="store_true")
    args = parser.parse_args()
    if not (args.check or args.print_findings or args.print_evidence):
        parser.error("select --check, --print-findings, or --print-evidence")
    try:
        findings, evidence = evaluate()
        observed = [asdict(item) for item in findings]
        if args.check:
            _require(observed == _load_expected(), "frozen B2C1A findings drifted")
        if args.print_findings:
            print(json.dumps(observed, indent=2, sort_keys=True))
        if args.print_evidence:
            print(json.dumps(evidence, indent=2, sort_keys=True))
        counts = evidence["finding_counts"]
        print(
            "[formal-source-view-codec-f0v2b2c1a] "
            f"{len(findings)}/{len(findings)} findings; Affirmative/{AGGREGATE}; "
            f"{evidence['encoded_inhabitants']} exact values; {counts}"
        )
        return 0
    except Exception as error:
        print(f"[formal-source-view-codec-f0v2b2c1a] FAIL: {error}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
