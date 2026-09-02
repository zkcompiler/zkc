#!/usr/bin/env python3
"""Check the F1-R1A target-profile basis and fixture-substitution boundary."""

from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
from types import ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
PUBLICATION_DIR = ROOT / "evaluation" / "semantic-profile-publication"
K2_MODEL = ROOT / "evaluation" / "k2-protocol-fiat-shamir" / "reference_model.py"
PUBLISHED_IDENTITIES = (
    ROOT / "docs-next" / "pir" / "profiles" / "published-identities.json"
)


class GateError(ValueError):
    """The inspected repository does not satisfy the bounded F1-R1A contract."""


@dataclass(frozen=True)
class BoundaryResult:
    name: str
    outcome: str
    code: str
    detail: str


def _load_module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise GateError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise GateError(detail)


def _body_field_ordinals(
    fragment: bytes,
    declaration: str,
) -> tuple[int, ...]:
    try:
        text = fragment.decode("utf-8")
    except UnicodeDecodeError as error:
        raise GateError("target body grammar is not UTF-8") from error
    header = f"{declaration} = R {{"
    start = text.find(header)
    if start < 0:
        raise GateError(f"target grammar omits {header!r}")
    end = text.find("\n}", start + len(header))
    if end < 0:
        raise GateError(f"target grammar does not close {declaration!r}")
    block = text[start:end]
    return tuple(int(match.group(1)) for match in re.finditer(r"(?m)^\s*(\d+):", block))


def _subject_compiler(manifest: Mapping[str, Any], subject: str) -> str:
    rows = [row for row in manifest["subjects"] if row["kind"] == subject]
    if len(rows) != 1:
        raise GateError(f"target manifest does not uniquely bind {subject}")
    compiler = rows[0]["body_compiler"]
    _require(compiler["profile"] == "self", f"{subject} compiler is not local")
    _require(
        compiler["kind"] == "pir.body-compiler",
        f"{subject} compiler has the wrong declaration kind",
    )
    return str(compiler["name"])


def _published_interaction_row() -> Mapping[str, Any]:
    try:
        value = json.loads(PUBLISHED_IDENTITIES.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateError("cannot read the frozen PIR identity table") from error
    try:
        row = value["profiles"]["interaction"]
    except (KeyError, TypeError) as error:
        raise GateError("frozen PIR identity table omits Interaction") from error
    if type(row) is not dict:
        raise GateError("frozen Interaction identity row has the wrong shape")
    return row


def evaluate() -> tuple[tuple[BoundaryResult, ...], Mapping[str, Any]]:
    publication = _load_module(
        "_zkc_f1r1a_publication",
        PUBLICATION_DIR / "reference_model.py",
    )
    independent = _load_module(
        "_zkc_f1r1a_publication_cold",
        PUBLICATION_DIR / "independent.py",
    )
    k2 = _load_module("_zkc_f1r1a_k2", K2_MODEL)

    reference_repository = publication.compile_repository()
    cold_repository = independent.compile_repository()
    reference_table = publication.identity_table(reference_repository)
    cold_table = independent.identity_table(cold_repository)
    _require(
        reference_table == cold_table,
        "independent semantic-profile compilers disagree",
    )

    target = reference_repository.profiles["interaction"]
    cold_target = cold_repository.profiles["interaction"]
    _require(
        target.body_bytes == cold_target.body_bytes,
        "independent Interaction profile bodies disagree",
    )
    _require(
        target.profile_id.internal_reference() == cold_target.identifier.ref(),
        "independent Interaction profile references disagree",
    )

    target_row = reference_table["profiles"]["interaction"]
    frozen_row = _published_interaction_row()
    _require(
        target_row == frozen_row,
        "reconstructed Interaction identity differs from the frozen v0 row",
    )
    results: list[BoundaryResult] = [
        BoundaryResult(
            "target-profile-independent-publication",
            "Affirmative",
            "F1R1A-A-PROFILE",
            "two independent compilers reproduce the complete Interaction profile",
        ),
        BoundaryResult(
            "target-profile-frozen-control",
            "Affirmative",
            "F1R1A-A-FROZEN-ID",
            "the reconstruction equals the checked-in frozen v0 identity row",
        ),
    ]

    manifest = target.manifest
    _require(
        manifest["profile_family"] == "pir.interaction" and manifest["revision"] == 0,
        "target Interaction family or revision changed",
    )
    _require(
        _subject_compiler(manifest, "pir.interactive-core")
        == "interactive-core-body-v0",
        "target Core does not select the durable Core body compiler",
    )
    _require(
        _subject_compiler(manifest, "pir.protocol") == "fresh-protocol-body-v0",
        "target Fresh Protocol does not select the durable Protocol body compiler",
    )
    definitions = {(row["kind"], row["name"]): row for row in manifest["definitions"]}
    for declaration in (
        ("pir.body-compiler", "interactive-core-body-v0"),
        ("pir.body-compiler", "fresh-protocol-body-v0"),
        ("pir.semantic-law", "core-admission-v0"),
        ("pir.semantic-law", "static-view-issuance-v0"),
        ("pir.evaluator-signature", "interaction-evaluator-v0"),
    ):
        _require(
            declaration in definitions,
            f"target Interaction manifest omits {declaration}",
        )
    results.append(
        BoundaryResult(
            "target-owner-declaration-routing",
            "Affirmative",
            "F1R1A-A-OWNER-ROUTING",
            "Core, Protocol, admission, static-view, and evaluator declarations are owner-bound",
        )
    )

    grammar = target.source_fragments["interaction-body-grammar"]
    target_core_fields = _body_field_ordinals(grammar, "InteractiveCoreBody(C)")
    target_protocol_fields = _body_field_ordinals(grammar, "ProtocolBody(P)")
    _require(
        target_core_fields == tuple(range(14)),
        "target Core source is not the fourteen-field Appendix A carrier",
    )
    _require(
        target_protocol_fields == (0, 1),
        "target Protocol source is not the two-field Appendix A carrier",
    )
    results.append(
        BoundaryResult(
            "target-canonical-source-shape",
            "Affirmative",
            "F1R1A-A-SOURCE-SHAPE",
            "published source names fourteen Core fields and two Protocol fields",
        )
    )

    view_fragment = target.source_fragments["interaction-static-views"]
    for needle in (
        b"PublicBindingView",
        b"PublicCoinView",
        b"EffectView",
        b"ClaimReductionView",
        b"PIRStaticViewIssueOutcome",
    ):
        _require(needle in view_fragment, f"target static-view source omits {needle!r}")
    results.append(
        BoundaryResult(
            "target-static-view-source-commitment",
            "Affirmative",
            "F1R1A-A-VIEW-SOURCE",
            "the target profile commits the required static-view source declarations",
        )
    )

    _require(
        target.profile_id != k2.PIR_INTERACTION_PROFILE_ID,
        "K2 fixture profile unexpectedly aliases the target Interaction profile",
    )
    results.append(
        BoundaryResult(
            "fixture-profile-substitution",
            "KindMismatch",
            "F1R1A-K-FIXTURE-PROFILE",
            "K2's witness-local Interaction profile is not the published target profile",
        )
    )

    core, _construction, _invocation, _strategy = k2.schnorr_fixture()
    fixture_core_body = k2.core_body(core)
    fixture_core_datum = k2.k1.decode_datum(fixture_core_body)
    _require(
        type(fixture_core_datum) is k2.k1.DatumRecord,
        "K2 Core body is not a canonical record",
    )
    fixture_core_fields = tuple(ordinal for ordinal, _ in fixture_core_datum.fields)
    _require(
        fixture_core_fields == tuple(range(8)),
        "K2 fixture Core no longer has its documented eight-field carrier",
    )
    _require(
        fixture_core_fields != target_core_fields,
        "K2 fixture Core unexpectedly has the target first-level shape",
    )
    results.append(
        BoundaryResult(
            "fixture-core-as-target",
            "Refused",
            "F1R1A-R-CORE-CARRIER",
            "the eight-field K2 Core is not the fourteen-field target Core carrier",
        )
    )

    fixture_core_id = k2.core_id(core)
    relabelled_core_id = k2.k1.profiled_content_id(
        "pir.interactive-core",
        target.profile_id,
        fixture_core_datum,
        semantic_regime=k2.k1.SEMANTIC_REGIME_ID,
    )
    _require(
        relabelled_core_id != fixture_core_id,
        "target-profile relabel did not rotate the fixture Core ID",
    )
    results.append(
        BoundaryResult(
            "identity-only-core-relabel",
            "Refused",
            "F1R1A-R-ID-NOT-ADMISSION",
            "Foundation forms a target-profiled ID, but the enclosed Core still fails target shape",
        )
    )

    fixture_protocol_body = k2.protocol_body(
        core,
        None,
        k2.ChallengeInterpretation.FRESH,
    )
    _require(
        type(fixture_protocol_body) is k2.k1.DatumRecord,
        "K2 Fresh Protocol body is not a canonical record",
    )
    fixture_protocol_fields = tuple(
        ordinal for ordinal, _ in fixture_protocol_body.fields
    )
    _require(
        fixture_protocol_fields == target_protocol_fields,
        "K2 Fresh Protocol no longer shares the target first-level wrapper shape",
    )
    fixture_protocol_core_ref = dict(fixture_protocol_body.fields)[0]
    _require(
        type(fixture_protocol_core_ref) is k2.k1.BytesValue
        and fixture_protocol_core_ref.value == fixture_core_id.internal_reference(),
        "K2 Fresh Protocol does not reference its exact fixture Core",
    )
    results.append(
        BoundaryResult(
            "fixture-protocol-wrapper-as-target",
            "Refused",
            "F1R1A-R-PROTOCOL-DEPENDENCY",
            "matching two-field shape retains a fixture-profiled Core dependency",
        )
    )

    interpretation = dict(fixture_protocol_body.fields)[1]
    recursively_relabelled_protocol_body = k2.k1.DatumRecord(
        (
            (
                0,
                k2.k1.BytesValue(relabelled_core_id.internal_reference()),
            ),
            (1, interpretation),
        )
    )
    relabelled_protocol_id = k2.k1.profiled_content_id(
        "pir.protocol",
        target.profile_id,
        recursively_relabelled_protocol_body,
        semantic_regime=k2.k1.SEMANTIC_REGIME_ID,
    )
    _require(
        relabelled_protocol_id.subject_kind == "pir.protocol",
        "recursive relabel did not form a Protocol-typed identity",
    )
    results.append(
        BoundaryResult(
            "recursive-identity-only-protocol-relabel",
            "Refused",
            "F1R1A-R-DEPENDENCY-NOT-ADMITTED",
            "recursive ID formation cannot turn the shape-invalid Core dependency into an admitted target Core",
        )
    )

    evidence = {
        "format": "zkc.formal-source-target-basis-f1r1a.v0",
        "target_interaction": {
            "profile_family": target_row["profile_family"],
            "revision": target_row["revision"],
            "body_length": target_row["body_length"],
            "body_sha256": target_row["body_sha256"],
            "profile_digest": target_row["profile_digest"],
            "core_field_ordinals": list(target_core_fields),
            "protocol_field_ordinals": list(target_protocol_fields),
        },
        "fixture_discriminator": {
            "profile_digest": k2.PIR_INTERACTION_PROFILE_ID.digest.hex(),
            "core_body_sha256": hashlib.sha256(fixture_core_body).hexdigest(),
            "core_field_ordinals": list(fixture_core_fields),
            "fixture_core_digest": fixture_core_id.digest.hex(),
            "identity_only_core_digest": relabelled_core_id.digest.hex(),
            "identity_only_protocol_digest": relabelled_protocol_id.digest.hex(),
        },
        "results": [asdict(result) for result in results],
    }
    return tuple(results), evidence


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--print-evidence", action="store_true")
    args = parser.parse_args(argv)
    try:
        results, evidence = evaluate()
    except GateError as error:
        print(f"F1-R1A target-basis gate failed: {error}", file=sys.stderr)
        return 1
    if args.print_evidence:
        print(json.dumps(evidence, indent=2, sort_keys=False))
    if args.check:
        for result in results:
            print(f"{result.outcome:12} {result.code} {result.name}")
    print(
        "F1-R1A target basis: "
        f"{len(results)}/{len(results)} expected boundary results; "
        "Q1 not formed"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
