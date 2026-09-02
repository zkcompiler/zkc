#!/usr/bin/env python3
"""Validate the F0-V2B2C0 canonical-byte owner-admission substrate."""

from __future__ import annotations

import argparse
import copy
from dataclasses import asdict, dataclass, replace
import hashlib
import importlib.util
import json
from pathlib import Path
import pickle
import sys
from types import MappingProxyType, ModuleType
from typing import Any, Callable


HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"
INDEPENDENT = HERE / "independent.py"
EXPECTED = HERE / "expected-findings.json"


class GateFailure(ValueError):
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


def _identified(model: ModuleType, kind: str, body: bytes) -> object:
    return model.k1.content_id(
        kind,
        body,
        semantic_regime=model.k1.SEMANTIC_REGIME_ID,
    )


def _profiled_parts(model: ModuleType, body: bytes) -> tuple[object, object]:
    value = model.k1.decode_datum(body)
    if type(value) is not model.k1.DatumRecord or tuple(
        ordinal for ordinal, _child in value.fields
    ) != (0, 1):
        raise GateFailure("fixture profiled body has another shape")
    return value.fields[0][1], value.fields[1][1]


def _expect_result(
    findings: list[Finding],
    name: str,
    result: object,
    outcome: str,
    code: str,
    detail: str,
) -> None:
    _require(
        result.outcome == outcome and result.code == code,
        f"{name}: expected {outcome}/{code}, got {result.outcome}/{result.code}",
    )
    findings.append(Finding(name, outcome, code, detail))


def _refuses(operation: Callable[[], object]) -> bool:
    try:
        operation()
    except (AttributeError, TypeError, pickle.PickleError):
        return True
    return False


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2c0_model", MODEL)
    cold = _load("_zkc_f0v2b2c0_independent", INDEPENDENT)
    environment, core_candidate, protocol_candidate = model.fixture()
    findings: list[Finding] = []

    legacy_fixture = model.base.make_fixture()
    legacy_result = model.base.admit_core(
        legacy_fixture.core_candidate, legacy_fixture.environment
    )
    _require(legacy_result.outcome == "Affirmative", "legacy positive Core drifted")
    old_identifier = legacy_result.handle.core_id
    legacy_result.handle.core_id = "ordinary-assignment-mutated-the-handle"
    legacy_mutable = legacy_result.handle.core_id != old_identifier
    legacy_result.handle.core_id = old_identifier
    _require(legacy_mutable, "the documented F1-R1B mutability gap disappeared")
    findings.append(
        Finding(
            "legacy-handle-mutability-gap",
            "Affirmative",
            "F0V2B2C0-A-LEGACY-MUTABILITY-GAP",
            "ordinary assignment mutates the retained F1-R1B admitted Core handle",
        )
    )

    core_result = model.admit_core_snapshot(core_candidate, environment)
    _expect_result(
        findings,
        "canonical-core-snapshot-admission",
        core_result,
        "Affirmative",
        "F0V2B2C0-A-CORE-SNAPSHOT",
        "strict canonical intake precedes all applicable target admission stages",
    )
    core_handle = core_result.handle
    _require(core_handle is not None, "affirmative Core admission omitted its handle")
    findings.append(
        Finding(
            "strict-core-roundtrip",
            "Affirmative",
            "F0V2B2C0-A-STRICT-ROUNDTRIP",
            "the complete profiled Core consumes all bytes and re-encodes identically",
        )
    )

    cold_core = cold.inspect_core(core_candidate.profiled_body)
    _require(
        cold_core["profile_reference"] == core_handle.profile_reference
        and cold_core["structural_summary"] == core_handle.structural_summary
        and cold_core["domain_body_sha256"]
        == hashlib.sha256(core_handle.domain_body).hexdigest(),
        "cold and reference Core decoders disagree",
    )
    findings.append(
        Finding(
            "cold-core-structural-decoder",
            "Affirmative",
            "F0V2B2C0-A-COLD-CORE-DECODE",
            "an iterative cold parser reproduces the profile, fourteen fields, and effects",
        )
    )

    immutable_operations = {
        "attribute assignment": lambda: setattr(core_handle, "core_reference", b"x"),
        "shallow copy": lambda: copy.copy(core_handle),
        "deep copy": lambda: copy.deepcopy(core_handle),
        "pickle": lambda: pickle.dumps(core_handle),
    }
    _require(
        all(_refuses(operation) for operation in immutable_operations.values()),
        "the Core snapshot is writable, copyable, or serializable",
    )
    findings.append(
        Finding(
            "immutable-noncopyable-core-authority",
            "Affirmative",
            "F0V2B2C0-A-IMMUTABLE-HANDLE",
            "ordinary assignment, copy, deepcopy, and serialization all refuse",
        )
    )

    # Supply mappings with externally retained aliases, admit, then mutate the
    # backing maps.  The handle must retain only tuple/bytes snapshots.
    profile_map = dict(environment.profile_preimages)
    module_map = dict(environment.module_preimages)
    algorithm_map = dict(environment.algorithm_preimages)
    algorithm_module_map = {
        key: MappingProxyType(dict(value))
        for key, value in environment.algorithm_modules.items()
    }
    contract_map = dict(environment.contract_preimages)
    aliased_environment = model.base.Environment(
        environment.profile_id,
        MappingProxyType(profile_map),
        MappingProxyType(module_map),
        MappingProxyType(algorithm_map),
        MappingProxyType(algorithm_module_map),
        MappingProxyType(contract_map),
        environment.prior_meta_preimages,
    )
    aliased_result = model.admit_core_snapshot(core_candidate, aliased_environment)
    _require(
        aliased_result.outcome == "Affirmative", "aliased environment did not admit"
    )
    frozen_fingerprint = aliased_result.handle.closure.fingerprint
    profile_map.clear()
    module_map.clear()
    algorithm_map.clear()
    contract_map.clear()
    _require(
        aliased_result.handle.closure.fingerprint == frozen_fingerprint
        and aliased_result.handle.profiled_body == core_candidate.profiled_body,
        "an external environment alias changed the admitted snapshot",
    )
    findings.append(
        Finding(
            "alias-free-closure-snapshot",
            "Affirmative",
            "F0V2B2C0-A-ALIAS-FREE-CLOSURE",
            "post-admission mutation of intake maps cannot change retained closure bytes",
        )
    )

    protocol_result = model.admit_fresh_protocol_snapshot(
        core_handle, protocol_candidate, environment
    )
    _expect_result(
        findings,
        "fresh-protocol-snapshot-admission",
        protocol_result,
        "Affirmative",
        "F0V2B2C0-A-FRESH-SNAPSHOT",
        "Fresh formation binds the exact Core, profile, body, closure, and evaluator",
    )
    protocol_handle = protocol_result.handle
    _require(
        protocol_handle is not None,
        "affirmative Protocol admission omitted its handle",
    )
    cold_protocol = cold.inspect_fresh_protocol(protocol_candidate.profiled_body)
    _require(
        cold_protocol["profile_reference"] == protocol_handle.profile_reference
        and cold_protocol["core_reference"] == core_handle.core_reference,
        "cold and reference Fresh Protocol decoders disagree",
    )
    findings.append(
        Finding(
            "cold-fresh-protocol-decoder",
            "Affirmative",
            "F0V2B2C0-A-COLD-PROTOCOL-DECODE",
            "the cold parser reproduces the Fresh profile and exact Core bearer",
        )
    )

    rebuilt_environment = model.reconstructed_environment(environment)
    rebuilt_protocol = model.admit_fresh_protocol_snapshot(
        core_handle, protocol_candidate, rebuilt_environment
    )
    _expect_result(
        findings,
        "content-equivalent-environment-pairing",
        rebuilt_protocol,
        "Affirmative",
        "F0V2B2C0-A-FRESH-SNAPSHOT",
        "fresh map objects with identical authenticated closure bytes preserve pairing",
    )

    _require(
        _refuses(lambda: setattr(protocol_handle, "protocol_reference", b"x"))
        and _refuses(lambda: copy.copy(protocol_handle))
        and _refuses(lambda: copy.deepcopy(protocol_handle))
        and model.serialization_refuses(protocol_handle),
        "the Fresh Protocol snapshot is writable, copyable, or serializable",
    )
    findings.append(
        Finding(
            "immutable-noncopyable-protocol-authority",
            "Affirmative",
            "F0V2B2C0-A-IMMUTABLE-PROTOCOL",
            "the paired Protocol authority refuses assignment, copying, and serialization",
        )
    )

    truncated = replace(core_candidate, profiled_body=core_candidate.profiled_body[:-1])
    _expect_result(
        findings,
        "truncated-core-body",
        model.admit_core_snapshot(truncated, environment),
        "Malformed",
        "F0V2B2C0-M-DECODE",
        "strict canonical decoding refuses a truncated body before owner admission",
    )
    trailing = replace(
        core_candidate, profiled_body=core_candidate.profiled_body + b"\x00"
    )
    _expect_result(
        findings,
        "trailing-core-body",
        model.admit_core_snapshot(trailing, environment),
        "Malformed",
        "F0V2B2C0-M-DECODE",
        "strict canonical decoding refuses trailing bytes before owner admission",
    )

    alternative_core = replace(
        legacy_fixture.core_candidate.core,
        verifier_private_inputs=(model.base.InputDecl(model.base.Z3),),
    )
    wrong_id = model.base.core_id(alternative_core, environment.profile_id)
    _expect_result(
        findings,
        "asserted-core-id-substitution",
        model.admit_core_snapshot(
            replace(core_candidate, asserted_id=wrong_id), environment
        ),
        "Malformed",
        "F0V2B2C0-M-CORE-ID",
        "an ID for another canonical Core cannot authenticate the retained bytes",
    )

    repository = model.base.publication.compile_repository()
    wrong_profile = repository.profiles["canonical-framed-fiat-shamir"].profile_id
    _expect_result(
        findings,
        "request-profile-substitution",
        model.admit_core_snapshot(
            replace(core_candidate, profile_id=wrong_profile), environment
        ),
        "KindMismatch",
        "F0V2B2C0-K-REQUEST-PROFILE",
        "the request profile cannot differ from the authenticated environment",
    )

    _profile_field, domain_field = _profiled_parts(model, core_candidate.profiled_body)
    substituted_body = model.k1.encode_datum(
        model.k1.DatumRecord(
            (
                (0, model.k1.BytesValue(wrong_profile.internal_reference())),
                (1, domain_field),
            )
        )
    )
    substituted = model.CanonicalCoreCandidate(
        _identified(model, model.base.TARGET_CORE_KIND, substituted_body),
        environment.profile_id,
        substituted_body,
    )
    _expect_result(
        findings,
        "body-profile-substitution",
        model.admit_core_snapshot(substituted, environment),
        "KindMismatch",
        "F0V2B2C0-K-BODY-PROFILE",
        "a separately identified body cannot hide another selected profile",
    )

    if type(domain_field) is not model.k1.DatumRecord:
        raise GateFailure("fixture Core domain is not a record")
    extra_domain = model.k1.DatumRecord(
        (*domain_field.fields, (14, model.k1.DatumSeq(())))
    )
    extra_body = model.k1.encode_datum(
        model.k1.DatumRecord(
            (
                (0, model.k1.BytesValue(environment.profile_id.internal_reference())),
                (1, extra_domain),
            )
        )
    )
    extra_candidate = model.CanonicalCoreCandidate(
        _identified(model, model.base.TARGET_CORE_KIND, extra_body),
        environment.profile_id,
        extra_body,
    )
    _expect_result(
        findings,
        "unknown-core-field",
        model.admit_core_snapshot(extra_candidate, environment),
        "Malformed",
        "F0V2B2C0-M-RECORD",
        "a body-authenticated fifteenth Core field still fails target formation",
    )

    legacy_protocol_attempt = model.admit_fresh_protocol_snapshot(
        legacy_result.handle, protocol_candidate, environment
    )
    _expect_result(
        findings,
        "legacy-handle-authority-substitution",
        legacy_protocol_attempt,
        "Refused",
        "F0V2B2C0-R-CORE-AUTHORITY",
        "a mutable predecessor handle cannot substitute for snapshot authority",
    )

    foreign_protocol = model.make_protocol_candidate(wrong_id, environment.profile_id)
    _expect_result(
        findings,
        "protocol-core-substitution",
        model.admit_fresh_protocol_snapshot(core_handle, foreign_protocol, environment),
        "Refused",
        "F0V2B2C0-R-PROTOCOL-CORE",
        "Fresh formation refuses a well-formed Protocol over another Core ID",
    )

    wrong_profile_protocol = replace(protocol_candidate, profile_id=wrong_profile)
    _expect_result(
        findings,
        "protocol-request-profile-substitution",
        model.admit_fresh_protocol_snapshot(
            core_handle, wrong_profile_protocol, environment
        ),
        "KindMismatch",
        "F0V2B2C0-K-PROTOCOL-PROFILE",
        "Fresh Protocol request and environment profiles must be identical",
    )

    protocol_profile, protocol_domain = _profiled_parts(
        model, protocol_candidate.profiled_body
    )
    if type(protocol_domain) is not model.k1.DatumRecord:
        raise GateFailure("fixture Protocol domain is not a record")
    fs_domain = model.k1.DatumRecord(
        (
            protocol_domain.fields[0],
            (
                1,
                model.k1.DatumVariant(
                    1, model.k1.BytesValue(core_handle.core_reference)
                ),
            ),
        )
    )
    fs_body = model.k1.encode_datum(
        model.k1.DatumRecord(((0, protocol_profile), (1, fs_domain)))
    )
    fs_candidate = model.CanonicalFreshProtocolCandidate(
        _identified(model, model.base.TARGET_PROTOCOL_KIND, fs_body),
        environment.profile_id,
        fs_body,
    )
    _expect_result(
        findings,
        "fresh-interpretation-substitution",
        model.admit_fresh_protocol_snapshot(core_handle, fs_candidate, environment),
        "Malformed",
        "F0V2B2C0-M-VARIANT",
        "Interaction-owned Fresh formation refuses an FS interpretation branch",
    )

    drifted_environment = model.base.Environment(
        environment.profile_id,
        environment.profile_preimages,
        environment.module_preimages,
        environment.algorithm_preimages,
        environment.algorithm_modules,
        MappingProxyType({}),
        environment.prior_meta_preimages,
    )
    _expect_result(
        findings,
        "protocol-closure-substitution",
        model.admit_fresh_protocol_snapshot(
            core_handle, protocol_candidate, drifted_environment
        ),
        "Refused",
        "F0V2B2C0-R-CLOSURE-PAIR",
        "equal profile and subject bytes do not hide a changed dependency closure",
    )

    findings.append(
        Finding(
            "constructor-isolation-and-owner-projection",
            "CannotAnswer",
            "F0V2B2C0-C-CONSTRUCTOR-ISOLATION",
            "B2C0 fixes intake authority; extended constructors and six-view projection remain B2C1",
        )
    )

    evidence = model.authority_summary(core_handle, protocol_handle)
    evidence.update(
        {
            "cold_core": {
                key: value
                for key, value in cold_core.items()
                if key not in {"profile_reference", "structural_summary"}
            },
            "cold_protocol": {
                key: value
                for key, value in cold_protocol.items()
                if key not in {"profile_reference", "core_reference"}
            },
            "legacy_handle_mutable": legacy_mutable,
            "new_core_copy_controls": tuple(immutable_operations),
            "finding_counts": {
                outcome: sum(item.outcome == outcome for item in findings)
                for outcome in sorted({item.outcome for item in findings})
            },
        }
    )
    return findings, evidence


def _load_expected() -> list[dict[str, str]]:
    try:
        value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read expected B2C0 findings") from error
    if type(value) is not list or any(
        type(item) is not dict or set(item) != {"name", "outcome", "code", "detail"}
        for item in value
    ):
        raise GateFailure("expected B2C0 findings have another shape")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--print-evidence", action="store_true")
    parser.add_argument("--print-findings", action="store_true")
    args = parser.parse_args()
    if not (args.check or args.print_evidence or args.print_findings):
        parser.error("select --check, --print-evidence, or --print-findings")
    try:
        findings, evidence = evaluate()
        observed = [asdict(item) for item in findings]
        if args.check:
            expected = _load_expected()
            _require(
                observed == expected,
                "observed B2C0 findings differ from the frozen table",
            )
            counts = evidence["finding_counts"]
            print(
                "[formal-source-owner-admission-f0v2b2c0] "
                f"{len(findings)}/{len(expected)} findings; "
                "CannotAnswer/F0V2B2C0-C-CONSTRUCTOR-ISOLATION; "
                f"{counts}"
            )
        if args.print_evidence:
            print(json.dumps(evidence, indent=2, sort_keys=True))
        if args.print_findings:
            print(json.dumps(observed, indent=2))
    except (GateFailure, Exception) as error:
        print(
            f"[formal-source-owner-admission-f0v2b2c0] FAIL: {error}", file=sys.stderr
        )
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
