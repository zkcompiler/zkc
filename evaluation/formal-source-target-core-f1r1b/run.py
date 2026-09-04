#!/usr/bin/env python3
"""Run the bounded F1-R1B target carrier/admission gate."""

from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
import hashlib
import importlib.util
import json
from pathlib import Path
import pickle
import sys
from types import MappingProxyType, ModuleType
from typing import Callable


HERE = Path(__file__).resolve().parent
EXPECTED_IDENTITIES = HERE / "expected-identities.json"


class GateFailure(RuntimeError):
    pass


def load_module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise GateFailure(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


r = load_module("_zkc_f1r1b_reference", HERE / "reference_model.py")
independent = load_module("_zkc_f1r1b_independent", HERE / "independent.py")


@dataclass(frozen=True)
class Case:
    name: str
    expected_outcome: str
    expected_code: str
    evaluate: Callable[[], object]


@dataclass(frozen=True)
class LocalResult:
    outcome: str
    code: str
    detail: str


def local(outcome: str, code: str, detail: str) -> LocalResult:
    return LocalResult(outcome, code, detail)


def identity_table(fixture: object) -> dict[str, str]:
    core = fixture.core_candidate.core
    profile = fixture.environment.profile_id
    core_body = r.core_profiled_body(core, profile)
    protocol_body = r.protocol_profiled_body(
        fixture.core_candidate.asserted_id, profile
    )
    algorithm_body = r.k1.algorithm_preimage(fixture.schnorr_algorithm)
    return {
        "algorithm_body_sha256": "sha256:" + hashlib.sha256(algorithm_body).hexdigest(),
        "core_body_sha256": "sha256:" + hashlib.sha256(core_body).hexdigest(),
        "core_id": fixture.core_candidate.asserted_id.carrier(),
        "evaluation_contract_id": r.k1.DEFAULT_EVALUATION_CONTRACT.identity.carrier(),
        "fresh_protocol_id": fixture.protocol_candidate.asserted_id.carrier(),
        "guard_algorithm_id": fixture.guard_algorithm.identity.carrier(),
        "module_id": fixture.module.identity.carrier(),
        "profile_id": profile.carrier(),
        "protocol_body_sha256": "sha256:" + hashlib.sha256(protocol_body).hexdigest(),
        "schnorr_algorithm_id": fixture.schnorr_algorithm.identity.carrier(),
    }


def check_frozen_identities(fixture: object) -> LocalResult:
    try:
        expected = json.loads(EXPECTED_IDENTITIES.read_text(encoding="ascii"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateFailure("cannot read the frozen F1-R1B identity table") from error
    observed = identity_table(fixture)
    if observed != expected:
        raise GateFailure(
            "target witness identities drifted:\n"
            + json.dumps({"expected": expected, "observed": observed}, indent=2)
        )
    return local(
        "Affirmative",
        "F1R1B-A-FROZEN-IDENTITIES",
        "the target profile, dependencies, Core, and Fresh Protocol match the frozen table",
    )


def independent_encoding(fixture: object) -> LocalResult:
    core = fixture.core_candidate.core
    profile = fixture.environment.profile_id
    module_id = fixture.module.identity
    contract_id = r.k1.DEFAULT_EVALUATION_CONTRACT.identity
    variants = (
        core,
        replace(core, verifier_private_inputs=(r.InputDecl(r.Z3),)),
        replace(
            core,
            constants=(r.TypedConstantDecl(r.Z3, r.k1.admit_value(r.Z3, r.k1.Nat(2))),),
        ),
        replace(
            core,
            derived_values=(
                r.DerivedValueDecl(
                    fixture.guard_algorithm.identity,
                    contract_id,
                    (r.PublicInputRef(0),),
                    r.k1.BOOL,
                ),
            ),
        ),
        replace(
            core,
            scopes=(*core.scopes, r.ScopeDecl(0, 4)),
            public_bindings=(
                *core.public_bindings,
                r.PublicBindingDecl(
                    1, r.BindingClass.SESSION_CONTEXT, r.PublicInputRef(0)
                ),
            ),
        ),
        replace(
            core,
            challenges=(
                replace(
                    core.challenges[0],
                    correlation=r.JointCorrelation(
                        r.ModuleDeclarationRef(
                            module_id, "pir.coin-correlation-group", 0
                        ),
                        0,
                        (),
                    ),
                    reduction_use=r.SharedReductionUse(
                        r.ModuleDeclarationRef(
                            module_id, "pir.challenge-sharing-contract", 0
                        )
                    ),
                ),
            ),
        ),
        replace(
            core,
            claims=(
                r.ClaimDecl(
                    r.ModuleDeclarationRef(module_id, "pir.claim-contract", 0),
                    0,
                    r.ClaimUsage.LINEAR,
                    0,
                ),
            ),
            terminals=(
                replace(
                    core.terminals[0],
                    claim_dispositions=(
                        r.ClaimDispositionEntry(0, r.ClaimDisposition.CONSUME),
                    ),
                ),
                replace(
                    core.terminals[1],
                    claim_dispositions=(
                        r.ClaimDispositionEntry(0, r.ClaimDisposition.DISCHARGE),
                    ),
                ),
            ),
        ),
    )
    for ordinal, variant in enumerate(variants):
        if independent.core_profiled_body(variant, profile) != r.core_profiled_body(
            variant, profile
        ):
            raise GateFailure(
                f"independent Core body encoder disagrees on variant {ordinal}"
            )
    core_id = fixture.core_candidate.asserted_id
    if independent.protocol_profiled_body(core_id, profile) != r.protocol_profiled_body(
        core_id, profile
    ):
        raise GateFailure("independent Protocol body encoder disagrees")
    summary = independent.body_summary(core, profile, core_id)
    if (
        summary["core_top_level_fields"] != 14
        or summary["protocol_top_level_fields"] != 2
    ):
        raise GateFailure("independent encoder did not reproduce Appendix-A shape")
    return local(
        "Affirmative",
        "F1R1B-A-INDEPENDENT-ENCODING",
        "separately written encoders agree across seven Core carriers and one Protocol",
    )


def exhaustive_term_semantics(fixture: object) -> LocalResult:
    mismatches = independent.exhaustive_schnorr_truth_table(fixture.schnorr_algorithm)
    if mismatches:
        raise GateFailure(f"finite Schnorr truth table differs at {mismatches!r}")
    return local(
        "Affirmative",
        "F1R1B-A-EXHAUSTIVE-Z3",
        "an independent interpreter checked all 81 values of z = A + cY mod 3",
    )


def k1_evaluator_samples(fixture: object) -> LocalResult:
    evaluator = r.k1.Evaluator()

    def values(items: tuple[int, ...]) -> tuple[object, ...]:
        return tuple(r.k1.admit_value(r.Z3, r.k1.Nat(item)) for item in items)

    true_result = evaluator.evaluate(
        fixture.schnorr_algorithm,
        values((1, 2, 2, 1)),
        modules=r.k1.FIXTURE_MODULE_PREIMAGES,
    )
    false_result = evaluator.evaluate(
        fixture.schnorr_algorithm,
        values((1, 2, 2, 0)),
        modules=r.k1.FIXTURE_MODULE_PREIMAGES,
    )
    if (
        true_result.outcome is not r.k1.Outcome.COMPLETED
        or false_result.outcome is not r.k1.Outcome.COMPLETED
        or true_result.completion.value.datum is not True
        or false_result.completion.value.datum is not False
    ):
        raise GateFailure("K1 evaluator samples disagree with finite Schnorr semantics")
    return local(
        "Affirmative",
        "F1R1B-A-K1-EVALUATION",
        "K1 independently admitted and evaluated one true and one false equation",
    )


def admitted_fixture(fixture: object) -> tuple[object, object]:
    core = r.admit_core(fixture.core_candidate, fixture.environment)
    if core.outcome != "Affirmative":
        raise GateFailure(f"positive Core did not admit: {core}")
    protocol = r.admit_fresh_protocol(
        core.handle, fixture.protocol_candidate, fixture.environment
    )
    if protocol.outcome != "Affirmative":
        raise GateFailure(f"positive Fresh Protocol did not admit: {protocol}")
    return core, protocol


def process_local_handles(fixture: object) -> LocalResult:
    core, protocol = admitted_fixture(fixture)
    for handle in (core.handle, protocol.handle):
        try:
            pickle.dumps(handle)
        except TypeError:
            continue
        raise GateFailure("an admitted owner handle unexpectedly serialized")
    reconstructed_environment = replace(fixture.environment)
    reconstructed = r.admit_fresh_protocol(
        core.handle, fixture.protocol_candidate, reconstructed_environment
    )
    if (
        reconstructed.outcome,
        reconstructed.code,
    ) != ("Refused", "F1R1B-R-EVALUATOR-AUTHORITY"):
        raise GateFailure("a reconstructed admission environment gained authority")
    return local(
        "Affirmative",
        "F1R1B-A-LOCAL-AUTHORITY",
        "admission mints nonserializable process-local Core and Protocol handles",
    )


def candidate(
    core: object, environment: object, asserted_id: object | None = None
) -> object:
    formed = r.make_core_candidate(core, environment.profile_id)
    return formed if asserted_id is None else replace(formed, asserted_id=asserted_id)


def exact_environment(base: object, core: object) -> object:
    return r.environment_for_core(base, core)


def build_cases(fixture: object) -> tuple[Case, ...]:
    base_core = fixture.core_candidate.core
    base_env = fixture.environment
    module_id = fixture.module.identity
    contract_id = r.k1.DEFAULT_EVALUATION_CONTRACT.identity

    retained_body = replace(base_core, verifier_private_inputs=(r.InputDecl(r.Z3),))

    missing_used = replace(base_core, used_modules=())
    missing_used_env = replace(base_env, module_preimages=MappingProxyType({}))

    extra_module = r.k1.SemanticModuleCandidate(
        r.k1.Symbol("f1r1b.unused-module"), (), r.k1.DatumSeq(())
    )
    extra_modules = tuple(
        sorted(
            (module_id, extra_module.identity),
            key=lambda item: item.internal_reference(),
        )
    )
    extra_used = replace(base_core, used_modules=extra_modules)
    extra_env = replace(
        base_env,
        module_preimages=MappingProxyType(
            {module_id: fixture.module, extra_module.identity: extra_module}
        ),
    )

    missing_preimage_env = replace(base_env, module_preimages=MappingProxyType({}))

    wrong_domain = replace(
        base_core.challenges[0],
        domain=r.ModuleDeclarationRef(module_id, "pir.message-channel", 0),
    )
    wrong_declaration = replace(base_core, challenges=(wrong_domain,))

    wrong_check = replace(
        base_core.checks[0], algorithm=fixture.guard_algorithm.identity
    )
    wrong_abi = replace(base_core, checks=(wrong_check,))
    wrong_abi_env = exact_environment(base_env, wrong_abi)

    bad_scope = replace(base_core, scopes=(*base_core.scopes, r.ScopeDecl(0, 99)))

    duplicate_challenge_occurrences = list(base_core.occurrences)
    duplicate_challenge_occurrences[2] = replace(
        duplicate_challenge_occurrences[2], effect=r.ChallengeEffect(0)
    )
    duplicate_challenge = replace(
        base_core, occurrences=tuple(duplicate_challenge_occurrences)
    )

    duplicate_check_occurrences = (
        *base_core.occurrences[:4],
        r.OccurrenceDecl(0, r.AlwaysGuard(), r.CheckEffect(0)),
        *base_core.occurrences[4:],
    )
    duplicate_check = replace(base_core, occurrences=duplicate_check_occurrences)

    duplicate_terminal_occurrences = list(base_core.occurrences)
    duplicate_terminal_occurrences[-1] = replace(
        duplicate_terminal_occurrences[-1], effect=r.TerminalEffect(0)
    )
    duplicate_terminal = replace(
        base_core, occurrences=tuple(duplicate_terminal_occurrences)
    )

    future_check = replace(
        base_core.checks[0],
        inputs=(
            r.PublicInputRef(0),
            r.OccurrenceOutputRef(0, 0),
            r.OccurrenceOutputRef(1, 0),
            r.OccurrenceOutputRef(4, 0),
        ),
    )
    future_occurrences = (
        *base_core.occurrences[:4],
        r.OccurrenceDecl(
            0,
            r.AlwaysGuard(),
            r.ProverMessageEffect(
                r.ModuleDeclarationRef(module_id, "pir.message-channel", 1), r.Z3
            ),
        ),
        *base_core.occurrences[4:],
    )
    future_read = replace(
        base_core, checks=(future_check,), occurrences=future_occurrences
    )

    private_challenge = replace(
        base_core.challenges[0],
        public_conditions=(r.VerifierPrivateInputRef(0),),
    )
    private_influence = replace(
        base_core,
        verifier_private_inputs=(r.InputDecl(r.Z3),),
        challenges=(private_challenge,),
    )

    shared_challenge = replace(
        base_core.challenges[0],
        reduction_use=r.SharedReductionUse(
            r.ModuleDeclarationRef(module_id, "pir.challenge-sharing-contract", 0)
        ),
    )
    unsatisfied_shared = replace(base_core, challenges=(shared_challenge,))

    dead_claim = r.ClaimDecl(
        r.ModuleDeclarationRef(module_id, "pir.claim-contract", 0),
        0,
        r.ClaimUsage.LINEAR,
        0,
    )
    unresolved_claim = replace(base_core, claims=(dead_claim,))

    guarded_fallback_occurrences = list(base_core.occurrences)
    guarded_fallback_occurrences[-1] = replace(
        guarded_fallback_occurrences[-1],
        guard=r.EvaluateGuard(
            fixture.guard_algorithm.identity,
            contract_id,
            (r.OccurrenceOutputRef(3, 0),),
        ),
    )
    guarded_fallback = replace(
        base_core, occurrences=tuple(guarded_fallback_occurrences)
    )

    unsupported_derived = r.DerivedValueDecl(
        fixture.guard_algorithm.identity,
        contract_id,
        (r.PublicInputRef(0),),
        r.k1.BOOL,
    )
    unsupported_family = replace(base_core, derived_values=(unsupported_derived,))

    wrong_profile_id = replace(base_env.profile_id, digest=b"\x00" * 32)
    wrong_profile_env = replace(base_env, profile_id=wrong_profile_id)

    positive_core, _positive_protocol = admitted_fixture(fixture)
    mismatched_core_id = r.core_id(guarded_fallback, base_env.profile_id)
    mismatched_protocol = r.make_protocol_candidate(
        mismatched_core_id, base_env.profile_id
    )
    bad_protocol_id = replace(
        fixture.protocol_candidate.asserted_id, digest=b"\x01" * 32
    )
    retained_protocol = replace(fixture.protocol_candidate, asserted_id=bad_protocol_id)

    return (
        Case(
            "target-core-admission",
            "Affirmative",
            "F1R1B-A-CORE-ADMITTED",
            lambda: r.admit_core(fixture.core_candidate, base_env),
        ),
        Case(
            "target-fresh-admission",
            "Affirmative",
            "F1R1B-A-FRESH-ADMITTED",
            lambda: r.admit_fresh_protocol(
                positive_core.handle, fixture.protocol_candidate, base_env
            ),
        ),
        Case(
            "frozen-identities",
            "Affirmative",
            "F1R1B-A-FROZEN-IDENTITIES",
            lambda: check_frozen_identities(fixture),
        ),
        Case(
            "independent-body-encoding",
            "Affirmative",
            "F1R1B-A-INDEPENDENT-ENCODING",
            lambda: independent_encoding(fixture),
        ),
        Case(
            "exhaustive-finite-equation",
            "Affirmative",
            "F1R1B-A-EXHAUSTIVE-Z3",
            lambda: exhaustive_term_semantics(fixture),
        ),
        Case(
            "k1-evaluator-samples",
            "Affirmative",
            "F1R1B-A-K1-EVALUATION",
            lambda: k1_evaluator_samples(fixture),
        ),
        Case(
            "process-local-admission-authority",
            "Affirmative",
            "F1R1B-A-LOCAL-AUTHORITY",
            lambda: process_local_handles(fixture),
        ),
        Case(
            "retained-core-id",
            "Refused",
            "F1R1B-R-CORE-ID",
            lambda: r.admit_core(
                candidate(retained_body, base_env, fixture.core_candidate.asserted_id),
                base_env,
            ),
        ),
        Case(
            "missing-used-module",
            "Refused",
            "F1R1B-R-EXACT-USED-MODULES",
            lambda: r.admit_core(
                candidate(missing_used, missing_used_env), missing_used_env
            ),
        ),
        Case(
            "extra-used-module",
            "Refused",
            "F1R1B-R-EXACT-USED-MODULES",
            lambda: r.admit_core(candidate(extra_used, extra_env), extra_env),
        ),
        Case(
            "missing-module-preimage",
            "MissingDependency",
            "F1R1B-D-MODULE-PREIMAGE",
            lambda: r.admit_core(
                candidate(base_core, missing_preimage_env), missing_preimage_env
            ),
        ),
        Case(
            "wrong-declaration-kind",
            "KindMismatch",
            "F1R1B-K-DECLARATION",
            lambda: r.admit_core(candidate(wrong_declaration, base_env), base_env),
        ),
        Case(
            "check-algorithm-abi",
            "KindMismatch",
            "F1R1B-K-ALGORITHM-ABI",
            lambda: r.admit_core(candidate(wrong_abi, wrong_abi_env), wrong_abi_env),
        ),
        Case(
            "bad-scope-opening",
            "Refused",
            "F1R1B-R-SCOPE-OPENING",
            lambda: r.admit_core(candidate(bad_scope, base_env), base_env),
        ),
        Case(
            "duplicate-challenge-backlink",
            "Refused",
            "F1R1B-R-BACKLINK",
            lambda: r.admit_core(candidate(duplicate_challenge, base_env), base_env),
        ),
        Case(
            "duplicate-check-backlink",
            "Refused",
            "F1R1B-R-BACKLINK",
            lambda: r.admit_core(candidate(duplicate_check, base_env), base_env),
        ),
        Case(
            "duplicate-terminal-backlink",
            "Refused",
            "F1R1B-R-BACKLINK",
            lambda: r.admit_core(candidate(duplicate_terminal, base_env), base_env),
        ),
        Case(
            "future-occurrence-read",
            "Refused",
            "F1R1B-R-VALUE-AVAILABILITY",
            lambda: r.admit_core(candidate(future_read, base_env), base_env),
        ),
        Case(
            "private-challenge-condition",
            "Refused",
            "F1R1B-R-CHALLENGE-CONDITION-PUBLIC",
            lambda: r.admit_core(candidate(private_influence, base_env), base_env),
        ),
        Case(
            "shared-without-consumers",
            "Refused",
            "F1R1B-R-SHARED-CONSUMERS",
            lambda: r.admit_core(candidate(unsatisfied_shared, base_env), base_env),
        ),
        Case(
            "unresolved-initial-claim",
            "Refused",
            "F1R1B-R-TERMINAL-CLAIM-CLOSURE",
            lambda: r.admit_core(candidate(unresolved_claim, base_env), base_env),
        ),
        Case(
            "missing-unconditional-fallback",
            "Refused",
            "F1R1B-R-FINAL-FALLBACK",
            lambda: r.admit_core(candidate(guarded_fallback, base_env), base_env),
        ),
        Case(
            "wrong-interaction-profile",
            "KindMismatch",
            "F1R1B-K-TARGET-PROFILE",
            lambda: r.admit_core(
                r.CoreCandidate(fixture.core_candidate.asserted_id, base_core),
                wrong_profile_env,
            ),
        ),
        Case(
            "protocol-core-substitution",
            "Refused",
            "F1R1B-R-PROTOCOL-CORE",
            lambda: r.admit_fresh_protocol(
                positive_core.handle, mismatched_protocol, base_env
            ),
        ),
        Case(
            "protocol-without-live-core",
            "Refused",
            "F1R1B-R-CORE-AUTHORITY",
            lambda: r.admit_fresh_protocol(
                fixture.core_candidate, fixture.protocol_candidate, base_env
            ),
        ),
        Case(
            "retained-protocol-id",
            "Refused",
            "F1R1B-R-PROTOCOL-ID",
            lambda: r.admit_fresh_protocol(
                positive_core.handle, retained_protocol, base_env
            ),
        ),
        Case(
            "unsupported-derived-family",
            "Unsupported",
            "F1R1B-U-OUTSIDE-SLICE",
            lambda: r.admit_core(candidate(unsupported_family, base_env), base_env),
        ),
    )


def run_gate() -> dict[str, object]:
    fixture = r.make_fixture()
    rows: list[dict[str, str]] = []
    seen: set[str] = set()
    cases = build_cases(fixture)
    for case in cases:
        if case.name in seen:
            raise GateFailure(f"duplicate case name {case.name!r}")
        seen.add(case.name)
        observed = case.evaluate()
        outcome = getattr(observed, "outcome", None)
        code = getattr(observed, "code", None)
        if (outcome, code) != (case.expected_outcome, case.expected_code):
            detail = getattr(observed, "detail", "")
            raise GateFailure(
                f"{case.name}: expected {case.expected_outcome}/{case.expected_code}, "
                f"observed {outcome}/{code}: {detail}"
            )
        rows.append({"name": case.name, "outcome": outcome, "code": code})

    body = r.core_profiled_body(
        fixture.core_candidate.core, fixture.environment.profile_id
    )
    return {
        "cases": rows,
        "passed": len(rows),
        "total": len(cases),
        "identities": identity_table(fixture),
        "measurements": {
            "algorithm_preimage_bytes": len(
                r.k1.algorithm_preimage(fixture.schnorr_algorithm)
            ),
            "core_profiled_body_bytes": len(body),
            "core_top_level_fields": len(
                r.core_domain_datum(fixture.core_candidate.core).fields
            ),
            "finite_equation_rows": 81,
            "protocol_top_level_fields": len(
                r.protocol_domain_datum(fixture.core_candidate.asserted_id).fields
            ),
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    arguments = parser.parse_args()
    try:
        report = run_gate()
    except GateFailure as error:
        print(f"F1-R1B gate failed: {error}", file=sys.stderr)
        return 1
    if arguments.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            f"F1-R1B target carrier/admission: {report['passed']}/{report['total']} passed"
        )
        for row in report["cases"]:
            print(f"  {row['name']}: {row['outcome']}/{row['code']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
