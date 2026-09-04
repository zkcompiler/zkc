#!/usr/bin/env python3
"""Independent Appendix-A re-encoder and finite-term interpreter for F1-R1B."""

from __future__ import annotations

import importlib.util
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


HERE = Path(__file__).resolve().parent
REFERENCE = HERE / "reference_model.py"


def _load_module(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


r = _load_module("_zkc_f1r1b_reference", REFERENCE)
k1 = r.k1


def rec(fields: tuple[object, ...]) -> object:
    return k1.DatumRecord(
        tuple((ordinal, value) for ordinal, value in enumerate(fields))
    )


def seq(values: tuple[object, ...]) -> object:
    return k1.DatumSeq(values)


def var(tag: int, payload: object = k1.UNIT) -> object:
    return k1.DatumVariant(tag, payload)


def declaration(reference: object) -> object:
    if type(reference) is not r.ModuleDeclarationRef:
        raise TypeError("independent encoder received a wrong declaration reference")
    return var(
        1,
        rec(
            (
                k1.BytesValue(reference.module.internal_reference()),
                k1.Symbol(reference.declaration_kind),
                k1.Nat(reference.local_ordinal),
            )
        ),
    )


def value_ref(reference: object) -> object:
    if type(reference) is r.PublicInputRef:
        return var(0, k1.Nat(reference.ordinal))
    if type(reference) is r.VerifierPrivateInputRef:
        return var(1, k1.Nat(reference.ordinal))
    if type(reference) is r.ConstantRef:
        return var(2, k1.Nat(reference.ordinal))
    if type(reference) is r.DerivedValueRef:
        return var(3, k1.Nat(reference.ordinal))
    if type(reference) is r.OccurrenceOutputRef:
        return var(
            4, rec((k1.Nat(reference.occurrence), k1.Nat(reference.output_ordinal)))
        )
    raise TypeError("independent encoder received an unknown value reference")


def input_body(item: object) -> object:
    return rec((k1.value_type_datum(item.value_type),))


def constant_body(item: object) -> object:
    return rec((k1.value_type_datum(item.value_type), item.value.datum))


def derived_body(item: object) -> object:
    return rec(
        (
            k1.BytesValue(item.algorithm.internal_reference()),
            k1.BytesValue(item.evaluation_contract.internal_reference()),
            seq(tuple(value_ref(value) for value in item.inputs)),
            k1.value_type_datum(item.result_type),
        )
    )


def scope_body(item: object) -> object:
    parent = var(0) if item.parent is None else var(1, k1.Nat(item.parent))
    opening = var(0) if item.opening is None else var(1, k1.Nat(item.opening))
    return rec((parent, opening))


def binding_body(item: object) -> object:
    return rec(
        (k1.Nat(item.scope), var(item.binding_class.value), value_ref(item.value))
    )


def challenge_body(item: object) -> object:
    correlation = item.correlation
    if type(correlation) is r.IndependentCorrelation:
        correlation_body = var(0)
    elif type(correlation) is r.JointCorrelation:
        correlation_body = var(
            1,
            rec(
                (
                    declaration(correlation.group),
                    k1.Nat(correlation.index),
                    seq(tuple(k1.Nat(value) for value in correlation.prior_members)),
                )
            ),
        )
    else:
        raise TypeError("unknown coin correlation")
    reduction_use = item.reduction_use
    if type(reduction_use) is r.ExclusiveReductionUse:
        reduction_body = var(0)
    elif type(reduction_use) is r.SharedReductionUse:
        reduction_body = var(1, declaration(reduction_use.contract))
    else:
        raise TypeError("unknown reduction-use policy")
    return rec(
        (
            k1.Nat(item.scope),
            k1.value_type_datum(item.value_type),
            declaration(item.domain),
            declaration(item.fresh_law),
            correlation_body,
            reduction_body,
            seq(tuple(value_ref(value) for value in item.public_conditions)),
        )
    )


def check_body(item: object) -> object:
    return rec(
        (
            k1.BytesValue(item.algorithm.internal_reference()),
            k1.BytesValue(item.evaluation_contract.internal_reference()),
            seq(tuple(value_ref(value) for value in item.inputs)),
        )
    )


def claim_body(item: object) -> object:
    return rec(
        (
            declaration(item.contract),
            k1.Nat(item.scope),
            var(item.usage.value),
            var(0, k1.Nat(item.source_binding)),
        )
    )


def terminal_body(item: object) -> object:
    dispositions = tuple(
        rec((k1.Nat(entry.claim), var(entry.disposition.value)))
        for entry in item.claim_dispositions
    )
    return rec(
        (
            var(item.verdict.value),
            seq(tuple(value_ref(value) for value in item.public_outputs)),
            seq(tuple(k1.Nat(value) for value in item.required_true_checks)),
            seq(dispositions),
        )
    )


def guard_body(item: object) -> object:
    if type(item) is r.AlwaysGuard:
        return var(0)
    if type(item) is r.EvaluateGuard:
        return var(
            1,
            rec(
                (
                    k1.BytesValue(item.algorithm.internal_reference()),
                    k1.BytesValue(item.evaluation_contract.internal_reference()),
                    seq(tuple(value_ref(value) for value in item.inputs)),
                )
            ),
        )
    raise TypeError("unknown guard")


def effect_body(item: object) -> object:
    if type(item) is r.ProverMessageEffect:
        return var(
            0, rec((declaration(item.channel), k1.value_type_datum(item.payload_type)))
        )
    if type(item) is r.ChallengeEffect:
        return var(2, k1.Nat(item.challenge))
    if type(item) is r.CheckEffect:
        return var(3, k1.Nat(item.check))
    if type(item) is r.TerminalEffect:
        return var(5, k1.Nat(item.terminal))
    raise TypeError("unknown effect")


def occurrence_body(item: object) -> object:
    return rec((k1.Nat(item.scope), guard_body(item.guard), effect_body(item.effect)))


def core_domain_datum(core: object) -> object:
    if type(core) is not r.InteractiveCore:
        raise TypeError("independent encoder received a wrong Core carrier")
    fields = (
        seq(
            tuple(
                k1.BytesValue(item.internal_reference()) for item in core.used_modules
            )
        ),
        seq(tuple(input_body(item) for item in core.public_inputs)),
        seq(tuple(input_body(item) for item in core.verifier_private_inputs)),
        seq(tuple(constant_body(item) for item in core.constants)),
        seq(tuple(derived_body(item) for item in core.derived_values)),
        seq(tuple(scope_body(item) for item in core.scopes)),
        seq(tuple(binding_body(item) for item in core.public_bindings)),
        seq(tuple(challenge_body(item) for item in core.challenges)),
        seq(tuple(core.oracles)),
        seq(tuple(check_body(item) for item in core.checks)),
        seq(tuple(claim_body(item) for item in core.claims)),
        seq(tuple(core.reductions)),
        seq(tuple(terminal_body(item) for item in core.terminals)),
        seq(tuple(occurrence_body(item) for item in core.occurrences)),
    )
    return rec(fields)


def core_profiled_body(core: object, profile_id: object) -> bytes:
    domain = core_domain_datum(core)
    wrapped = rec((k1.BytesValue(profile_id.internal_reference()), domain))
    return k1.encode_datum(wrapped)


def protocol_domain_datum(core_id: object) -> object:
    return rec((k1.BytesValue(core_id.internal_reference()), var(0)))


def protocol_profiled_body(core_id: object, profile_id: object) -> bytes:
    domain = protocol_domain_datum(core_id)
    return k1.encode_datum(
        rec((k1.BytesValue(profile_id.internal_reference()), domain))
    )


def interpret_term(term: object, inputs: tuple[int | bool, ...]) -> int | bool:
    """Evaluate only the exact finite witness calculus without K1's evaluator."""

    if type(term) is k1.Literal:
        datum = term.value.datum
        if type(datum) is k1.Nat:
            return datum.value
        if type(datum) is bool:
            return datum
        raise TypeError("independent interpreter saw an unsupported literal")
    if type(term) is k1.Variable:
        return inputs[term.index]
    if type(term) is k1.Conditional:
        condition = interpret_term(term.condition, inputs)
        if type(condition) is not bool:
            raise TypeError("conditional input is not Boolean")
        branch = term.when_true if condition else term.when_false
        return interpret_term(branch, inputs)
    if type(term) is k1.PrimitiveCall:
        expected = k1.PRIMITIVE_REFS_BY_KEY[("nat.lt", 1)]
        if term.primitive != expected or len(term.arguments) != 2:
            raise TypeError("independent interpreter saw an unsupported primitive")
        left, right = tuple(interpret_term(value, inputs) for value in term.arguments)
        if type(left) is not int or type(right) is not int:
            raise TypeError("nat.lt arguments are not exact naturals")
        return left < right
    raise TypeError(f"independent interpreter saw {type(term)!r}")


def exhaustive_schnorr_truth_table(algorithm: object) -> tuple[tuple[int, ...], ...]:
    mismatches: list[tuple[int, ...]] = []
    for y in range(3):
        for commitment in range(3):
            for challenge in range(3):
                for response in range(3):
                    inputs: tuple[int | bool, ...] = (
                        y,
                        commitment,
                        challenge,
                        response,
                    )
                    observed = interpret_term(algorithm.term, inputs)
                    expected = response == (commitment + challenge * y) % 3
                    if observed is not expected:
                        mismatches.append((y, commitment, challenge, response))
    return tuple(mismatches)


def body_summary(core: object, profile_id: object, core_id: object) -> dict[str, Any]:
    core_body = core_profiled_body(core, profile_id)
    protocol_body = protocol_profiled_body(core_id, profile_id)
    return {
        "core_body_bytes": len(core_body),
        "core_top_level_fields": len(core_domain_datum(core).fields),
        "protocol_body_bytes": len(protocol_body),
        "protocol_top_level_fields": len(protocol_domain_datum(core_id).fields),
    }
