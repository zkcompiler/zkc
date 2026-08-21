"""RULE_WF, binding well-formedness, and the freeze that requires both.

`RULE_WF` proves syntax and typing and nothing else: it does not prove that a
cited theorem is true, that a rule encodes it faithfully, or that a binding is
faithful to the protocol occurrence it names.  Those are meta-level antecedents
the kernel consumes rather than establishes (docs/spec/soundness.md section 8).

What is decided here is where a typing defect would otherwise sit unnoticed and
let a wrong application succeed: whether a body's premise carries the exact
index its equation needs, whether a quantity reads a name that is in scope,
whether an exponent is structurally integral, whether a binding covers every
slot its rule declares, and whether a declared parameter is read by anything at
all.  Every one of those is mechanical, which is why this is the half the
reference mirrors.

The carrier's value types are flat records whose inactive fields must be shown
to be at their defaults; the variants here cannot carry a field their case does
not have, so those checks hold by construction rather than by inspection.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Any

from .model import Refusal
from .signature import (
    Binding,
    Bound,
    BoundOperation,
    ContractRoundFact,
    NamedQuantity,
    PremiseCoordinate,
    PremisePort,
    PrimitiveAdvantage,
    Quantity,
    QuantityBound,
    QuantityOperation,
    QUANTITY_OPERATIONS,
    RationalLiteral,
    RESULT_OF_NOTION,
    Rule,
    ScalarBound,
    ScaledBound,
    SchemaContext,
    SecurityIndex,
    Sequence,
    Signature,
    read_signature,
)

NUMERIC_SORTS = frozenset({"integer", "rational"})

# The exponent range the exact evaluator is defined over.  Outside it a power
# is refused rather than approximated.
EXPONENT_LIMIT = 4096

# The shape law each notion's index obeys, independent of the admitted table:
# which of `variant` and `model` must be empty and which must be filled.
INDEX_SHAPE = {
    "special_soundness": (False, False),
    "computational_special_soundness": (False, False),
    "round_by_round": (True, False),
    "state_restoration": (True, False),
    "fiat_shamir": (True, True),
    "completeness": (False, False),
}

# What each body demands of its one premise, given the conclusion index.  A
# `None` premise notion means the body takes none.  `carries_variant` says
# whether the premise repeats the conclusion's variant or erases it, which is
# the difference between staying inside a notion and crossing into one whose
# variant does not apply.
BODY_LAW = {
    "special_soundness_entry": (None, None, False),
    "native_round_by_round_entry": (None, None, False),
    "computational_entry": (None, None, False),
    "completeness_entry": (None, None, False),
    "special_soundness_preservation": ("source_port", "special_soundness", False),
    "round_by_round_preservation": ("source_port", "round_by_round", True),
    "round_scaling": ("round_by_round_port", "round_by_round", True),
    "special_soundness_to_round_by_round": (
        "special_soundness_port", "special_soundness", False),
    "round_by_round_to_state_restoration": (
        "round_by_round_port", "round_by_round", True),
    "state_restoration_to_fiat_shamir_duplex": (
        "state_restoration_port", "state_restoration", True),
}

# The canonical identity of every machine decider.  A decider is a name for
# code in the binary, so a signature that renames one, or restates its
# signature differently, is naming something that does not exist.
MACHINE_DECIDERS = {
    "one_message_role": ("zkc.side.one_message_role", ("reduction_contract",)),
    "space_embeds": ("zkc.side.space_embeds",
                     ("reduction_contract", "integer")),
    "bound_bites": ("zkc.side.bound_bites", ("reduction_contract",)),
    "field_class": ("zkc.side.field_class", ("reduction_contract", "string")),
    "space_covers_arity": ("zkc.side.space_covers_arity",
                           ("reduction_contract", "integer")),
    "batch_arity": ("zkc.side.batch_arity", ("integer",)),
    "space_covers_batch": ("zkc.side.space_covers_batch",
                           ("integer", "integer")),
    "same_point": ("zkc.side.same_point", ("reduction_contract",)),
    "batch_after_material": ("zkc.side.batch_after_material",
                             ("reduction_contract",)),
    "fri_shape": ("zkc.side.fri_shape",
                  ("integer", "integer", "integer", "integer")),
    "johnson_fold_param": ("zkc.side.johnson_fold_param", ("integer",)),
    "johnson_slack": ("zkc.side.johnson_slack",
                      ("rational", "integer", "integer")),
    "johnson_multiplicity": ("zkc.side.johnson_multiplicity",
                             ("integer", "rational", "integer")),
    "johnson_delta": ("zkc.side.johnson_delta",
                      ("rational", "rational", "integer")),
    "udr_domain_floor": ("zkc.side.udr_domain_floor",
                         ("integer", "integer", "integer")),
    "udr_theta_window": ("zkc.side.udr_theta_window",
                         ("rational", "integer", "integer")),
    "random_words_eta_floor": ("zkc.side.random_words_eta_floor",
                               ("rational", "integer", "integer")),
    "threshold_delta_window": ("zkc.side.threshold_delta_window",
                               ("rational", "integer")),
    "pow_pinned": ("zkc.side.pow_pinned", ("round_adjacency",)),
    "pow_adjacent": ("zkc.side.pow_adjacent", ("round_adjacency",)),
    "duplex_spine": ("zkc.side.duplex_spine", ("path_transition",)),
    "codec_bias_declared": ("zkc.side.codec_bias_declared",
                            ("path_transition",)),
    # The one arity relation the artifact fixes -- a multiplicity column is
    # indexed by its table -- and the lemma's own characteristic hypothesis.
    # Neither ties a declared arity to what was committed; that gap is an
    # external hypothesis, not a machine condition.
    # Every anchor of every consumed claim is tied by the contract to a
    # message role: without it a bound prices a passage between two
    # statements about different objects.
    "consumed_anchors_are_round_material": (
        "zkc.side.consumed_anchors_are_round_material", ("reduction_contract",)),
    # A bound instantiated per round whose quantities come from the whole
    # reduction prices the first round's numbers against every round.
    "single_round": ("zkc.side.single_round", ("reduction_contract",)),
    "multiplicities_match_table": ("zkc.side.multiplicities_match_table",
                              ("integer", "integer")),
    "lookup_fits_characteristic": ("zkc.side.lookup_fits_characteristic",
                                   ("integer", "integer", "integer")),
}

MACHINE_DECIDER_REVISION = "zkc.soundness"

# The typed construction fields a path occurrence offers.  A field outside this
# table is a name for something the sealed artifact does not authenticate.
PATH_BINDING_FIELDS = {
    "sponge.capacity": "integer",
    "sponge.rate": "integer",
    "sponge.alphabet_order": "integer",
    "codec_bias_max": "rational",
    "codec_bias_sum": "rational",
}

RESULT_SORT_OF_ROUND_FIELD = {
    "RoundIndex": "integer",
    "RoundKind": "string",
    "ChallengeSpace": "integer",
    "ChallengeCount": "integer",
    "RoundDegree": "integer",
    "ChallengeSpaceLog2": "integer",
}


# --------------------------------------------------------------------------
# The typing lattice a quantity is analysed into.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class QuantityInfo:
    """What analysis learns about a quantity without a protocol.

    `integrality` and `resource_shape` are the two properties the admitted
    normal form is stated over: an exponent has to be structurally integral
    for the power to be exact, and a product may contain at most one
    resource-valued factor for the result to stay graded-linear.  `constant`
    and `static_offset` are the exact value and the exact resource-free part
    where both are determined by the declaration alone.
    """

    sort: str
    integrality: str = "unknown"  # integer | half_integer | unknown
    resource_shape: str = "none"  # none | monomial | polynomial
    constant: Fraction | None = None
    static_offset: Fraction | None = None


@dataclass(frozen=True)
class QuantityScope:
    """What the enclosing body has lexically bound.

    `round_cases` are the contract-round binders in scope, `bound_coordinate_port`
    is the premise whose coordinate the enclosing body iterates, and
    `forbidden_port` is a premise a body-local expression may not reread
    because the body equation already consumes it exactly once.
    """

    round_cases: frozenset[str] = frozenset()
    bound_coordinate_port: str | None = None
    forbidden_port: str | None = None


@dataclass(frozen=True)
class Environment:
    parameters: dict[str, str]
    resources: dict[str, str]
    facts: dict[str, str]
    premises: dict[str, PremisePort]


def _environment(rule: Rule) -> Environment:
    return Environment(
        {item.name: item.sort for item in rule.parameters},
        {item.name: item.sort for item in rule.resources},
        {item.name: item.sort for item in rule.artifact_facts},
        {port.name: port for port in rule.premises},
    )


# --------------------------------------------------------------------------
# Quantity analysis.
# --------------------------------------------------------------------------


def analyze_quantity(environment: Environment, quantity: Quantity,
                     scope: QuantityScope, where: str) -> QuantityInfo:
    if isinstance(quantity, RationalLiteral):
        value = quantity.value
        integrality = ("integer" if value.denominator == 1
                       else "half_integer" if value.denominator == 2
                       else "unknown")
        return QuantityInfo("integer" if value.denominator == 1 else "rational",
                            integrality, "none", value, value)

    if isinstance(quantity, NamedQuantity):
        table, word = {
            "parameter": (environment.parameters, "parameter"),
            "artifact_fact": (environment.facts, "artifact fact"),
            "resource_variable": (environment.resources, "resource variable"),
        }[quantity.kind]
        sort = table.get(quantity.name)
        if sort is None or sort not in NUMERIC_SORTS:
            raise Refusal(f"{where} reads an unknown or non-numeric "
                          f"{word} '{quantity.name}'")
        integrality = "integer" if sort == "integer" else "unknown"
        if quantity.kind == "resource_variable":
            return QuantityInfo(sort, integrality, "monomial", None, Fraction(0))
        return QuantityInfo(sort, integrality)

    if isinstance(quantity, ContractRoundFact):
        if quantity.case_name not in scope.round_cases:
            raise Refusal(f"{where} reads contract round case "
                          f"'{quantity.case_name}' from outside its lexical case")
        return QuantityInfo("integer", "integer")

    if isinstance(quantity, PremiseCoordinate):
        port = environment.premises.get(quantity.port)
        if port is None or port.expected_result != "extraction":
            raise Refusal(f"{where} projects a coordinate from a non-extraction "
                          f"premise '{quantity.port}'")
        if scope.forbidden_port == quantity.port:
            raise Refusal(f"{where} rereads the premise its body equation "
                          "already consumes")
        if scope.bound_coordinate_port != quantity.port:
            raise Refusal(f"{where} uses a bound coordinate outside the "
                          "binder that introduces it")
        return QuantityInfo("integer", "integer")

    assert isinstance(quantity, QuantityOperation)
    arity = QUANTITY_OPERATIONS[quantity.kind]
    if not quantity.operands:
        raise Refusal(f"{where} has no operands")
    if arity is not None and len(quantity.operands) != arity:
        raise Refusal(f"{where} takes exactly {arity} operands and has "
                      f"{len(quantity.operands)}")
    operands = [
        analyze_quantity(environment, operand, scope, f"{where}.operand[{index}]")
        for index, operand in enumerate(quantity.operands)
    ]
    return _analyze_operation(quantity.kind, operands, where)


def _fold(values: list[Fraction | None], combine) -> Fraction | None:
    if any(value is None for value in values):
        return None
    result = values[0]
    for value in values[1:]:
        result = combine(result, value)
    return result


def _analyze_operation(kind: str, operands: list[QuantityInfo],
                       where: str) -> QuantityInfo:
    additive = kind in ("add", "sub", "mul")
    sort = ("integer" if additive and all(item.sort == "integer"
                                          for item in operands)
            else "rational")

    if kind in ("add", "sub"):
        if kind == "sub" and operands[1].resource_shape != "none":
            raise Refusal(f"{where} subtracts a resource-valued term, which "
                          "could turn a bound negative")
        integrality = _join_integrality(operands)
        shape = ("polynomial"
                 if any(item.resource_shape != "none" for item in operands)
                 else "none")
        combine = ((lambda a, b: a + b) if kind == "add"
                   else (lambda a, b: a - b))
        return QuantityInfo(
            sort, integrality, shape,
            _fold([item.constant for item in operands], combine),
            _fold([item.static_offset for item in operands], combine),
        )

    if kind == "mul":
        resourceful = [item for item in operands
                       if item.resource_shape != "none"]
        if len(resourceful) > 1:
            raise Refusal(f"{where} multiplies two resource-valued factors, "
                          "which leaves the admitted normal form")
        shape = resourceful[0].resource_shape if resourceful else "none"
        integrality = _join_integrality(operands, multiplicative=True)
        constant = _fold([item.constant for item in operands],
                         lambda a, b: a * b)
        if constant is None and resourceful:
            # The empty product is one, so a lone resource factor is a
            # monomial with coefficient one rather than a coefficient nobody
            # wrote.
            coefficient = _fold(
                [item.constant for item in operands
                 if item.resource_shape == "none"] or [Fraction(1)],
                lambda a, b: a * b)
            if coefficient is not None and coefficient < 0:
                raise Refusal(f"{where} scales a resource by a negative "
                              "coefficient")
        return QuantityInfo(
            sort, integrality, shape, constant,
            _fold([item.static_offset for item in operands],
                  lambda a, b: a * b),
        )

    if kind == "div":
        numerator, denominator = operands
        if denominator.resource_shape != "none":
            raise Refusal(f"{where} divides by a resource-valued term")
        if denominator.constant is not None and denominator.constant == 0:
            raise Refusal(f"{where} divides by a static zero")
        if (numerator.resource_shape != "none"
                and denominator.constant is not None
                and denominator.constant < 0):
            raise Refusal(f"{where} divides a resource by a negative constant")
        integrality = "unknown"
        if denominator.constant is not None:
            if abs(denominator.constant) == 1:
                integrality = numerator.integrality
            elif (abs(denominator.constant) == 2
                  and numerator.integrality == "integer"):
                integrality = "half_integer"
        constant = (numerator.constant / denominator.constant
                    if numerator.constant is not None
                    and denominator.constant is not None else None)
        offset = (numerator.static_offset / denominator.constant
                  if numerator.static_offset is not None
                  and denominator.constant is not None else None)
        return QuantityInfo("rational", integrality, numerator.resource_shape,
                            constant, offset)

    if kind == "pow":
        base, exponent = operands
        if exponent.resource_shape != "none":
            raise Refusal(f"{where} raises to a resource-valued exponent")
        power = _static_exponent(exponent, where)
        if power is None and exponent.integrality != "integer":
            raise Refusal(f"{where} raises to an exponent that is not "
                          "structurally integral")
        if base.resource_shape != "none":
            if (base.resource_shape != "monomial" or power is None
                    or power <= 0):
                raise Refusal(f"{where} raises a resource to something other "
                              "than a static positive integer power")
            shape = "monomial"
        else:
            shape = "none"
        integrality = "unknown"
        constant = offset = None
        if power is not None:
            # Integrality, not sort: division and exponentiation are
            # rational-sorted whatever they produce, so an integer-valued
            # expression under one of them keeps its integrality and loses
            # its sort. Reading the sort here would refuse (n/1)^2.
            integrality = ("integer" if power == 0
                           else "integer" if power > 0
                           and base.integrality == "integer"
                           else base.integrality if power == 1
                           else "unknown")
            constant = _exact_power(base.constant, power)
            offset = _exact_power(base.static_offset, power)
        return QuantityInfo("rational", integrality, shape, constant, offset)

    # pow2 and pow2_up: the dyadic bound, and its explicit outward rounding.
    exponent = operands[0]
    if exponent.resource_shape != "none":
        raise Refusal(f"{where} takes a dyadic power of a resource-valued "
                      "exponent")
    power = None
    if exponent.constant is not None:
        if kind == "pow2":
            if exponent.constant.denominator != 1:
                raise Refusal(f"{where} takes a dyadic power of a non-integer")
            power = int(exponent.constant)
        else:
            if exponent.constant.denominator not in (1, 2):
                raise Refusal(f"{where} rounds an exponent that is not a "
                              "half-integer")
            power = -((-exponent.constant.numerator)
                      // exponent.constant.denominator)
    elif kind == "pow2" and exponent.integrality != "integer":
        raise Refusal(f"{where} takes a dyadic power of an exponent that is "
                      "not structurally integral")
    elif kind == "pow2_up" and exponent.integrality == "unknown":
        raise Refusal(f"{where} rounds an exponent that is not structurally "
                      "half-integral")
    if power is None:
        return QuantityInfo("rational")
    if abs(power) > EXPONENT_LIMIT:
        raise Refusal(f"{where} has a dyadic exponent outside the exact range")
    value = Fraction(2) ** power
    integrality = ("integer" if power >= 0
                   else "half_integer" if power == -1 else "unknown")
    return QuantityInfo("rational", integrality, "none", value, value)


def _join_integrality(operands: list[QuantityInfo], *,
                      multiplicative: bool = False) -> str:
    if any(item.integrality == "unknown" for item in operands):
        return "unknown"
    halves = sum(1 for item in operands if item.integrality == "half_integer")
    if multiplicative:
        return ("integer" if halves == 0
                else "half_integer" if halves == 1 else "unknown")
    return "half_integer" if halves else "integer"


def _static_exponent(exponent: QuantityInfo, where: str) -> int | None:
    if exponent.constant is None:
        return None
    if exponent.constant.denominator != 1:
        raise Refusal(f"{where} raises to a non-integer exponent")
    power = int(exponent.constant)
    if abs(power) > EXPONENT_LIMIT:
        raise Refusal(f"{where} has an exponent outside the exact range")
    return power


def _exact_power(base: Fraction | None, power: int) -> Fraction | None:
    if base is None:
        return None
    if base == 0 and power < 0:
        raise Refusal("a negative power of zero is outside the exact domain")
    return base ** power


def check_domain(info: QuantityInfo, domain: str, where: str) -> None:
    """`positive_integer` for a structural size, `non_negative` otherwise.

    A structural arity or challenge space is a property of the protocol shape
    and cannot depend on how much work an adversary does, which is why a
    resource anywhere in one refuses.
    """
    if domain == "positive_integer":
        if info.resource_shape != "none":
            raise Refusal(f"{where} lets a structural size depend on a resource")
        if info.constant is not None:
            if info.constant <= 0:
                raise Refusal(f"{where} is statically non-positive")
            if info.constant.denominator != 1:
                raise Refusal(f"{where} is statically non-integral")
        return
    if info.constant is not None and info.constant < 0:
        raise Refusal(f"{where} is statically negative")
    if info.static_offset is not None and info.static_offset < 0:
        raise Refusal(f"{where} has a statically negative constant term")


def _require_resource_free(expression: Quantity, where: str) -> None:
    """A premise resource substitution may name conclusion resources and exact
    arithmetic and nothing else: a parameter or a protocol fact reaching into
    one would let the caller's numbers change what a premise means."""
    if isinstance(expression, (NamedQuantity, ContractRoundFact,
                              PremiseCoordinate)):
        if not (isinstance(expression, NamedQuantity)
                and expression.kind == "resource_variable"):
            raise Refusal(f"{where} lets a premise resource depend on something "
                          "other than conclusion resources and exact arithmetic")
    if isinstance(expression, QuantityOperation):
        for operand in expression.operands:
            _require_resource_free(operand, where)


# --------------------------------------------------------------------------
# Bound analysis.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class BoundInfo:
    ground: bool


def analyze_bound(environment: Environment, schemas: SchemaContext, bound: Bound,
                  scope: QuantityScope, where: str) -> BoundInfo:
    if isinstance(bound, QuantityBound):
        info = analyze_quantity(environment, bound.quantity, scope,
                                f"{where}.quantity")
        check_domain(info, "non_negative", f"{where}.quantity")
        return BoundInfo(info.resource_shape == "none")

    if isinstance(bound, ScalarBound):
        if scope.forbidden_port == bound.premise_port:
            raise Refusal(f"{where} rereads the premise its body equation "
                          "already consumes")
        port = environment.premises.get(bound.premise_port)
        if port is None or port.expected_result != "scalar":
            raise Refusal(f"{where} projects a scalar from premise "
                          f"'{bound.premise_port}', which carries no scalar")
        return BoundInfo(False)

    if isinstance(bound, PrimitiveAdvantage):
        _check_game(environment, schemas, bound, scope, where)
        return BoundInfo(False)

    if isinstance(bound, ScaledBound):
        if len(bound.operands) != 1:
            raise Refusal(f"{where} scales {len(bound.operands)} bounds and "
                          "must scale exactly one")
        info = analyze_quantity(environment, bound.scale, scope, f"{where}.scale")
        if info.resource_shape != "none":
            raise Refusal(f"{where} scales by a resource-valued coefficient")
        check_domain(info, "non_negative", f"{where}.scale")
        return BoundInfo(analyze_bound(environment, schemas, bound.operands[0],
                                       scope, f"{where}.bound[0]").ground)

    assert isinstance(bound, BoundOperation)
    if not bound.operands:
        raise Refusal(f"{where} aggregates no bounds")
    ground = True
    for index, operand in enumerate(bound.operands):
        ground &= analyze_bound(environment, schemas, operand, scope,
                                f"{where}.bound[{index}]").ground
    if bound.kind == "max" and not ground:
        raise Refusal(f"{where} takes a maximum over symbolic alternatives, "
                      "which the exact normal form cannot decide")
    return BoundInfo(ground)


def _check_game(environment: Environment, schemas: SchemaContext,
                bound: PrimitiveAdvantage, scope: QuantityScope,
                where: str) -> None:
    definition = None
    for identifier, ref, argument_types, resources in schemas.primitive_games:
        if identifier == bound.game.ref:
            definition = (ref, argument_types, resources)
            break
    if definition is None:
        raise Refusal(f"{where} names an unknown primitive game "
                      f"'{bound.game.ref}'")
    ref, argument_types, resources = definition
    if not ref.id or not ref.source_revision or ref.id != bound.game.ref:
        raise Refusal(f"{where} names a primitive game whose declaration does "
                      "not carry its own exact reference")
    if len(argument_types) != len(bound.game.instance_arguments):
        raise Refusal(f"{where} supplies {len(bound.game.instance_arguments)} "
                      f"instance arguments and the game takes "
                      f"{len(argument_types)}")
    for index, (expected, argument) in enumerate(
            zip(argument_types, bound.game.instance_arguments)):
        check_binding_value(environment, argument, expected,
                            f"{where}.game_argument[{index}]")
    names = [item.name for item in resources]
    if len(set(names)) != len(names):
        raise Refusal(f"{where} names a primitive game that declares one "
                      "resource twice")
    for item in resources:
        if item.sort not in NUMERIC_SORTS:
            raise Refusal(f"{where} names a primitive game whose resource "
                          f"'{item.name}' is not numeric")
    supplied = {name for name, _ in bound.resource_substitution}
    if supplied != set(names):
        raise Refusal(f"{where} does not substitute the game's resources "
                      "totally")
    declared = {item.name: item.sort for item in resources}
    for name, expression in bound.resource_substitution:
        at = f"{where}.game_resource.{name}"
        info = analyze_quantity(environment, expression, scope, at)
        check_domain(info, "non_negative", at)
        if info.sort != declared[name]:
            raise Refusal(f"{at} substitutes a {info.sort} for a "
                          f"{declared[name]} resource")


# --------------------------------------------------------------------------
# Binding values.
# --------------------------------------------------------------------------


def check_binding_value(environment: Environment, value, expected_sort: str,
                        where: str) -> None:
    if value.sort != expected_sort:
        raise Refusal(f"{where} is declared {value.sort} where "
                      f"{expected_sort} is required")

    # Constructor-level provenance: three sorts name authenticated protocol
    # structure, and each has exactly one constructor that can produce it. A
    # value of the same runtime sort from any other source would let a
    # declaration assert a fact it never read.
    if expected_sort == "reduction_contract":
        if (value.kind != "sealed_artifact_projection"
                or value.artifact_projection.kind
                != "conclusion_reduction_contract"):
            raise Refusal(f"{where} must be the sealed conclusion contract")
    if expected_sort == "round_adjacency":
        if (value.kind != "sealed_artifact_projection"
                or value.artifact_projection.kind != "contract_round_adjacency"):
            raise Refusal(f"{where} must be the sealed contract-round adjacency")
    if expected_sort == "path_transition":
        if value.kind != "application_path_transition":
            raise Refusal(f"{where} must be the selected application path "
                          "transition")

    if value.kind == "literal":
        _check_literal(value, where)
    elif value.kind == "sealed_artifact_projection":
        projection = value.artifact_projection
        if projection.result_sort != value.sort:
            raise Refusal(f"{where} projects a {projection.result_sort} into a "
                          f"{value.sort} position")
        _check_projection(projection, f"{where}.artifact_projection")
    elif value.kind == "conclusion_subject":
        if value.sort != "subject":
            raise Refusal(f"{where} reads the conclusion subject at sort "
                          f"{value.sort}")
    elif value.kind == "application_path_transition":
        if value.sort != "path_transition":
            raise Refusal(f"{where} reads the path transition at sort "
                          f"{value.sort}")
    elif value.kind == "conclusion_resource":
        if environment.resources.get(value.reference) != value.sort:
            raise Refusal(f"{where} names an unknown or ill-typed conclusion "
                          f"resource '{value.reference}'")
    else:
        if environment.parameters.get(value.reference) != value.sort:
            raise Refusal(f"{where} names an unknown or ill-typed parameter "
                          f"'{value.reference}'")


def _check_literal(value, where: str) -> None:
    if value.sort == "integer":
        if not isinstance(value.literal, Fraction) or value.literal.denominator != 1:
            raise Refusal(f"{where} is not an exact integer literal")
    elif value.sort == "rational":
        if not isinstance(value.literal, Fraction):
            raise Refusal(f"{where} is not an exact rational literal")
    elif value.sort == "string":
        if not isinstance(value.literal, str):
            raise Refusal(f"{where} is not a string literal")
    elif value.sort == "boolean":
        if not isinstance(value.literal, bool):
            raise Refusal(f"{where} is not a boolean literal")
    elif value.sort == "algebra_instance":
        algebra = value.literal
        if (not algebra.group or not algebra.field_class
                or algebra.field_order.denominator != 1
                or algebra.field_order <= 0):
            raise Refusal(f"{where} is not an exact positive-order carrier")
    else:
        raise Refusal(f"{where} has no literal constructor for sort "
                      f"{value.sort}")


def _check_projection(projection, where: str) -> None:
    kind = projection.kind
    if kind == "conclusion_reduction_contract":
        if projection.result_sort != "reduction_contract":
            raise Refusal(f"{where} does not produce a reduction contract")
    elif kind == "contract_round_adjacency":
        if projection.result_sort != "round_adjacency":
            raise Refusal(f"{where} does not produce a round adjacency")
    elif kind == "reduction_input_count":
        if projection.result_sort != "integer":
            raise Refusal(f"{where} does not produce an integer count")
    elif kind == "bound_relation_anchor_count":
        if projection.result_sort != "integer":
            raise Refusal(f"{where} does not produce an integer count")
    elif kind == "committed_arity":
        if projection.result_sort != "integer":
            raise Refusal(f"{where} does not produce an integer arity")
    elif kind == "reduction_parameter":
        if projection.result_sort not in ("integer", "rational", "string",
                                          "boolean"):
            raise Refusal(f"{where} reads a reduction parameter at a sort no "
                          "parameter carries")
    elif kind == "path_binding_field":
        expected = PATH_BINDING_FIELDS.get(projection.field)
        if expected is None:
            raise Refusal(f"{where} names an unknown path-binding field "
                          f"'{projection.field}'")
        if expected != projection.result_sort:
            raise Refusal(f"{where} reads path-binding field "
                          f"'{projection.field}' at the wrong sort")
    else:
        expected = RESULT_SORT_OF_ROUND_FIELD[projection.field]
        if projection.aggregate == "count":
            if projection.result_sort != "integer":
                raise Refusal(f"{where} counts rounds into a non-integer")
        elif projection.result_sort != expected:
            raise Refusal(f"{where} reads round field '{projection.field}' at "
                          "the wrong sort")


# --------------------------------------------------------------------------
# RULE_WF.
# --------------------------------------------------------------------------


def index_admitted(schemas: SchemaContext, index: SecurityIndex) -> bool:
    needs_variant, needs_model = INDEX_SHAPE[index.notion]
    if bool(index.variant) != needs_variant:
        return False
    if needs_model:
        if index.model != "duplex":
            return False
    elif index.model:
        return False
    # A quantification variable describes a set of indices rather than
    # one, so what it must satisfy is satisfiability: some admitted
    # index matches it on every other coordinate. For a literal this
    # degenerates to membership.
    if index.quantification.startswith("$"):
        return any(
            replace(index, quantification=admitted.quantification) == admitted
            for admitted in schemas.security_indices)
    return index in schemas.security_indices


def _subject_schema(schemas: SchemaContext, identifier: str):
    for entry in schemas.subject_schemas:
        if entry[0] == identifier:
            return entry
    return None


def _check_subject_schema(schemas: SchemaContext, identifier: str, where: str):
    entry = _subject_schema(schemas, identifier)
    if entry is None:
        raise Refusal(f"{where} names an unadmitted subject schema "
                      f"'{identifier}'")
    _, kind, argument_types = entry
    if kind == "protocol_claim":
        valid = identifier == "zkc.subject.protocol_claim" and not argument_types
    elif kind == "consumed_claim_vector":
        valid = (identifier == "zkc.subject.consumed_claim_vector"
                 and not argument_types)
    else:
        valid = (identifier not in ("zkc.subject.protocol_claim",
                                    "zkc.subject.consumed_claim_vector")
                 and bool(argument_types))
    if not valid:
        raise Refusal(f"{where} names a subject schema whose kind and "
                      "arguments disagree")
    return entry


def check_rule_well_formed(schemas: SchemaContext, rule: Rule) -> None:
    where = f"rule '{rule.id}'"
    conclusion = rule.conclusion_index
    if conclusion.quantification.startswith("$"):
        # A conclusion's variable restates what a premise bound; with no
        # premise naming it there is nothing to restate and the
        # conclusion denotes no index at all. The instantiated index is
        # checked where the conclusion is assembled, since which index
        # that is depends on the derivation.
        if not any(port.expected_index.quantification
                   == conclusion.quantification for port in rule.premises):
            raise Refusal(f"{where} concludes an index variable no premise "
                          "binds")
    # The variable is a rule-level device with one name: a premise binds
    # it and the conclusion restates it. A premise naming a variable the
    # conclusion does not restate binds a value the conclusion discards,
    # and a conclusion whose literal is stronger than the discarded value
    # would then claim more than any premise established.
    for port in rule.premises:
        if (port.expected_index.quantification.startswith("$")
                and port.expected_index.quantification
                != conclusion.quantification):
            raise Refusal(f"{where} premise '{port.name}' binds an index "
                          "variable the conclusion does not restate")
    if not index_admitted(schemas, conclusion):
        raise Refusal(f"{where} concludes an index the vocabulary does not "
                      "admit")
    for item in rule.resources:
        if item.sort not in NUMERIC_SORTS:
            raise Refusal(f"{where} declares a non-numeric resource "
                          f"'{item.name}'")
    environment = _environment(rule)

    for port in rule.premises:
        at = f"{where} premise '{port.name}'"
        if not index_admitted(schemas, port.expected_index):
            raise Refusal(f"{at} expects an unadmitted index")
        if port.expected_result != RESULT_OF_NOTION[port.expected_index.notion]:
            raise Refusal(f"{at} expects a result schema its index does not "
                          "carry")
        _check_subject_schema(schemas, port.expected_subject_schema, at)
        for item in port.expected_resources:
            if item.sort not in NUMERIC_SORTS:
                raise Refusal(f"{at} declares a non-numeric resource "
                              f"'{item.name}'")
        declared = {item.name: item.sort for item in port.expected_resources}
        supplied = {name for name, _ in port.resource_substitution}
        if supplied != set(declared):
            raise Refusal(f"{at} does not substitute its resources totally")
        for name, expression in port.resource_substitution:
            substitution_at = f"{at} substitution '{name}'"
            _require_resource_free(expression, substitution_at)
            info = analyze_quantity(environment, expression, QuantityScope(),
                                    substitution_at)
            check_domain(info, "non_negative", substitution_at)
            if info.sort != declared[name]:
                raise Refusal(f"{substitution_at} changes the resource's sort")

    for condition in rule.machine_conditions:
        at = f"{where} condition '{condition.slot}'"
        entry = None
        for identifier, kind, ref, argument_types in schemas.machine_deciders:
            if identifier == condition.ref:
                entry = (kind, ref, argument_types)
                break
        if entry is None:
            raise Refusal(f"{at} names an undeclared decider '{condition.ref}'")
        kind, ref, argument_types = entry
        canonical = MACHINE_DECIDERS.get(kind)
        if canonical is None:
            raise Refusal(f"{at} names a decider kind this binary does not "
                          f"implement: '{kind}'")
        if (ref.id != canonical[0] or ref.source_revision
                != MACHINE_DECIDER_REVISION or ref.id != condition.ref):
            raise Refusal(f"{at} names a decider whose declared identity is "
                          "not the one the binary implements")
        if argument_types != canonical[1] or condition.argument_types != canonical[1]:
            raise Refusal(f"{at} restates the decider's argument signature")

    for hypothesis in rule.external_hypotheses:
        at = f"{where} hypothesis '{hypothesis.slot}'"
        entry = None
        for identifier, ref, argument_types in schemas.propositions:
            if identifier == hypothesis.ref:
                entry = (ref, argument_types)
                break
        if entry is None:
            raise Refusal(f"{at} names an undeclared proposition "
                          f"'{hypothesis.ref}'")
        ref, argument_types = entry
        if not ref.id or not ref.source_revision or ref.id != hypothesis.ref:
            raise Refusal(f"{at} names a proposition whose declaration does not "
                          "carry its own exact reference")
        if argument_types != hypothesis.argument_types:
            raise Refusal(f"{at} restates the proposition's argument signature")

    for pin in rule.exact_parameter_pins:
        at = f"{where} pin on '{pin.parameter}'"
        sort = environment.parameters.get(pin.parameter)
        if sort is None:
            raise Refusal(f"{at} names no declared parameter")
        if pin.expected.kind != "literal" or pin.expected.sort != sort:
            raise Refusal(f"{at} expects a nonliteral or ill-typed value")
        check_binding_value(environment, pin.expected, sort, f"{at} expected")

    _check_body(environment, schemas, rule, where)


def _check_body(environment: Environment, schemas: SchemaContext, rule: Rule,
                where: str) -> None:
    body = rule.body
    conclusion = rule.conclusion_index
    port_field, premise_notion, carries_variant = BODY_LAW[body.kind]
    expected_premises = 0 if premise_notion is None else 1
    if len(rule.premises) != expected_premises:
        raise Refusal(f"{where} body '{body.kind}' takes {expected_premises} "
                      f"premises and the rule declares {len(rule.premises)}")
    _, expected_notion = _body_conclusion(body.kind)
    if conclusion.notion != expected_notion:
        raise Refusal(f"{where} body '{body.kind}' cannot conclude "
                      f"'{conclusion.notion}'")

    premise_port = None
    if premise_notion is not None:
        name = body.get(port_field)
        expected_index = SecurityIndex(
            premise_notion, conclusion.track,
            conclusion.variant if carries_variant else "",
            conclusion.model if body.kind == "round_scaling" else "",
            conclusion.quantification,
        )
        premise_port = environment.premises.get(name) if name else None
        # A premise whose quantification is a variable matches whatever
        # the body asks for on that coordinate alone; every other
        # coordinate is compared exactly.
        def _port_carries(pattern: SecurityIndex) -> bool:
            if pattern.quantification.startswith("$"):
                return (replace(pattern,
                                quantification=expected_index.quantification)
                        == expected_index)
            return pattern == expected_index
        if (premise_port is None
                or not _port_carries(premise_port.expected_index)
                or premise_port.expected_result
                != RESULT_OF_NOTION[premise_notion]):
            raise Refusal(f"{where} body reads premise '{name}', which does not "
                          "carry the exact index its equation needs")

    scope = QuantityScope()
    if body.kind == "special_soundness_entry":
        _check_coordinates(environment, body.get("coordinates"),
                           f"{where}.body.coordinates")
    elif body.kind == "native_round_by_round_entry":
        _check_rounds(environment, schemas, body.get("rounds"),
                      f"{where}.body.rounds")
    elif body.kind == "computational_entry":
        _check_coordinates(environment, body.get("coordinates"),
                           f"{where}.body.coordinates")
        analyze_bound(environment, schemas, body.get("failure_bound"), scope,
                      f"{where}.body.failure_bound")
    elif body.kind == "completeness_entry":
        analyze_bound(environment, schemas, body.get("bound"), scope,
                      f"{where}.body.bound")
    elif body.kind == "special_soundness_preservation":
        _check_coordinates(environment, body.get("appended_coordinates"),
                           f"{where}.body.appended_coordinates")
        analyze_bound(environment, schemas, body.get("conclusion_failure_bound"),
                      scope, f"{where}.body.conclusion_failure_bound")
    elif body.kind == "round_by_round_preservation":
        # The appended rounds are checked exactly as an entry's are; the
        # concatenation itself combines no bounds, so there is nothing else
        # for a declaration to carry.  The body-level spine guards are
        # application-time facts and live in the evaluator.
        _check_rounds(environment, schemas, body.get("appended_rounds"),
                      f"{where}.body.appended_rounds")
    elif body.kind == "round_scaling":
        selected = body.get("selected_round")
        if selected.kind == "adjacent_predecessor_round":
            if environment.facts.get(selected.adjacency_fact_port) != "round_adjacency":
                raise Refusal(f"{where} selects an adjacent round through "
                              "something that is not a typed adjacency fact")
        info = analyze_quantity(environment, body.get("scale"), scope,
                                f"{where}.body.scale")
        if info.resource_shape != "none":
            raise Refusal(f"{where} scales a round by a resource-valued factor")
        check_domain(info, "non_negative", f"{where}.body.scale")
    elif body.kind == "special_soundness_to_round_by_round":
        analyze_bound(
            environment, schemas, body.get("per_coordinate_bound"),
            QuantityScope(bound_coordinate_port=body.get("special_soundness_port")),
            f"{where}.body.per_coordinate_bound")
    elif body.kind == "round_by_round_to_state_restoration":
        # Multiplying the premise's round maximum by a formal move budget would
        # otherwise create a resource times a primitive advantage, outside the
        # admitted normal form.  The premise has to rule that out, and the rule
        # has to say so rather than the evaluator discovering it.
        constraints = set(premise_port.result_constraints) if premise_port else set()
        if constraints != {"requires_empty_game_support",
                           "requires_no_bound_resource_support"}:
            raise Refusal(f"{where} multiplies a premise round maximum by a "
                          "move budget without requiring the premise to be "
                          "ground and information-theoretic")
        info = analyze_quantity(environment, body.get("move_budget"), scope,
                                f"{where}.body.move_budget")
        check_domain(info, "non_negative", f"{where}.body.move_budget")
    else:
        analyze_bound(
            environment, schemas, body.get("local_duplex_bound"),
            QuantityScope(forbidden_port=body.get("state_restoration_port")),
            f"{where}.body.local_duplex_bound")


def _body_conclusion(kind: str) -> tuple[tuple[str, ...], str]:
    from .signature import BODY_SIGNATURES
    return BODY_SIGNATURES[kind]


def _check_sequence_cases(environment: Environment, sequence: Sequence,
                          where: str) -> None:
    if environment.facts.get(sequence.contract_fact_port) != "reduction_contract":
        raise Refusal(f"{where} resolves against something that is not a typed "
                      "contract fact")
    selectors = [case.selector for case in sequence.cases]
    if any(kind == "all_contract_rounds" for kind, _ in selectors) and len(selectors) > 1:
        raise Refusal(f"{where} pairs a catch-all case with another case")
    if len(set(selectors)) != len(selectors):
        raise Refusal(f"{where} declares two cases that select the same rounds")


def _check_coordinates(environment: Environment, sequence: Sequence,
                       where: str) -> None:
    if sequence.kind == "explicit":
        for index, coordinate in enumerate(sequence.entries):
            at = f"{where}.coordinate[{index}]"
            check_domain(analyze_quantity(environment, coordinate.arity,
                                          QuantityScope(), f"{at}.arity"),
                         "positive_integer", f"{at}.arity")
            if coordinate.challenge_space is not None:
                check_domain(
                    analyze_quantity(environment, coordinate.challenge_space,
                                     QuantityScope(), f"{at}.space"),
                    "positive_integer", f"{at}.space")
        return
    _check_sequence_cases(environment, sequence, where)
    for index, case in enumerate(sequence.cases):
        at = f"{where}.case[{index}]"
        scope = QuantityScope(round_cases=frozenset({case.case_name}))
        if case.arity is None:
            raise Refusal(f"{at} declares a coordinate with no arity")
        check_domain(analyze_quantity(environment, case.arity, scope,
                                      f"{at}.arity"),
                     "positive_integer", f"{at}.arity")
        check_domain(analyze_quantity(environment, case.challenge_space, scope,
                                      f"{at}.space"),
                     "positive_integer", f"{at}.space")


def _check_rounds(environment: Environment, schemas: SchemaContext,
                  sequence: Sequence, where: str) -> None:
    if sequence.kind == "explicit":
        for index, round_template in enumerate(sequence.entries):
            at = f"{where}.round[{index}]"
            check_domain(
                analyze_quantity(environment, round_template.challenge_space,
                                 QuantityScope(), f"{at}.space"),
                "positive_integer", f"{at}.space")
            analyze_bound(environment, schemas, round_template.bound,
                          QuantityScope(), f"{at}.bound")
        return
    _check_sequence_cases(environment, sequence, where)
    for index, case in enumerate(sequence.cases):
        at = f"{where}.case[{index}]"
        scope = QuantityScope(round_cases=frozenset({case.case_name}))
        check_domain(analyze_quantity(environment, case.challenge_space, scope,
                                      f"{at}.space"),
                     "positive_integer", f"{at}.space")
        if case.bound is None:
            raise Refusal(f"{at} declares a round with no bound")
        analyze_bound(environment, schemas, case.bound, scope, f"{at}.bound")


# --------------------------------------------------------------------------
# Binding well-formedness.
# --------------------------------------------------------------------------


def check_binding_well_formed(schemas: SchemaContext, rule: Rule,
                              binding: Binding) -> None:
    check_rule_well_formed(schemas, rule)
    where = f"binding '{binding.id}'"
    if rule.status != "admitted":
        raise Refusal(f"{where} names rule '{rule.id}', which is declared and "
                      "therefore unreachable")
    if binding.rule_revision != rule.revision():
        raise Refusal(f"{where} does not name the exact rule revision")
    if not binding.anchor_ref.id or not binding.anchor_ref.source_revision:
        raise Refusal(f"{where} carries an incomplete protocol anchor")
    entry = _check_subject_schema(schemas, binding.subject_schema, where)
    if entry[1] != "protocol_claim":
        raise Refusal(f"{where} concludes about something other than an exact "
                      "protocol claim")

    environment = _environment(rule)
    _cover(binding.parameter_bindings, [item.name for item in rule.parameters],
           f"{where} parameters")
    for item in rule.parameters:
        value = dict(binding.parameter_bindings)[item.name]
        at = f"{where} parameter '{item.name}'"
        check_binding_value(environment, value, item.sort, at)
        _check_anchor(binding, value, at)
    _cover(binding.fact_bindings, [item.name for item in rule.artifact_facts],
           f"{where} facts")
    for item in rule.artifact_facts:
        value = dict(binding.fact_bindings)[item.name]
        at = f"{where} fact '{item.name}'"
        check_binding_value(environment, value, item.sort, at)
        _check_anchor(binding, value, at)

    _cover(binding.premise_relations, [port.name for port in rule.premises],
           f"{where} premise relations")
    relations = dict(binding.premise_relations)
    for port in rule.premises:
        _check_relation(schemas, binding, port, relations[port.name],
                        environment, f"{where} premise '{port.name}'")

    _check_arguments(environment, binding, binding.condition_argument_bindings,
                     rule.machine_conditions, f"{where} condition")
    _check_arguments(environment, binding, binding.hypothesis_argument_bindings,
                     rule.external_hypotheses, f"{where} hypothesis")

    # A primitive-game instance argument is a binding value like any other, and
    # the body is the one place they are typed without an occurrence in hand.
    # A rule is reusable across bindings whose anchors differ, so whether a
    # path field is reachable is a question only the binding can answer.
    game_arguments: list[Any] = []
    _collect_game_arguments(rule.body, game_arguments)
    for index, argument in enumerate(game_arguments):
        _check_anchor(binding, argument,
                      f"{where} body game argument[{index}]")

    _check_reachability(rule, binding, where)


def _collect_game_arguments(node: Any, into: list[Any]) -> None:
    if isinstance(node, PrimitiveAdvantage):
        into.extend(node.game.instance_arguments)
        return
    for attribute in ("operands", "entries", "cases"):
        for child in getattr(node, attribute, ()) or ():
            _collect_game_arguments(child, into)
    child = getattr(node, "bound", None)
    if child is not None:
        _collect_game_arguments(child, into)
    if hasattr(node, "fields"):
        for _, value in node.fields:
            _collect_game_arguments(value, into)


def _cover(supplied, required: list[str], where: str) -> None:
    keys = {name for name, _ in supplied}
    if keys != set(required):
        missing = sorted(set(required) - keys)
        extra = sorted(keys - set(required))
        detail = (f"is missing {missing[0]!r}" if missing
                  else f"carries an unwanted {extra[0]!r}")
        raise Refusal(f"{where} coverage is not exact: it {detail}")


def _check_anchor(binding: Binding, value, where: str) -> None:
    """A value's source has to be reachable from the occurrence the binding
    names: a path field at a reduction site, or a reduction projection at a
    path site, reads something that occurrence does not have."""
    if value.kind == "application_path_transition":
        if binding.anchor_kind != "path_transition":
            raise Refusal(f"{where} reads a path transition at a reduction "
                          "occurrence")
        return
    if value.kind != "sealed_artifact_projection":
        return
    if value.artifact_projection.kind == "path_binding_field":
        if binding.anchor_kind != "path_transition":
            raise Refusal(f"{where} reads a path field at a reduction "
                          "occurrence")
        return
    # A fact about the whole artifact rather than one occurrence, so it
    # is readable from either anchor kind.
    if value.artifact_projection.kind == "bound_relation_anchor_count":
        return
    if binding.anchor_kind != "reduction_contract":
        raise Refusal(f"{where} reads a reduction projection at a path "
                      "occurrence")


def _check_relation(schemas: SchemaContext, binding: Binding, port: PremisePort,
                    relation, environment: Environment, where: str) -> None:
    entry = _subject_schema(schemas, port.expected_subject_schema)
    if entry is None:
        raise Refusal(f"{where} expects an unadmitted subject schema")
    schema_kind = entry[1]
    if relation.kind == "same_subject":
        if port.expected_subject_schema != binding.subject_schema:
            raise Refusal(f"{where} claims the conclusion's own subject while "
                          "expecting a different schema")
        return
    if relation.kind == "consumed_claim":
        if (binding.anchor_kind != "reduction_contract"
                or len(relation.input_indices) != 1
                or schema_kind != "protocol_claim"):
            raise Refusal(f"{where} consumes one reduction input and the "
                          "occurrence or premise schema does not permit it")
        return
    if relation.kind == "consumed_claim_vector":
        whole = (relation.selector == "all_reduction_inputs"
                 and not relation.input_indices)
        listed = (relation.selector == "reduction_inputs"
                  and bool(relation.input_indices))
        if (binding.anchor_kind != "reduction_contract"
                or not (whole or listed)
                or schema_kind != "consumed_claim_vector"):
            raise Refusal(f"{where} selects a claim vector the occurrence or "
                          "premise schema does not permit")
        return
    if relation.external_subject_schema != port.expected_subject_schema:
        raise Refusal(f"{where} asserts a subject schema the premise does not "
                      "expect")
    if schema_kind != "external_instance":
        raise Refusal(f"{where} asserts an external subject against a premise "
                      "that expects a protocol one")
    argument_types = entry[2]
    if len(relation.external_arguments) != len(argument_types):
        raise Refusal(f"{where} supplies the wrong number of external subject "
                      "arguments")
    for index, (expected, argument) in enumerate(
            zip(argument_types, relation.external_arguments)):
        at = f"{where} argument[{index}]"
        check_binding_value(environment, argument, expected, at)
        _check_anchor(binding, argument, at)


def _check_arguments(environment: Environment, binding: Binding, supplied,
                     templates, where: str) -> None:
    _cover(supplied, [template.slot for template in templates], where)
    table = dict(supplied)
    for template in templates:
        arguments = table[template.slot]
        at = f"{where} '{template.slot}'"
        if len(arguments) != len(template.argument_types):
            raise Refusal(f"{at} supplies {len(arguments)} arguments and the "
                          f"template takes {len(template.argument_types)}")
        for index, (expected, argument) in enumerate(
                zip(template.argument_types, arguments)):
            argument_at = f"{at}[{index}]"
            check_binding_value(environment, argument, expected, argument_at)
            _check_anchor(binding, argument, argument_at)


def _check_reachability(rule: Rule, binding: Binding, where: str) -> None:
    """A declared parameter that nothing reads is not inert.

    It is bound, so it demands a value from the caller, and it can carry the
    same quantity a condition asserts as a separate literal with nothing tying
    the two together.  Requiring every parameter to be reached forces the one
    value to have one source.
    """
    read: set[str] = set()
    _collect_parameters(rule.body, read)
    for pin in rule.exact_parameter_pins:
        read.add(pin.parameter)
    bound = dict(binding.parameter_bindings)
    for _, values in (list(binding.condition_argument_bindings)
                      + list(binding.hypothesis_argument_bindings)):
        for value in values:
            if value.kind == "resolved_parameter":
                read.add(value.reference)
            # A parameter also counts as read when a condition argument is the
            # very same projection the parameter is bound to: the value has one
            # source, which is what the check exists to force.  A literal is
            # not such a source, so an equal literal proves nothing.
            for name, bound_value in bound.items():
                if bound_value.kind != "literal" and value == bound_value:
                    read.add(name)
    for item in rule.parameters:
        if item.name not in read:
            raise Refusal(f"{where} binds parameter '{item.name}', which "
                          "neither the rule body nor any argument of this "
                          "binding reads")


def _collect_parameters(node: Any, into: set[str]) -> None:
    if isinstance(node, NamedQuantity):
        if node.kind == "parameter":
            into.add(node.name)
        return
    if isinstance(node, QuantityOperation):
        for operand in node.operands:
            _collect_parameters(operand, into)
        return
    if isinstance(node, QuantityBound):
        _collect_parameters(node.quantity, into)
        return
    if isinstance(node, (BoundOperation,)):
        for operand in node.operands:
            _collect_parameters(operand, into)
        return
    if isinstance(node, ScaledBound):
        _collect_parameters(node.scale, into)
        for operand in node.operands:
            _collect_parameters(operand, into)
        return
    if isinstance(node, PrimitiveAdvantage):
        for argument in node.game.instance_arguments:
            if argument.kind == "resolved_parameter":
                into.add(argument.reference)
        for _, expression in node.resource_substitution:
            _collect_parameters(expression, into)
        return
    if isinstance(node, Sequence):
        for entry in node.entries:
            for child in (getattr(entry, "arity", None),
                          getattr(entry, "challenge_space", None),
                          getattr(entry, "bound", None)):
                if child is not None:
                    _collect_parameters(child, into)
        for case in node.cases:
            for child in (case.arity, case.challenge_space, case.bound):
                if child is not None:
                    _collect_parameters(child, into)
        return
    if hasattr(node, "fields"):  # a rule body
        for _, value in node.fields:
            _collect_parameters(value, into)


# --------------------------------------------------------------------------
# Freeze.
# --------------------------------------------------------------------------


def freeze(signature: Signature) -> Signature:
    """The only construction boundary.

    Every rule passes RULE_WF, every binding names an exact rule revision in
    the same snapshot and passes binding well-formedness.  A signature that
    does not freeze is not one anything may be derived against.
    """
    check_schemas(signature.schemas)
    for rule in signature.rules:
        check_rule_well_formed(signature.schemas, rule)
    for binding in signature.bindings:
        check_binding_well_formed(signature.schemas,
                                  signature.rule(binding.rule), binding)
    check_annotations(signature)
    return signature


def load(document: Any, source: str = "signature") -> Signature:
    return freeze(read_signature(document, source))


# --------------------------------------------------------------------------
# The schema tables, and the record beside the declarations.
# --------------------------------------------------------------------------


def check_schemas(schemas: SchemaContext) -> None:
    """Every entry in a closed table is checked, not only the reached ones.

    A table entry is a declaration in its own right: an unreferenced decider
    whose canonical identity is wrong is a name for code that does not exist,
    and it becomes reachable the moment a rule cites it.
    """
    for identifier, kind, ref, argument_types in schemas.machine_deciders:
        at = f"decider '{identifier}'"
        canonical = MACHINE_DECIDERS.get(kind)
        if canonical is None:
            raise Refusal(f"{at} names a decider kind this binary does not "
                          f"implement: '{kind}'")
        if (ref.id != canonical[0] or ref.id != identifier
                or ref.source_revision != MACHINE_DECIDER_REVISION):
            raise Refusal(f"{at} declares an identity that is not the one the "
                          "binary implements")
        if argument_types != canonical[1]:
            raise Refusal(f"{at} restates the decider's argument signature")

    for identifier, ref, _, resources in schemas.primitive_games:
        at = f"primitive game '{identifier}'"
        if ref.id != identifier or not ref.source_revision:
            raise Refusal(f"{at} does not carry its own exact reference")
        names = [item.name for item in resources]
        if len(set(names)) != len(names):
            raise Refusal(f"{at} declares one resource twice")
        for item in resources:
            if item.sort not in NUMERIC_SORTS:
                raise Refusal(f"{at} declares a non-numeric resource "
                              f"'{item.name}'")

    for identifier, ref, _ in schemas.propositions:
        if ref.id != identifier or not ref.source_revision:
            raise Refusal(f"proposition '{identifier}' does not carry its own "
                          "exact reference")

    for identifier, kind, argument_types in schemas.subject_schemas:
        at = f"subject schema '{identifier}'"
        if kind == "protocol_claim":
            valid = (identifier == "zkc.subject.protocol_claim"
                     and not argument_types)
        elif kind == "consumed_claim_vector":
            valid = (identifier == "zkc.subject.consumed_claim_vector"
                     and not argument_types)
        else:
            valid = (identifier not in ("zkc.subject.protocol_claim",
                                        "zkc.subject.consumed_claim_vector")
                     and bool(argument_types))
        if not valid:
            raise Refusal(f"{at} declares a kind and arguments that disagree")

    for index in schemas.security_indices:
        needs_variant, needs_model = INDEX_SHAPE[index.notion]
        if bool(index.variant) != needs_variant:
            raise Refusal(f"the admitted index for '{index.notion}' carries "
                          "the wrong variant shape")
        if needs_model:
            if index.model != "duplex":
                raise Refusal(f"the admitted Fiat-Shamir index names model "
                              f"'{index.model}'")
        elif index.model:
            raise Refusal(f"the admitted index for '{index.notion}' names a "
                          "model")


def check_annotations(signature: Signature) -> None:
    """A rule whose statement cannot be located is one nobody can check.

    Nothing here is checked by the kernel — an annotation cannot reach
    RULE_WF, APPLY, or DERIVE, and no declaration digest picks one up. What
    freezing requires is that the record beside a declaration exists, points
    somewhere, and does not overstate what it carries.
    """
    declared = ({rule.id for rule in signature.rules}
                | {binding.id for binding in signature.bindings}
                | {identifier for identifier, *_ in signature.schemas.primitive_games}
                | {identifier for identifier, *_ in signature.schemas.propositions}
                | {identifier for identifier, *_ in signature.schemas.machine_deciders}
                | {identifier for identifier, *_ in signature.schemas.subject_schemas})
    for identifier, _ in signature.annotations:
        if identifier not in declared:
            raise Refusal(f"annotation '{identifier}' names nothing this "
                          "signature declares")

    for rule in signature.rules:
        annotation = signature.annotation(rule.id)
        if annotation is None:
            raise Refusal(f"rule '{rule.id}' carries no annotation")
        if not annotation.statement_basis:
            raise Refusal(f"rule '{rule.id}' names no source anchor")
        for anchor in annotation.statement_basis:
            if not anchor.source or not anchor.anchor:
                raise Refusal(f"rule '{rule.id}' has a source anchor without a "
                              "source or a location inside it")
        if rule.status != "admitted" and not annotation.status_rationale:
            raise Refusal(f"rule '{rule.id}' is not admitted and does not say "
                          "why")
        slots = ({item.slot for item in rule.machine_conditions}
                 | {item.slot for item in rule.external_hypotheses})
        for receipt in annotation.formalization:
            if not receipt.declaration:
                raise Refusal(f"rule '{rule.id}' has a formalization receipt "
                              "naming no declaration")
            # An empty axiom list is the claim that none are admitted, so a
            # receipt cannot record a mechanized statement while its reviewed
            # dependency closure says a hole is reachable, or the reverse.
            if (receipt.state == "mechanized") == receipt.admits_hole():
                raise Refusal(f"rule '{rule.id}' has a formalization receipt "
                              f"recorded as {receipt.state} whose axiom "
                              "profile says the opposite")
            for slot in receipt.unmatched_obligations:
                if slot not in slots:
                    raise Refusal(f"rule '{rule.id}' has a formalization "
                                  f"receipt naming '{slot}', which the rule "
                                  "does not declare")
        # The catalog stays total: a rule must say what the mechanization
        # holds for it, or that a counterpart was looked for and not found.
        if not annotation.formalization and (annotation.formalization_absence
                                             is None):
            raise Refusal(f"rule '{rule.id}' records neither a formalization "
                          "receipt nor a surveyed absence")
