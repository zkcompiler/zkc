"""Independent reference for a soundness signature.

A signature is the declaration file the compiler reads: the closed schema
tables, the rules that encode cited theorems, and the bindings that connect a
rule to sealed protocol structure.  This module reads one fail-closed, decides
rule and binding well-formedness, and writes the canonical declaration
documents together with the content addresses taken over them.

What it deliberately does not do is evaluate a bound.  A second implementation
of the same arithmetic shares a common-mode misreading with the first, so the
declared gate is the structural and typing half: this module mirrors the shape
of a declaration and the typing of its use, and the numbers are cross-checked
by re-derivation from the cited source instead.  See docs/spec/soundness.md
sections 5 and 7.1 for the normative statement of what is read here.

Every value is read into a typed Python object and the document is written back
from that object rather than copied from the input.  A field this reader does
not model therefore cannot reach a digest, which is what keeps the byte
comparison from degenerating into echoing the file back.
"""

from __future__ import annotations

from dataclasses import dataclass, replace as dataclass_replace
from fractions import Fraction
from typing import Any

from .model import Refusal, tagged_digest

RULE_DOMAIN = "zkc/soundness-rule\n"
BINDING_DOMAIN = "zkc/soundness-binding\n"
SIGNATURE_DOMAIN = "zkc/soundness-signature\n"


# --------------------------------------------------------------------------
# Closed vocabularies.  Every one of these is a tagged sum in the
# specification; spelling a set here is what makes an unknown tag a refusal
# rather than a silently ignored field.
# --------------------------------------------------------------------------

SORTS = frozenset(
    {
        "integer",
        "rational",
        "string",
        "boolean",
        "subject",
        "reduction_contract",
        "path_transition",
        "round_adjacency",
        "algebra_instance",
        "srs_instance",
        "fri_domain_instance",
    }
)

# Sorts a literal can be written at.  The remainder are carried only by a
# projection or by the kernel, so writing one as a literal would let a
# declaration assert a protocol fact it never read.
LITERAL_SORTS = frozenset(
    {"integer", "rational", "string", "boolean", "algebra_instance"}
)

NOTIONS = frozenset(
    {
        "special_soundness",
        "computational_special_soundness",
        "round_by_round",
        "state_restoration",
        "fiat_shamir",
        "completeness",
    }
)
TRACKS = frozenset({"soundness", "knowledge", "completeness"})
RESULT_SCHEMAS = frozenset({"extraction", "round", "scalar"})

# The result schema each notion requires (soundness.md section 3.3).
RESULT_OF_NOTION = {
    "special_soundness": "extraction",
    "computational_special_soundness": "extraction",
    "round_by_round": "round",
    "state_restoration": "scalar",
    "fiat_shamir": "scalar",
    "completeness": "scalar",
}

STATUSES = frozenset({"admitted", "declared"})

BODY_KINDS = frozenset(
    {
        "special_soundness_entry",
        "native_round_by_round_entry",
        "computational_entry",
        "completeness_entry",
        "special_soundness_preservation",
        "round_by_round_preservation",
        "round_scaling",
        "special_soundness_to_round_by_round",
        "round_by_round_to_state_restoration",
        "state_restoration_to_fiat_shamir_duplex",
    }
)

QUANTITY_LEAVES = frozenset(
    {
        "rational_literal",
        "parameter",
        "artifact_fact",
        "contract_round_fact",
        "premise_coordinate",
        "resource_variable",
    }
)
# Operation arity is a well-formedness question rather than a reading one: the
# grammar admits an operand list, and how long it may be is a property of the
# operator that RULE_WF decides.
QUANTITY_OPERATIONS = {
    "add": None,  # nonempty, any arity
    "sub": 2,
    "mul": None,
    "div": 2,
    "pow": 2,
    "pow2": 1,
    "pow2_up": 1,
}

BOUND_KINDS = frozenset(
    {"quantity", "scalar_bound", "primitive_advantage", "add", "scale", "max"}
)

BINDING_VALUE_KINDS = frozenset(
    {
        "literal",
        "sealed_artifact_projection",
        "conclusion_subject",
        "application_path_transition",
        "conclusion_resource",
        "resolved_parameter",
    }
)

PROJECTION_KINDS = frozenset(
    {
        "conclusion_reduction_contract",
        "contract_round_adjacency",
        "reduction_input_count",
        "reduction_parameter",
        "path_binding_field",
        "contract_round_family_field",
    }
)
AGGREGATES = frozenset({"unique_equal", "count"})

# A round selector inside a projection or a body case.
CONTRACT_ROUND_SELECTORS = frozenset(
    {"all_contract_rounds", "round_kind", "round_position"}
)

# The per-round fields a projection reads, spelled as the projection writes
# them, and the same fields as a body case reads them through its lexical
# binder.  The two spellings are not interchangeable and neither is a path.
PROJECTION_ROUND_FIELDS = frozenset(
    {
        "RoundIndex",
        "RoundKind",
        "ChallengeSpace",
        "ChallengeCount",
        "RoundDegree",
        "ChallengeSpaceLog2",
    }
)
# A case reads a quantity from the round it bound, so the two fields that name
# a round rather than measure it are not among them.
CASE_ROUND_FIELDS = frozenset(
    {
        "challenge_space",
        "challenge_count",
        "round_degree",
        "challenge_space_log2",
    }
)

LABEL_PROJECTIONS = frozenset(
    {"round_index", "round_kind_occurrence", "case_name",
     "site_qualified_round_index"})

SELECTED_ROUND_KINDS = frozenset({"by_round_index", "adjacent_predecessor_round"})

PREMISE_RESULT_CONSTRAINTS = frozenset(
    {"requires_empty_game_support", "requires_no_bound_resource_support"}
)

SUBJECT_RELATIONS = frozenset(
    {
        "same_subject",
        "consumed_claim",
        "consumed_claim_vector",
        "exact_external_subject",
    }
)
CONSUMED_SELECTORS = frozenset(
    {"reduction_input", "all_reduction_inputs", "reduction_inputs"}
)

ANCHOR_KINDS = frozenset({"reduction_contract", "path_transition"})

SUBJECT_SCHEMA_KINDS = frozenset(
    {"protocol_claim", "consumed_claim_vector", "external_instance"}
)

PREMISE_COORDINATE_FIELDS = frozenset({"arity", "challenge_space"})
# The only coordinate binder is the one `SpecialSoundnessToRoundByRound`
# introduces; no free string selector is admitted.
PREMISE_COORDINATE_SELECTORS = frozenset({"bound_coordinate"})

# `result_constraints` is a set on the carrier side, so its written order does
# not survive into the document.  This is the order it comes back in.
CONSTRAINT_ORDER = (
    "requires_empty_game_support",
    "requires_no_bound_resource_support",
)

# The exact index signature of each body: how many premises it takes, the
# notion each premise must carry, and the notion it concludes.  This table is
# stronger than result-schema compatibility, which is the point: sharing a
# scalar result does not make FS to SR a legal step.
BODY_SIGNATURES = {
    "special_soundness_entry": ((), "special_soundness"),
    "native_round_by_round_entry": ((), "round_by_round"),
    "computational_entry": ((), "computational_special_soundness"),
    "completeness_entry": ((), "completeness"),
    "special_soundness_preservation": (
        ("special_soundness",),
        "computational_special_soundness",
    ),
    "round_by_round_preservation": (("round_by_round",), "round_by_round"),
    "round_scaling": (("round_by_round",), "round_by_round"),
    "special_soundness_to_round_by_round": (
        ("special_soundness",),
        "round_by_round",
    ),
    "round_by_round_to_state_restoration": (
        ("round_by_round",),
        "state_restoration",
    ),
    "state_restoration_to_fiat_shamir_duplex": (
        ("state_restoration",),
        "fiat_shamir",
    ),
}

# The port field each body reads its premise through.
BODY_PREMISE_FIELD = {
    "special_soundness_preservation": "source_port",
    "round_by_round_preservation": "source_port",
    "round_scaling": "round_by_round_port",
    "special_soundness_to_round_by_round": "special_soundness_port",
    "round_by_round_to_state_restoration": "round_by_round_port",
    "state_restoration_to_fiat_shamir_duplex": "state_restoration_port",
}


# --------------------------------------------------------------------------
# Fail-closed reading.  Every object has a closed field set; an unknown field
# at any depth refuses rather than being ignored, because a field nobody reads
# is a field an author believed was doing something.
# --------------------------------------------------------------------------


def _object(node: Any, where: str, required: tuple[str, ...],
            optional: tuple[str, ...] = ()) -> dict[str, Any]:
    if not isinstance(node, dict):
        raise Refusal(f"{where} is not an object")
    allowed = set(required) | set(optional)
    for key in sorted(node):
        if key not in allowed:
            raise Refusal(f"{where} carries an unknown field {key!r}")
    for key in required:
        if key not in node:
            raise Refusal(f"{where} is missing {key!r}")
    return node


def _string(node: dict[str, Any], key: str, where: str) -> str:
    """A declared name, held to the encoding domain.

    Strings that reach a canonical encoding are printable ASCII, so a name
    outside it cannot be digested faithfully and refuses rather than being
    escaped into one (docs/spec/kernel.md section 3.4).
    """
    value = node[key]
    if not isinstance(value, str) or not value:
        raise Refusal(f"{where} needs a nonempty string {key!r}")
    if any(not 0x20 <= ord(character) <= 0x7E for character in value):
        raise Refusal(f"{where} has a {key!r} outside printable ASCII")
    return value


def _list(node: dict[str, Any], key: str, where: str) -> list[Any]:
    value = node[key]
    if not isinstance(value, list):
        raise Refusal(f"{where} needs a list {key!r}")
    return value


def _mapping(node: dict[str, Any], key: str, where: str) -> dict[str, Any]:
    value = node[key]
    if not isinstance(value, dict):
        raise Refusal(f"{where} needs an object {key!r}")
    return value


def _tag(node: Any, where: str, admitted: frozenset[str]) -> str:
    if not isinstance(node, dict):
        raise Refusal(f"{where} is not an object")
    kind = node.get("kind")
    if not isinstance(kind, str):
        raise Refusal(f"{where} has no 'kind'")
    if kind not in admitted:
        raise Refusal(f"{where} names an unadmitted kind {kind!r}")
    return kind


def _member(value: Any, admitted: frozenset[str], where: str) -> str:
    if not isinstance(value, str) or value not in admitted:
        raise Refusal(f"{where} is not one of the admitted values: {value!r}")
    return value


def _sort(node: dict[str, Any], key: str, where: str) -> str:
    return _member(node.get(key), SORTS, f"{where} {key}")


def _rational(text: Any, where: str) -> Fraction:
    """Read an exact decimal rational, written 'n' or 'n/d'.

    The spelling is exact on purpose: a decimal point or a leading zero is an
    author writing an approximation, and an approximate probability that
    reads as exact is the failure this whole grammar exists to prevent.
    """
    if not isinstance(text, str):
        raise Refusal(f"{where} is not a decimal rational string")
    numerator, slash, denominator = text.partition("/")
    value = _decimal_integer(numerator, where)
    if slash:
        divisor = _decimal_integer(denominator, where)
        if divisor == 0:
            raise Refusal(f"{where} has a zero denominator")
        return Fraction(value, divisor)
    return Fraction(value)


def _domain_integer(value: Any, where: str, what: str) -> int:
    """A JSON integer, held to the encoding domain.

    An integer is signed-64-bit representable and a float is unrepresentable
    (docs/spec/kernel.md section 3.4), so a whole-valued float is a second
    spelling of a value that has exactly one, and a value outside the range
    names something no artifact can carry.
    """
    if isinstance(value, bool) or not isinstance(value, int):
        raise Refusal(f"{where} needs an exact integer {what}")
    if not -(2 ** 63) <= value < 2 ** 63:
        raise Refusal(f"{where} has a {what} outside the encoding domain")
    return value


def _decimal_integer(text: str, where: str) -> int:
    digits = text[1:] if text.startswith("-") else text
    if not digits or not digits.isdigit() or not digits.isascii():
        raise Refusal(f"{where} is not a decimal integer: {text!r}")
    if len(digits) > 1 and digits[0] == "0":
        raise Refusal(f"{where} carries a leading zero: {text!r}")
    return -int(digits) if text.startswith("-") else int(digits)


def _rational_text(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else str(value)


def _unique(names: list[str], where: str) -> tuple[str, ...]:
    seen: set[str] = set()
    for name in names:
        if name in seen:
            raise Refusal(f"{where} declares {name!r} twice")
        seen.add(name)
    return tuple(names)


# --------------------------------------------------------------------------
# Typed declarations, indices, and values.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ExactRef:
    id: str
    source_revision: str

    def document(self) -> dict[str, Any]:
        return {"id": self.id, "source_revision": self.source_revision}


@dataclass(frozen=True)
class TypedName:
    """One declared parameter or resource variable."""

    name: str
    sort: str

    def document(self) -> dict[str, Any]:
        return {"name": self.name, "sort": self.sort}


@dataclass(frozen=True)
class SecurityIndex:
    notion: str
    track: str
    variant: str
    model: str

    def document(self) -> dict[str, Any]:
        return {
            "model": self.model,
            "notion": self.notion,
            "track": self.track,
            "variant": self.variant,
        }


def _read_exact_ref(node: Any, where: str) -> ExactRef:
    entry = _object(node, where, ("id", "source_revision"))
    return ExactRef(_string(entry, "id", where),
                    _string(entry, "source_revision", where))


def _read_typed_names(node: Any, where: str) -> tuple[TypedName, ...]:
    if not isinstance(node, list):
        raise Refusal(f"{where} is not a list")
    declarations = []
    for position, item in enumerate(node):
        at = f"{where}[{position}]"
        entry = _object(item, at, ("name", "sort"))
        declarations.append(TypedName(_string(entry, "name", at),
                                      _sort(entry, "sort", at)))
    _unique([item.name for item in declarations], where)
    return tuple(declarations)


def _read_security_index(node: Any, where: str) -> SecurityIndex:
    entry = _object(node, where, ("notion", "track", "variant", "model"))
    notion = _member(entry["notion"], NOTIONS, f"{where} notion")
    track = _member(entry["track"], TRACKS, f"{where} track")
    # The completeness notion and track come together or not at all: a
    # completeness judgment must not read as a soundness or knowledge claim,
    # and no soundness notion may borrow the spelling (soundness.md
    # section 3.2).
    if (notion == "completeness") != (track == "completeness"):
        raise Refusal(f"{where} mixes the completeness notion and track")
    for key in ("variant", "model"):
        value = entry[key]
        if not isinstance(value, str):
            raise Refusal(f"{where} {key} is not a string")
        if any(not 0x20 <= ord(character) <= 0x7E for character in value):
            raise Refusal(f"{where} {key} leaves printable ASCII")
    return SecurityIndex(notion, track, entry["variant"], entry["model"])


# --------------------------------------------------------------------------
# Quantity templates.  Five shapes cover the grammar: a literal, a name in one
# of three namespaces, the lexically bound contract round, a premise
# coordinate, and an operation over sub-quantities.
# --------------------------------------------------------------------------


class Quantity:
    """Base for the quantity template variants."""

    def document(self) -> dict[str, Any]:  # pragma: no cover - abstract
        raise NotImplementedError


@dataclass(frozen=True)
class RationalLiteral(Quantity):
    value: Fraction

    def document(self) -> dict[str, Any]:
        return {"kind": "rational_literal", "literal": _rational_text(self.value)}


@dataclass(frozen=True)
class NamedQuantity(Quantity):
    """A parameter, a resource variable, or an artifact fact port."""

    kind: str
    name: str

    def document(self) -> dict[str, Any]:
        return {"kind": self.kind, "name": self.name}


@dataclass(frozen=True)
class ContractRoundFact(Quantity):
    case_name: str
    field: str

    def document(self) -> dict[str, Any]:
        return {
            "case_name": self.case_name,
            "field": self.field,
            "kind": "contract_round_fact",
        }


@dataclass(frozen=True)
class PremiseCoordinate(Quantity):
    port: str
    field: str
    selector: str

    def document(self) -> dict[str, Any]:
        return {
            "field": self.field,
            "kind": "premise_coordinate",
            "port": self.port,
            "selector": {"kind": self.selector},
        }


@dataclass(frozen=True)
class QuantityOperation(Quantity):
    kind: str
    operands: tuple[Quantity, ...]

    def document(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "operands": [operand.document() for operand in self.operands],
        }


def _read_quantity(node: Any, where: str) -> Quantity:
    admitted = QUANTITY_LEAVES | frozenset(QUANTITY_OPERATIONS)
    kind = _tag(node, where, admitted)
    if kind == "rational_literal":
        entry = _object(node, where, ("kind", "literal"))
        return RationalLiteral(_rational(entry["literal"], f"{where} literal"))
    if kind in ("parameter", "resource_variable", "artifact_fact"):
        entry = _object(node, where, ("kind", "name"))
        return NamedQuantity(kind, _string(entry, "name", where))
    if kind == "contract_round_fact":
        entry = _object(node, where, ("kind", "case_name", "field"))
        return ContractRoundFact(
            _string(entry, "case_name", where),
            _member(entry["field"], CASE_ROUND_FIELDS, f"{where} field"),
        )
    if kind == "premise_coordinate":
        entry = _object(node, where, ("kind", "port", "field", "selector"))
        selector = _tag(entry["selector"], f"{where} selector",
                        PREMISE_COORDINATE_SELECTORS)
        _object(entry["selector"], f"{where} selector", ("kind",))
        return PremiseCoordinate(
            _string(entry, "port", where),
            _member(entry["field"], PREMISE_COORDINATE_FIELDS, f"{where} field"),
            selector,
        )
    entry = _object(node, where, ("kind", "operands"))
    operands = _list(entry, "operands", where)
    return QuantityOperation(
        kind,
        tuple(_read_quantity(operand, f"{where}.{kind}[{position}]")
              for position, operand in enumerate(operands)),
    )


# --------------------------------------------------------------------------
# Rule bounds.  A bound is monotone in its premise: subtraction, division and
# powers live inside a quantity coefficient and never around a premise bound
# or a primitive advantage.
# --------------------------------------------------------------------------


class Bound:
    def document(self) -> dict[str, Any]:  # pragma: no cover - abstract
        raise NotImplementedError


@dataclass(frozen=True)
class QuantityBound(Bound):
    quantity: Quantity

    def document(self) -> dict[str, Any]:
        return {"kind": "quantity", "quantity": self.quantity.document()}


@dataclass(frozen=True)
class ScalarBound(Bound):
    premise_port: str

    def document(self) -> dict[str, Any]:
        return {"kind": "scalar_bound", "premise_port": self.premise_port}


@dataclass(frozen=True)
class GameInstance:
    ref: str
    instance_arguments: tuple["BindingValue", ...]

    def document(self) -> dict[str, Any]:
        return {
            "instance_arguments": [
                argument.document() for argument in self.instance_arguments
            ],
            "ref": self.ref,
        }


@dataclass(frozen=True)
class PrimitiveAdvantage(Bound):
    game: GameInstance
    resource_substitution: tuple[tuple[str, Quantity], ...]

    def document(self) -> dict[str, Any]:
        return {
            "game": self.game.document(),
            "kind": "primitive_advantage",
            "resource_substitution": {
                name: quantity.document()
                for name, quantity in self.resource_substitution
            },
        }


@dataclass(frozen=True)
class BoundOperation(Bound):
    """`add` over bounds, or `max` over bounds."""

    kind: str
    operands: tuple[Bound, ...]

    def document(self) -> dict[str, Any]:
        return {
            "kind": self.kind,
            "operands": [operand.document() for operand in self.operands],
        }


@dataclass(frozen=True)
class ScaledBound(Bound):
    """A coefficient times a bound.  The operand list is how the grammar
    spells it; that exactly one operand is admitted is a well-formedness
    question, not a reading one."""

    scale: Quantity
    operands: tuple[Bound, ...]

    def document(self) -> dict[str, Any]:
        return {
            "kind": "scale",
            "operands": [operand.document() for operand in self.operands],
            "scale": self.scale.document(),
        }


def _read_resource_substitution(node: Any, where: str
                                ) -> tuple[tuple[str, Quantity], ...]:
    if not isinstance(node, dict):
        raise Refusal(f"{where} is not an object")
    return tuple(
        (name, _read_quantity(node[name], f"{where}.{name}"))
        for name in sorted(node)
    )


def _read_game_instance(node: Any, where: str) -> GameInstance:
    entry = _object(node, where, ("ref", "instance_arguments"))
    arguments = _list(entry, "instance_arguments", where)
    return GameInstance(
        _string(entry, "ref", where),
        tuple(
            _read_binding_value(argument, f"{where} argument {position}")
            for position, argument in enumerate(arguments)
        ),
    )


def _read_bound(node: Any, where: str) -> Bound:
    kind = _tag(node, where, BOUND_KINDS)
    if kind == "quantity":
        entry = _object(node, where, ("kind", "quantity"))
        return QuantityBound(_read_quantity(entry["quantity"], f"{where} quantity"))
    if kind == "scalar_bound":
        entry = _object(node, where, ("kind", "premise_port"))
        return ScalarBound(_string(entry, "premise_port", where))
    if kind == "primitive_advantage":
        entry = _object(node, where, ("kind", "game", "resource_substitution"))
        return PrimitiveAdvantage(
            _read_game_instance(entry["game"], f"{where} game"),
            _read_resource_substitution(entry["resource_substitution"],
                                        f"{where} resource substitution"),
        )
    if kind == "scale":
        entry = _object(node, where, ("kind", "scale", "operands"))
        return ScaledBound(
            _read_quantity(entry["scale"], f"{where} scale"),
            tuple(_read_bound(operand, f"{where} scaled[{position}]")
                  for position, operand in enumerate(
                      _list(entry, "operands", where))),
        )
    entry = _object(node, where, ("kind", "operands"))
    operands = _list(entry, "operands", where)
    return BoundOperation(
        kind,
        tuple(_read_bound(operand, f"{where}.{kind}[{position}]")
              for position, operand in enumerate(operands)),
    )


# --------------------------------------------------------------------------
# Binding values and artifact projections.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class AlgebraInstance:
    group: str
    field_class: str
    field_order: Fraction

    def document(self) -> dict[str, Any]:
        return {
            "field_class": self.field_class,
            "field_order": _rational_text(self.field_order),
            "group": self.group,
        }


@dataclass(frozen=True)
class ArtifactProjection:
    kind: str
    result_sort: str
    field: str | None = None
    round_selector: tuple[str, str | int | None] | None = None
    aggregate: str | None = None

    def document(self) -> dict[str, Any]:
        document: dict[str, Any] = {"kind": self.kind,
                                    "result_sort": self.result_sort}
        if self.field is not None:
            document["field"] = self.field
        if self.round_selector is not None:
            kind, payload = self.round_selector
            selector: dict[str, Any] = {"kind": kind}
            if kind == "round_kind":
                selector["round_kind"] = payload
            elif kind == "round_position":
                selector["position"] = payload
            document["round_selector"] = selector
        if self.aggregate is not None:
            document["aggregate"] = self.aggregate
        return document


@dataclass(frozen=True)
class BindingValue:
    kind: str
    sort: str
    literal: Fraction | str | bool | AlgebraInstance | None = None
    reference: str | None = None
    artifact_projection: ArtifactProjection | None = None

    def document(self) -> dict[str, Any]:
        document: dict[str, Any] = {"kind": self.kind, "sort": self.sort}
        if self.kind == "literal":
            if isinstance(self.literal, AlgebraInstance):
                document["literal"] = self.literal.document()
            elif isinstance(self.literal, Fraction):
                document["literal"] = _rational_text(self.literal)
            else:
                document["literal"] = self.literal
        elif self.kind == "sealed_artifact_projection":
            projection = self.artifact_projection
            if projection is None:
                raise Refusal("a projection value carries no projection")
            document["artifact_projection"] = projection.document()
        elif self.kind in ("conclusion_resource", "resolved_parameter"):
            document["reference"] = self.reference
        return document


def _read_round_selector(node: Any, where: str) -> tuple[str, str | int | None]:
    kind = _tag(node, where, CONTRACT_ROUND_SELECTORS)
    if kind == "all_contract_rounds":
        _object(node, where, ("kind",))
        return (kind, None)
    if kind == "round_kind":
        entry = _object(node, where, ("kind", "round_kind"))
        return (kind, _string(entry, "round_kind", where))
    entry = _object(node, where, ("kind", "position"))
    position = _domain_integer(entry["position"], where, "round position")
    if position < 0:
        raise Refusal(f"{where} needs a non-negative round position")
    return (kind, position)


def _read_artifact_projection(node: Any, where: str) -> ArtifactProjection:
    kind = _tag(node, where, PROJECTION_KINDS)
    if kind in ("conclusion_reduction_contract", "contract_round_adjacency",
                "reduction_input_count"):
        entry = _object(node, where, ("kind", "result_sort"))
        return ArtifactProjection(kind, _sort(entry, "result_sort", where))
    if kind in ("reduction_parameter", "path_binding_field"):
        entry = _object(node, where, ("kind", "result_sort", "field"))
        return ArtifactProjection(kind, _sort(entry, "result_sort", where),
                                  field=_string(entry, "field", where))
    entry = _object(node, where,
                    ("kind", "result_sort", "field", "round_selector",
                     "aggregate"))
    return ArtifactProjection(
        kind,
        _sort(entry, "result_sort", where),
        field=_member(entry["field"], PROJECTION_ROUND_FIELDS, f"{where} field"),
        round_selector=_read_round_selector(entry["round_selector"],
                                            f"{where} round selector"),
        aggregate=_member(entry["aggregate"], AGGREGATES, f"{where} aggregate"),
    )


def _read_binding_value(node: Any, where: str) -> BindingValue:
    kind = _tag(node, where, BINDING_VALUE_KINDS)
    sort = _sort(_object(node, where, ("kind", "sort"),
                         ("literal", "reference", "artifact_projection")),
                 "sort", where)
    if kind == "literal":
        entry = _object(node, where, ("kind", "sort", "literal"))
        if sort not in LITERAL_SORTS:
            raise Refusal(f"{where} has no literal constructor for sort {sort!r}")
        return BindingValue(kind, sort,
                            literal=_read_literal(entry["literal"], sort, where))
    if kind == "sealed_artifact_projection":
        entry = _object(node, where, ("kind", "sort", "artifact_projection"))
        return BindingValue(
            kind, sort,
            artifact_projection=_read_artifact_projection(
                entry["artifact_projection"], f"{where} projection"),
        )
    if kind in ("conclusion_resource", "resolved_parameter"):
        entry = _object(node, where, ("kind", "sort", "reference"))
        return BindingValue(kind, sort,
                            reference=_string(entry, "reference", where))
    _object(node, where, ("kind", "sort"))
    return BindingValue(kind, sort)


def _read_literal(value: Any, sort: str, where: str
                  ) -> Fraction | str | bool | AlgebraInstance:
    if sort in ("integer", "rational"):
        return _rational(value, f"{where} literal")
    if sort == "string":
        if not isinstance(value, str):
            raise Refusal(f"{where} needs a string literal")
        # A literal reaches the declaration digest like any other string, and
        # the encoding domain is printable ASCII. Emptiness is admitted here
        # and nowhere else: a literal empty string is a value.
        if any(not 0x20 <= ord(character) <= 0x7E for character in value):
            raise Refusal(f"{where} has a literal outside printable ASCII")
        return value
    if sort == "boolean":
        if not isinstance(value, bool):
            raise Refusal(f"{where} needs a boolean literal")
        return value
    entry = _object(value, f"{where} literal",
                    ("group", "field_class", "field_order"))
    return AlgebraInstance(
        _string(entry, "group", where),
        _string(entry, "field_class", where),
        _rational(entry["field_order"], f"{where} field order"),
    )


# --------------------------------------------------------------------------
# Sequence templates: the coordinates of an extraction result and the rounds
# of a round-by-round result, either written out or resolved against the
# authenticated contract.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class CoordinateTemplate:
    label: str
    arity: Quantity
    challenge_space: Quantity | None

    def document(self) -> dict[str, Any]:
        return {
            "arity": self.arity.document(),
            "challenge_space": (None if self.challenge_space is None
                                else self.challenge_space.document()),
            "label": self.label,
        }


@dataclass(frozen=True)
class RoundTemplate:
    round_index: str
    challenge_space: Quantity
    bound: Bound

    def document(self) -> dict[str, Any]:
        return {
            "bound": self.bound.document(),
            "challenge_space": self.challenge_space.document(),
            "round_index": self.round_index,
        }


@dataclass(frozen=True)
class ContractCase:
    """One case of a contract-derived sequence.

    The case lexically binds the contract round it matched; the projection
    that names the output entry and the quantity templates read only that
    round.  `bound` is present for a round case and absent for a coordinate
    case, which instead carries `arity`.
    """

    case_name: str
    selector: tuple[str, str | int | None]
    projection: str
    challenge_space: Quantity
    arity: Quantity | None = None
    bound: Bound | None = None

    def document(self) -> dict[str, Any]:
        document: dict[str, Any] = {
            "case_name": self.case_name,
            "challenge_space": self.challenge_space.document(),
        }
        kind, payload = self.selector
        selector: dict[str, Any] = {"kind": kind}
        if kind == "round_kind":
            selector["round_kind"] = payload
        elif kind == "round_position":
            selector["position"] = payload
        document["selector"] = selector
        if self.arity is not None:
            document["arity"] = self.arity.document()
            document["label_projection"] = self.projection
        elif self.bound is not None:
            document["bound"] = self.bound.document()
            document["index_projection"] = self.projection
        else:
            raise Refusal(f"contract case '{self.case_name}' is neither a "
                          "coordinate nor a round")
        return document


@dataclass(frozen=True)
class Sequence:
    """Either an explicit list of entries or a contract-resolved case list."""

    kind: str
    entries: tuple[Any, ...] = ()
    contract_fact_port: str | None = None
    cases: tuple[ContractCase, ...] = ()
    entry_key: str = "coordinates"

    def document(self) -> dict[str, Any]:
        if self.kind == "explicit":
            return {
                "kind": "explicit",
                self.entry_key: [entry.document() for entry in self.entries],
            }
        return {
            "cases": [case.document() for case in self.cases],
            "contract_fact_port": self.contract_fact_port,
            "kind": "contract",
        }


def _read_coordinate_sequence(node: Any, where: str) -> Sequence:
    kind = _tag(node, where, frozenset({"explicit", "contract"}))
    if kind == "explicit":
        entry = _object(node, where, ("kind", "coordinates"))
        items = _list(entry, "coordinates", where)
        if not items:
            raise Refusal(f"{where} lists no coordinates")
        coordinates = []
        for position, item in enumerate(items):
            at = f"{where} coordinate {position}"
            fields = _object(item, at, ("label", "arity", "challenge_space"))
            space = fields["challenge_space"]
            coordinates.append(CoordinateTemplate(
                _string(fields, "label", at),
                _read_quantity(fields["arity"], f"{at} arity"),
                None if space is None else _read_quantity(space, f"{at} space"),
            ))
        _unique([item.label for item in coordinates], where)
        return Sequence("explicit", entries=tuple(coordinates),
                        entry_key="coordinates")
    return _read_contract_sequence(node, where, coordinate=True,
                                   entry_key="coordinates")


def _read_round_sequence(node: Any, where: str) -> Sequence:
    kind = _tag(node, where, frozenset({"explicit", "contract"}))
    if kind == "explicit":
        entry = _object(node, where, ("kind", "rounds"))
        items = _list(entry, "rounds", where)
        if not items:
            raise Refusal(f"{where} lists no rounds")
        rounds = []
        for position, item in enumerate(items):
            at = f"{where} round {position}"
            fields = _object(item, at, ("round_index", "challenge_space", "bound"))
            rounds.append(RoundTemplate(
                _string(fields, "round_index", at),
                _read_quantity(fields["challenge_space"], f"{at} space"),
                _read_bound(fields["bound"], f"{at} bound"),
            ))
        _unique([item.round_index for item in rounds], where)
        return Sequence("explicit", entries=tuple(rounds), entry_key="rounds")
    return _read_contract_sequence(node, where, coordinate=False,
                                   entry_key="rounds")


def _read_contract_sequence(node: Any, where: str, *, coordinate: bool,
                            entry_key: str) -> Sequence:
    entry = _object(node, where, ("kind", "contract_fact_port", "cases"))
    items = _list(entry, "cases", where)
    if not items:
        raise Refusal(f"{where} lists no cases")
    projection_key = "label_projection" if coordinate else "index_projection"
    value_key = "arity" if coordinate else "bound"
    cases = []
    for position, item in enumerate(items):
        at = f"{where} case {position}"
        fields = _object(item, at,
                         ("case_name", "selector", projection_key,
                          "challenge_space", value_key))
        selector = _read_round_selector(fields["selector"], f"{at} selector")
        case = ContractCase(
            case_name=_string(fields, "case_name", at),
            selector=selector,
            projection=_member(fields[projection_key], LABEL_PROJECTIONS,
                               f"{at} {projection_key}"),
            challenge_space=_read_quantity(fields["challenge_space"],
                                           f"{at} challenge space"),
            arity=(_read_quantity(fields["arity"], f"{at} arity")
                   if coordinate else None),
            bound=(None if coordinate
                   else _read_bound(fields["bound"], f"{at} bound")),
        )
        cases.append(case)
    _unique([case.case_name for case in cases], where)
    _check_case_law(cases, where)
    return Sequence("contract",
                    contract_fact_port=_string(entry, "contract_fact_port", where),
                    cases=tuple(cases), entry_key=entry_key)


def _check_case_law(cases: list[ContractCase], where: str) -> None:
    """The part of the matching law that is decidable without a contract.

    Whether every round matches exactly one case, and every case at least one
    round, needs the sealed contract and is decided at application.  What a
    declaration alone settles is that a catch-all is not sharing the list with
    a case it would swallow, and that no two cases select the same rounds.
    """
    kinds = [case.selector[0] for case in cases]
    if "all_contract_rounds" in kinds and len(cases) > 1:
        raise Refusal(f"{where} pairs a catch-all case with another case")
    seen: set[tuple[str, Any]] = set()
    for case in cases:
        if case.selector in seen:
            raise Refusal(f"{where} selects the same rounds twice")
        seen.add(case.selector)


# --------------------------------------------------------------------------
# Rule bodies.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class RuleBody:
    kind: str
    fields: tuple[tuple[str, Any], ...]

    def get(self, name: str) -> Any:
        for key, value in self.fields:
            if key == name:
                return value
        return None

    def document(self) -> dict[str, Any]:
        document: dict[str, Any] = {"kind": self.kind}
        for key, value in self.fields:
            document[key] = value.document() if hasattr(value, "document") else value
        return document


def _read_body(node: Any, where: str) -> RuleBody:
    kind = _tag(node, where, BODY_KINDS)
    if kind == "special_soundness_entry":
        entry = _object(node, where, ("kind", "coordinates"))
        return RuleBody(kind, (
            ("coordinates",
             _read_coordinate_sequence(entry["coordinates"], f"{where} coordinates")),
        ))
    if kind == "native_round_by_round_entry":
        entry = _object(node, where, ("kind", "rounds"))
        return RuleBody(kind, (
            ("rounds", _read_round_sequence(entry["rounds"], f"{where} rounds")),
        ))
    if kind == "computational_entry":
        entry = _object(node, where, ("kind", "coordinates", "failure_bound"))
        return RuleBody(kind, (
            ("coordinates",
             _read_coordinate_sequence(entry["coordinates"], f"{where} coordinates")),
            ("failure_bound",
             _read_bound(entry["failure_bound"], f"{where} failure bound")),
        ))
    if kind == "completeness_entry":
        entry = _object(node, where, ("kind", "bound"))
        return RuleBody(kind, (
            ("bound", _read_bound(entry["bound"], f"{where} bound")),
        ))
    if kind == "special_soundness_preservation":
        entry = _object(node, where, ("kind", "source_port",
                                      "appended_coordinates",
                                      "conclusion_failure_bound"))
        return RuleBody(kind, (
            ("appended_coordinates",
             _read_coordinate_sequence(entry["appended_coordinates"],
                                       f"{where} appended coordinates")),
            ("conclusion_failure_bound",
             _read_bound(entry["conclusion_failure_bound"],
                         f"{where} conclusion failure bound")),
            ("source_port", _string(entry, "source_port", where)),
        ))
    if kind == "round_by_round_preservation":
        entry = _object(node, where, ("kind", "source_port", "appended_rounds"))
        return RuleBody(kind, (
            ("appended_rounds",
             _read_round_sequence(entry["appended_rounds"],
                                  f"{where} appended rounds")),
            ("source_port", _string(entry, "source_port", where)),
        ))
    if kind == "round_scaling":
        entry = _object(node, where, ("kind", "round_by_round_port",
                                      "selected_round", "scale"))
        return RuleBody(kind, (
            ("round_by_round_port", _string(entry, "round_by_round_port", where)),
            ("scale", _read_quantity(entry["scale"], f"{where} scale")),
            ("selected_round",
             _read_selected_round(entry["selected_round"],
                                  f"{where} selected round")),
        ))
    if kind == "special_soundness_to_round_by_round":
        entry = _object(node, where, ("kind", "special_soundness_port",
                                      "per_coordinate_bound"))
        return RuleBody(kind, (
            ("per_coordinate_bound",
             _read_bound(entry["per_coordinate_bound"],
                         f"{where} per coordinate bound")),
            ("special_soundness_port",
             _string(entry, "special_soundness_port", where)),
        ))
    if kind == "round_by_round_to_state_restoration":
        entry = _object(node, where, ("kind", "round_by_round_port",
                                      "move_budget"))
        return RuleBody(kind, (
            ("move_budget",
             _read_quantity(entry["move_budget"], f"{where} move budget")),
            ("round_by_round_port", _string(entry, "round_by_round_port", where)),
        ))
    entry = _object(node, where, ("kind", "state_restoration_port",
                                 "local_duplex_bound"))
    return RuleBody(kind, (
        ("local_duplex_bound",
         _read_bound(entry["local_duplex_bound"], f"{where} local duplex bound")),
        ("state_restoration_port", _string(entry, "state_restoration_port", where)),
    ))


@dataclass(frozen=True)
class SelectedRound:
    kind: str
    round_index: str | None = None
    adjacency_fact_port: str | None = None

    def document(self) -> dict[str, Any]:
        if self.kind == "by_round_index":
            return {"kind": self.kind, "round_index": self.round_index}
        return {"adjacency_fact_port": self.adjacency_fact_port,
                "kind": self.kind}


def _read_selected_round(node: Any, where: str) -> SelectedRound:
    kind = _tag(node, where, SELECTED_ROUND_KINDS)
    if kind == "by_round_index":
        entry = _object(node, where, ("kind", "round_index"))
        return SelectedRound(kind, round_index=_string(entry, "round_index", where))
    entry = _object(node, where, ("kind", "adjacency_fact_port"))
    return SelectedRound(
        kind, adjacency_fact_port=_string(entry, "adjacency_fact_port", where))


# --------------------------------------------------------------------------
# Premise ports, condition and hypothesis templates, pins, and the rule.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class PremisePort:
    name: str
    expected_subject_schema: str
    expected_index: SecurityIndex
    expected_result: str
    expected_resources: tuple[TypedName, ...]
    result_constraints: tuple[str, ...]
    resource_substitution: tuple[tuple[str, Quantity], ...]

    def document(self) -> dict[str, Any]:
        return {
            "expected_index": self.expected_index.document(),
            "expected_resources": [item.document()
                                   for item in self.expected_resources],
            "expected_result": self.expected_result,
            "expected_subject_schema": self.expected_subject_schema,
            "name": self.name,
            "resource_substitution": {
                name: quantity.document()
                for name, quantity in self.resource_substitution
            },
            "result_constraints": list(self.result_constraints),
        }


@dataclass(frozen=True)
class SlotTemplate:
    """A machine condition or an external hypothesis: a fixed identity and a
    fixed ordered signature that a binding may fill but not change."""

    slot: str
    ref: str
    argument_types: tuple[str, ...]
    ref_key: str

    def document(self) -> dict[str, Any]:
        return {
            "argument_types": list(self.argument_types),
            self.ref_key: self.ref,
            "slot": self.slot,
        }


@dataclass(frozen=True)
class ParameterPin:
    parameter: str
    expected: BindingValue

    def document(self) -> dict[str, Any]:
        return {"expected": self.expected.document(), "parameter": self.parameter}


@dataclass(frozen=True)
class Rule:
    id: str
    status: str
    parameters: tuple[TypedName, ...]
    resources: tuple[TypedName, ...]
    premises: tuple[PremisePort, ...]
    artifact_facts: tuple[TypedName, ...]
    machine_conditions: tuple[SlotTemplate, ...]
    external_hypotheses: tuple[SlotTemplate, ...]
    exact_parameter_pins: tuple[ParameterPin, ...]
    conclusion_index: SecurityIndex
    body: RuleBody

    def document(self) -> dict[str, Any]:
        return {
            "artifact_facts": [item.document() for item in self.artifact_facts],
            "body": self.body.document(),
            "conclusion_index": self.conclusion_index.document(),
            "exact_parameter_pins": [item.document()
                                     for item in self.exact_parameter_pins],
            "external_hypotheses": [item.document()
                                    for item in self.external_hypotheses],
            "id": self.id,
            "machine_conditions": [item.document()
                                   for item in self.machine_conditions],
            "parameters": [item.document() for item in self.parameters],
            "premises": [item.document() for item in self.premises],
            "resources": [item.document() for item in self.resources],
            "status": self.status,
        }

    def revision(self) -> str:
        return tagged_digest(RULE_DOMAIN, self.document())


def _read_premise(node: Any, where: str) -> PremisePort:
    entry = _object(node, where,
                    ("name", "expected_subject_schema", "expected_index",
                     "expected_result", "expected_resources",
                     "result_constraints", "resource_substitution"))
    declared = set()
    for constraint in _list(entry, "result_constraints", where):
        declared.add(_member(constraint, PREMISE_RESULT_CONSTRAINTS,
                             f"{where} constraint"))
    constraints = tuple(name for name in CONSTRAINT_ORDER if name in declared)
    return PremisePort(
        name=_string(entry, "name", where),
        expected_subject_schema=_string(entry, "expected_subject_schema", where),
        expected_index=_read_security_index(entry["expected_index"],
                                            f"{where} expected index"),
        expected_result=_member(entry["expected_result"], RESULT_SCHEMAS,
                                f"{where} expected result"),
        expected_resources=_read_typed_names(entry["expected_resources"],
                                             f"{where} expected resources"),
        result_constraints=constraints,
        resource_substitution=_read_resource_substitution(
            entry["resource_substitution"], f"{where} resource substitution"),
    )


def _read_slots(node: Any, where: str, ref_key: str) -> tuple[SlotTemplate, ...]:
    if not isinstance(node, list):
        raise Refusal(f"{where} is not a list")
    slots = []
    for position, item in enumerate(node):
        at = f"{where}[{position}]"
        entry = _object(item, at, ("slot", ref_key, "argument_types"))
        types = _list(entry, "argument_types", at)
        slots.append(SlotTemplate(
            _string(entry, "slot", at),
            _string(entry, ref_key, at),
            tuple(_member(item, SORTS, f"{at} argument type") for item in types),
            ref_key,
        ))
    _unique([slot.slot for slot in slots], where)
    return tuple(slots)


def _read_rule(identifier: str, node: Any) -> Rule:
    where = f"rule '{identifier}'"
    entry = _object(node, where,
                    ("id", "status", "parameters", "resources", "premises",
                     "artifact_facts", "machine_conditions",
                     "external_hypotheses", "exact_parameter_pins",
                     "conclusion_index", "body"))
    if _string(entry, "id", where) != identifier:
        raise Refusal(f"{where} is filed under a different identifier")
    premises = tuple(
        _read_premise(item, f"{where} premise {position}")
        for position, item in enumerate(_list(entry, "premises", where))
    )
    _unique([premise.name for premise in premises], f"{where} premises")
    pins = []
    for position, item in enumerate(_list(entry, "exact_parameter_pins", where)):
        at = f"{where} pin {position}"
        fields = _object(item, at, ("parameter", "expected"))
        pins.append(ParameterPin(
            _string(fields, "parameter", at),
            _read_binding_value(fields["expected"], f"{at} expected"),
        ))
    _unique([pin.parameter for pin in pins], f"{where} pins")
    return Rule(
        id=identifier,
        status=_member(entry["status"], STATUSES, f"{where} status"),
        parameters=_read_typed_names(entry["parameters"], f"{where} parameters"),
        resources=_read_typed_names(entry["resources"], f"{where} resources"),
        premises=premises,
        artifact_facts=_read_typed_names(entry["artifact_facts"],
                                         f"{where} artifact facts"),
        machine_conditions=_read_slots(entry["machine_conditions"],
                                       f"{where} machine conditions",
                                       "predicate_ref"),
        external_hypotheses=_read_slots(entry["external_hypotheses"],
                                        f"{where} external hypotheses",
                                        "proposition_ref"),
        exact_parameter_pins=tuple(pins),
        conclusion_index=_read_security_index(entry["conclusion_index"],
                                              f"{where} conclusion index"),
        body=_read_body(entry["body"], f"{where} body"),
    )


# --------------------------------------------------------------------------
# Bindings.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class SubjectRelation:
    kind: str
    selector: str | None = None
    input_indices: tuple[int, ...] = ()
    external_subject_schema: str | None = None
    external_arguments: tuple[BindingValue, ...] = ()

    def document(self) -> dict[str, Any]:
        if self.kind == "same_subject":
            return {"kind": "same_subject"}
        if self.kind == "exact_external_subject":
            return {
                "external_arguments": [argument.document()
                                       for argument in self.external_arguments],
                "external_subject_schema": self.external_subject_schema,
                "kind": self.kind,
            }
        return {
            "input_indices": list(self.input_indices),
            "kind": self.kind,
            "selector": self.selector,
        }


@dataclass(frozen=True)
class Binding:
    id: str
    rule: str
    rule_revision: str
    subject_schema: str
    anchor_kind: str
    anchor_ref: ExactRef
    premise_relations: tuple[tuple[str, SubjectRelation], ...]
    parameter_bindings: tuple[tuple[str, BindingValue], ...]
    fact_bindings: tuple[tuple[str, BindingValue], ...]
    condition_argument_bindings: tuple[tuple[str, tuple[BindingValue, ...]], ...]
    hypothesis_argument_bindings: tuple[tuple[str, tuple[BindingValue, ...]], ...]

    def document(self) -> dict[str, Any]:
        return {
            "anchor": {"kind": self.anchor_kind,
                       "ref": self.anchor_ref.document()},
            "condition_argument_bindings": {
                slot: [value.document() for value in values]
                for slot, values in self.condition_argument_bindings
            },
            "fact_bindings": {name: value.document()
                              for name, value in self.fact_bindings},
            "hypothesis_argument_bindings": {
                slot: [value.document() for value in values]
                for slot, values in self.hypothesis_argument_bindings
            },
            "id": self.id,
            "parameter_bindings": {name: value.document()
                                   for name, value in self.parameter_bindings},
            "premise_relations": {port: relation.document()
                                  for port, relation in self.premise_relations},
            "rule_ref": {"id": self.rule, "source_revision": self.rule_revision},
            "subject_schema": self.subject_schema,
        }

    def revision(self) -> str:
        return tagged_digest(BINDING_DOMAIN, self.document())


def _read_subject_relation(node: Any, where: str) -> SubjectRelation:
    kind = _tag(node, where, SUBJECT_RELATIONS)
    if kind == "same_subject":
        _object(node, where, ("kind",))
        return SubjectRelation(kind)
    if kind == "exact_external_subject":
        entry = _object(node, where,
                        ("kind", "external_subject_schema", "external_arguments"))
        return SubjectRelation(
            kind,
            external_subject_schema=_string(entry, "external_subject_schema",
                                            where),
            external_arguments=tuple(
                _read_binding_value(argument, f"{where} argument {position}")
                for position, argument in enumerate(
                    _list(entry, "external_arguments", where))),
        )
    entry = _object(node, where, ("kind", "selector", "input_indices"))
    selector = _member(entry["selector"], CONSUMED_SELECTORS, f"{where} selector")
    indices = [_domain_integer(index, where, "operand index")
               for index in _list(entry, "input_indices", where)]
    for index in indices:
        if index < 0:
            raise Refusal(f"{where} carries a negative operand index")
    if selector == "all_reduction_inputs" and indices:
        raise Refusal(f"{where} lists operand indices beside a whole-vector "
                      "selector")
    if selector != "all_reduction_inputs" and not indices:
        raise Refusal(f"{where} selects operands and names none")
    if len(set(indices)) != len(indices):
        raise Refusal(f"{where} names one operand position twice")
    if kind == "consumed_claim" and len(indices) != 1:
        raise Refusal(f"{where} consumes one claim and names {len(indices)}")
    return SubjectRelation(kind, selector, tuple(indices))


def _read_value_map(node: Any, where: str
                    ) -> tuple[tuple[str, BindingValue], ...]:
    if not isinstance(node, dict):
        raise Refusal(f"{where} is not an object")
    return tuple(
        (name, _read_binding_value(node[name], f"{where}.{name}"))
        for name in sorted(node)
    )


def _read_argument_map(node: Any, where: str
                       ) -> tuple[tuple[str, tuple[BindingValue, ...]], ...]:
    if not isinstance(node, dict):
        raise Refusal(f"{where} is not an object")
    entries = []
    for slot in sorted(node):
        arguments = node[slot]
        if not isinstance(arguments, list):
            raise Refusal(f"{where}.{slot} is not an ordered argument list")
        entries.append((slot, tuple(
            _read_binding_value(argument, f"{where}.{slot}[{position}]")
            for position, argument in enumerate(arguments)
        )))
    return tuple(entries)


def _read_binding(identifier: str, node: Any) -> Binding:
    where = f"binding '{identifier}'"
    entry = _object(node, where,
                    ("id", "rule", "subject_schema", "anchor",
                     "premise_relations", "parameter_bindings", "fact_bindings",
                     "condition_argument_bindings",
                     "hypothesis_argument_bindings"))
    if _string(entry, "id", where) != identifier:
        raise Refusal(f"{where} is filed under a different identifier")
    anchor = _object(entry["anchor"], f"{where} anchor", ("kind", "ref"))
    return Binding(
        id=identifier,
        rule=_string(entry, "rule", where),
        rule_revision="",  # resolved against the signature after the read
        subject_schema=_string(entry, "subject_schema", where),
        anchor_kind=_member(anchor["kind"], ANCHOR_KINDS, f"{where} anchor"),
        anchor_ref=_read_exact_ref(anchor["ref"], f"{where} anchor ref"),
        premise_relations=tuple(
            (port, _read_subject_relation(entry["premise_relations"][port],
                                          f"{where} premise '{port}'"))
            for port in sorted(_mapping(entry, "premise_relations", where))
        ),
        parameter_bindings=_read_value_map(entry["parameter_bindings"],
                                           f"{where} parameter bindings"),
        fact_bindings=_read_value_map(entry["fact_bindings"],
                                      f"{where} fact bindings"),
        condition_argument_bindings=_read_argument_map(
            entry["condition_argument_bindings"], f"{where} condition arguments"),
        hypothesis_argument_bindings=_read_argument_map(
            entry["hypothesis_argument_bindings"],
            f"{where} hypothesis arguments"),
    )


# --------------------------------------------------------------------------
# Schema tables.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class SchemaContext:
    machine_deciders: tuple[tuple[str, str, ExactRef, tuple[str, ...]], ...]
    primitive_games: tuple[tuple[str, ExactRef, tuple[str, ...],
                                 tuple[TypedName, ...]], ...]
    propositions: tuple[tuple[str, ExactRef, tuple[str, ...]], ...]
    security_indices: tuple[SecurityIndex, ...]
    subject_schemas: tuple[tuple[str, str, tuple[str, ...]], ...]

    def document(self) -> dict[str, Any]:
        return {
            "machine_deciders": {
                identifier: {"argument_types": list(types), "kind": kind,
                             "ref": ref.document()}
                for identifier, kind, ref, types in self.machine_deciders
            },
            "primitive_games": {
                identifier: {"instance_argument_types": list(types),
                             "ref": ref.document(),
                             "resources": [item.document() for item in resources]}
                for identifier, ref, types, resources in self.primitive_games
            },
            "propositions": {
                identifier: {"argument_types": list(types), "ref": ref.document()}
                for identifier, ref, types in self.propositions
            },
            "security_indices": [index.document()
                                 for index in self.security_indices],
            "subject_schemas": {
                identifier: {"argument_types": list(types), "kind": kind,
                             "ref": identifier}
                for identifier, kind, types in self.subject_schemas
            },
        }


def _read_argument_types(entry: dict[str, Any], key: str, where: str
                         ) -> tuple[str, ...]:
    return tuple(_member(item, SORTS, f"{where} argument type")
                 for item in _list(entry, key, where))


def _read_schemas(node: Any) -> SchemaContext:
    where = "schemas"
    entry = _object(node, where,
                    ("machine_deciders", "primitive_games", "propositions",
                     "security_indices", "subject_schemas"))
    deciders = []
    for identifier in sorted(_mapping(entry, "machine_deciders", where)):
        at = f"decider '{identifier}'"
        fields = _object(entry["machine_deciders"][identifier], at,
                         ("kind", "ref", "argument_types"))
        deciders.append((identifier, _string(fields, "kind", at),
                         _read_exact_ref(fields["ref"], f"{at} ref"),
                         _read_argument_types(fields, "argument_types", at)))
    games = []
    for identifier in sorted(_mapping(entry, "primitive_games", where)):
        at = f"primitive game '{identifier}'"
        fields = _object(entry["primitive_games"][identifier], at,
                         ("ref", "instance_argument_types", "resources"))
        games.append((identifier,
                      _read_exact_ref(fields["ref"], f"{at} ref"),
                      _read_argument_types(fields, "instance_argument_types", at),
                      _read_typed_names(fields["resources"], f"{at} resources")))
    propositions = []
    for identifier in sorted(_mapping(entry, "propositions", where)):
        at = f"proposition '{identifier}'"
        fields = _object(entry["propositions"][identifier], at,
                         ("ref", "argument_types"))
        propositions.append((identifier,
                             _read_exact_ref(fields["ref"], f"{at} ref"),
                             _read_argument_types(fields, "argument_types", at)))
    indices = tuple(
        _read_security_index(item, f"{where} security index {position}")
        for position, item in enumerate(_list(entry, "security_indices", where))
    )
    if len(set(indices)) != len(indices):
        raise Refusal("schemas admit the same security index twice")
    subjects = []
    for identifier in sorted(_mapping(entry, "subject_schemas", where)):
        at = f"subject schema '{identifier}'"
        fields = _object(entry["subject_schemas"][identifier], at,
                         ("kind", "ref", "argument_types"))
        if _string(fields, "ref", at) != identifier:
            raise Refusal(f"{at} is filed under a different identifier")
        subjects.append((identifier,
                         _member(fields["kind"], SUBJECT_SCHEMA_KINDS,
                                 f"{at} kind"),
                         _read_argument_types(fields, "argument_types", at)))
    return SchemaContext(tuple(deciders), tuple(games), tuple(propositions),
                         indices, tuple(subjects))


# --------------------------------------------------------------------------
# The signature.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Signature:
    schemas: SchemaContext
    rules: tuple[Rule, ...]
    bindings: tuple[Binding, ...]
    annotations: tuple[tuple[str, "Annotation"], ...] = ()

    def annotation(self, identifier: str):
        for key, value in self.annotations:
            if key == identifier:
                return value
        return None

    def rule(self, identifier: str) -> Rule:
        for rule in self.rules:
            if rule.id == identifier:
                return rule
        raise Refusal(f"no rule named {identifier!r}")

    def document(self) -> dict[str, Any]:
        """The executable content of a signature, and nothing else.

        Annotations are outside this for the same reason they are outside a
        declaration digest: correcting a citation must not make an artifact's
        analysis a different analysis.
        """
        return {
            "bindings": {binding.id: binding.document()
                         for binding in self.bindings},
            "rules": {rule.id: rule.document() for rule in self.rules},
            "schemas": self.schemas.document(),
        }

    def digest(self) -> str:
        return tagged_digest(SIGNATURE_DOMAIN, self.document())

    def lint_document(self) -> dict[str, Any]:
        """The document plus the content address of every part of it, which is
        what a second implementation has to reach from the same bytes."""
        document = self.document()
        document["digest"] = self.digest()
        document["revisions"] = {
            "bindings": {binding.id: binding.revision()
                         for binding in self.bindings},
            "rules": {rule.id: rule.revision() for rule in self.rules},
        }
        return document


# The declaration grammar is a tree, and the judgment over it is total only
# because the tree is bounded.  Hostile nesting exhausts a counter here rather
# than an implementation (docs/spec/kernel.md section 3.4).
MAX_DEPTH = 64


def _check_depth(node: Any, where: str, depth: int = 0) -> None:
    if depth > MAX_DEPTH:
        raise Refusal(f"{where} nests deeper than {MAX_DEPTH} levels")
    if isinstance(node, dict):
        for value in node.values():
            _check_depth(value, where, depth + 1)
    elif isinstance(node, list):
        for value in node:
            _check_depth(value, where, depth + 1)


def read_signature(document: Any, source: str = "signature") -> Signature:
    """Read a signature document into typed declarations.

    Well-formedness is a separate judgment; see `wellformed.freeze`, which is
    the only way to obtain a signature this reference will derive against.
    """
    _check_depth(document, source)
    root = _object(document, source,
                   ("registry", "schemas", "rules", "bindings",
                    "annotations"))
    if root["registry"] != "zkc.soundness_signature":
        raise Refusal(f"{source} is not a soundness signature")
    # `True == 1` in Python, so the type has to be checked before the value.
    if not _mapping(root, "rules", source):
        raise Refusal(f"{source} declares no rules")
    schemas = _read_schemas(root["schemas"])
    rules = tuple(
        _read_rule(identifier, _mapping(root, "rules", source)[identifier])
        for identifier in sorted(_mapping(root, "rules", source))
    )
    revisions = {rule.id: rule.revision() for rule in rules}
    bindings = []
    for identifier in sorted(_mapping(root, "bindings", source)):
        binding = _read_binding(identifier, root["bindings"][identifier])
        # A binding names its rule by identifier and the reader resolves the
        # revision here, so a binding can never be pinned to a stale digest
        # and an edited rule re-mints every binding that reaches it.
        if binding.rule not in revisions:
            raise Refusal(f"binding '{identifier}' names no rule in this "
                          "signature")
        bindings.append(dataclass_replace(binding,
                                          rule_revision=revisions[binding.rule]))
    annotations = tuple(
        (identifier, _read_annotation(identifier, root["annotations"][identifier]))
        for identifier in sorted(_mapping(root, "annotations", source))
    )
    return Signature(schemas, rules, tuple(bindings), annotations)


# --------------------------------------------------------------------------
# Annotations.  These sit outside every declaration digest: an editorial
# change must not re-mint a rule, and the presence of a citation must not
# discharge a premise.  Nothing here reaches RULE_WF.
# --------------------------------------------------------------------------

RECEIPT_STATES = frozenset(
    {"mechanized", "proof_incomplete", "subject_incomplete"})

# The axioms whose presence means the mechanized statement rests on a hole.
HOLE_AXIOMS = frozenset({"sorryAx", "sorry"})


@dataclass(frozen=True)
class SourceAnchor:
    source: str
    revision: str
    anchor: str


@dataclass(frozen=True)
class FormalizationReceipt:
    """What a machine established about a mechanized statement, and what a
    person claims about it, kept apart.

    The printed type and the admitted-axiom profile are obtainable without
    proving anything and are diffable, so they are recorded facts.  The
    obligations the cited theorem does not match are named as slots, which is
    what makes an authoring-side gap list a per-rule artifact rather than the
    output of a review that has to be re-run.
    """

    repository: str
    revision: str
    declaration: str
    statement: str
    axioms: tuple[str, ...]
    state: str
    covers: str
    does_not_cover: str
    unmatched_obligations: tuple[str, ...]

    def admits_hole(self) -> bool:
        return any(axiom in HOLE_AXIOMS for axiom in self.axioms)


@dataclass(frozen=True)
class FormalizationAbsence:
    """A surveyed absence of a mechanized counterpart.

    A receipt records a statement that exists; this records that one was
    looked for and not found, so a rule without a receipt is not silent about
    why.  When the counterpart lands, the record is replaced by a receipt
    rather than amended.
    """

    repository: str
    revision: str
    wanted: str
    demand: str


@dataclass(frozen=True)
class Annotation:
    statement: str = ""
    loss_display: str = ""
    status_rationale: str = ""
    notes: str = ""
    citations: tuple[str, ...] = ()
    statement_basis: tuple[SourceAnchor, ...] = ()
    formalization: tuple[FormalizationReceipt, ...] = ()
    formalization_absence: FormalizationAbsence | None = None


def _optional_string(node: dict[str, Any], key: str, where: str) -> str:
    if key not in node:
        return ""
    return _string(node, key, where) if node[key] != "" else ""


def _ascii_list(node: dict[str, Any], key: str, where: str,
                *, required: bool = False) -> tuple[str, ...]:
    if key not in node:
        if required:
            raise Refusal(f"{where} needs a {key!r} list")
        return ()
    values = _list(node, key, where)
    return tuple(_string({"item": value}, "item", f"{where} {key}")
                 for value in values)


def _read_receipt(node: Any, where: str) -> FormalizationReceipt:
    entry = _object(node, where, ("state", "axioms"),
                    ("repository", "revision", "declaration", "statement",
                     "covers", "does_not_cover", "unmatched_obligations"))
    return FormalizationReceipt(
        repository=_optional_string(entry, "repository", where),
        revision=_optional_string(entry, "revision", where),
        declaration=_optional_string(entry, "declaration", where),
        statement=_optional_string(entry, "statement", where),
        # Present and possibly empty: an absent list would be
        # indistinguishable from one nobody filled in, and the empty list is
        # the claim that no axiom was admitted.
        axioms=_ascii_list(entry, "axioms", where, required=True),
        state=_member(entry["state"], RECEIPT_STATES, f"{where} state"),
        covers=_optional_string(entry, "covers", where),
        does_not_cover=_optional_string(entry, "does_not_cover", where),
        unmatched_obligations=_ascii_list(entry, "unmatched_obligations",
                                          where),
    )


def _read_absence(node: Any, where: str) -> FormalizationAbsence:
    entry = _object(node, where,
                    ("repository", "revision", "wanted", "demand"))
    return FormalizationAbsence(
        repository=_string(entry, "repository", where),
        revision=_string(entry, "revision", where),
        wanted=_string(entry, "wanted", where),
        demand=_string(entry, "demand", where),
    )


def _read_annotation(identifier: str, node: Any) -> Annotation:
    where = f"annotation '{identifier}'"
    entry = _object(node, where, (),
                    ("statement", "loss_display", "status_rationale", "notes",
                     "citations", "statement_basis", "formalization",
                     "formalization_absence"))
    anchors = []
    for position, item in enumerate(entry.get("statement_basis", []) or []):
        at = f"{where} source anchor {position}"
        fields = _object(item, at, (), ("source", "revision", "anchor"))
        anchors.append(SourceAnchor(_optional_string(fields, "source", at),
                                    _optional_string(fields, "revision", at),
                                    _optional_string(fields, "anchor", at)))
    if "statement_basis" in entry and not isinstance(entry["statement_basis"],
                                                     list):
        raise Refusal(f"{where} statement basis is not a list")
    if "formalization" in entry and not isinstance(entry["formalization"], list):
        raise Refusal(f"{where} formalization is not a list")
    return Annotation(
        statement=_optional_string(entry, "statement", where),
        loss_display=_optional_string(entry, "loss_display", where),
        status_rationale=_optional_string(entry, "status_rationale", where),
        notes=_optional_string(entry, "notes", where),
        citations=_ascii_list(entry, "citations", where),
        statement_basis=tuple(anchors),
        formalization=tuple(
            _read_receipt(item, f"{where} receipt {position}")
            for position, item in enumerate(entry.get("formalization", []) or [])),
        formalization_absence=(
            _read_absence(entry["formalization_absence"],
                          f"{where} formalization absence")
            if "formalization_absence" in entry else None),
    )
