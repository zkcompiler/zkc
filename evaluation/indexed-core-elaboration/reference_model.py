"""Closed bounded Core-template experiment above exact finite Protocol Cores.

The authenticated subject is a complete declarative program AST.  One small
interpreter expands both FRI-shaped and sumcheck-shaped programs.  The grammar
has only static sequencing and finite repetition over authenticated index
axes; it has no recursion, calls, runtime branching, or family-specific opaque
nodes.  Expanded candidates become usable only after the existing Protocol
model admits and authenticates the exact finite Core.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import importlib.util
from pathlib import Path
import sys
from types import MappingProxyType
from typing import Iterable, TypeAlias


_PROTOCOL_MODEL_NAME = "_zkc_protocol_fiat_shamir_for_indexed_elaboration"
_PROTOCOL_MODEL_PATH = (
    Path(__file__).resolve().parents[1]
    / "k2-protocol-fiat-shamir"
    / "reference_model.py"
)
if _PROTOCOL_MODEL_NAME in sys.modules:
    protocol = sys.modules[_PROTOCOL_MODEL_NAME]
else:
    _spec = importlib.util.spec_from_file_location(
        _PROTOCOL_MODEL_NAME,
        _PROTOCOL_MODEL_PATH,
    )
    if _spec is None or _spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load Protocol model from {_PROTOCOL_MODEL_PATH}")
    protocol = importlib.util.module_from_spec(_spec)
    sys.modules[_PROTOCOL_MODEL_NAME] = protocol
    _spec.loader.exec_module(protocol)

k1 = protocol.k1


class ElaborationError(ValueError):
    """Base refusal for this bounded experiment."""


class GrammarError(ElaborationError):
    """A program is outside the closed declarative grammar."""


class UnsupportedDynamicTopology(GrammarError):
    """A program asks runtime data to choose its Core topology."""


class InvalidSemanticIndex(ElaborationError):
    """An index is not in the schema's exact finite semantic domain."""


class StaticExpansionOverflow(ElaborationError):
    """The schema's declared static bound does not cover a finite fiber."""


class EvaluatorLimitExceeded(ElaborationError):
    """A local evaluator refuses work without changing semantic identity."""


class UnsupportedFamilyClaim(ElaborationError):
    """Finite elaboration evidence was asked to imply an asymptotic theorem."""


# ---------------------------------------------------------------------------
# Closed declarative grammar
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class NatConst:
    value: int


@dataclass(frozen=True)
class AxisValue:
    axis: str


@dataclass(frozen=True)
class LoopValue:
    variable: str


@dataclass(frozen=True)
class NatAdd:
    left: "NatExpression"
    right: "NatExpression"


NatExpression: TypeAlias = NatConst | AxisValue | LoopValue | NatAdd


@dataclass(frozen=True)
class LiteralName:
    value: str


@dataclass(frozen=True)
class IndexedName:
    prefix: str
    indices: tuple[NatExpression, ...]


NameExpression: TypeAlias = LiteralName | IndexedName


@dataclass(frozen=True)
class ExplicitNames:
    names: tuple[NameExpression, ...]


@dataclass(frozen=True)
class RangeNames:
    prefix: str
    start: NatExpression
    count: NatExpression


@dataclass(frozen=True)
class ConcatNames:
    parts: tuple["NameSequenceExpression", ...]


NameSequenceExpression: TypeAlias = ExplicitNames | RangeNames | ConcatNames


@dataclass(frozen=True)
class PairedNameSequences:
    publications: NameSequenceExpression
    next_challenges: NameSequenceExpression


@dataclass(frozen=True)
class RefExpression:
    kind: object
    name: NameExpression


@dataclass(frozen=True)
class PredicateTemplate:
    kind: object
    refs: tuple[RefExpression, ...]
    parameters: tuple[NatExpression, ...] = ()


@dataclass(frozen=True)
class DeclareInput:
    name: NameExpression
    role: object
    scope: NameExpression
    value_sort: object


@dataclass(frozen=True)
class DeclareScope:
    name: NameExpression
    parent: NameExpression | None
    open_before: NameExpression | None


@dataclass(frozen=True)
class DeclareExtension:
    name: NameExpression


@dataclass(frozen=True)
class DeclareInitialClaim:
    name: NameExpression


@dataclass(frozen=True)
class EmitOccurrence:
    name: NameExpression
    kind: object
    scope: NameExpression = LiteralName("root")
    dependencies: tuple[RefExpression, ...] = ()
    challenge_modulus: NatExpression | None = None
    oracle_name: NameExpression | None = None
    check_predicate: PredicateTemplate | None = None
    prover_value_sort: object = protocol.ValueSort.BYTES


@dataclass(frozen=True)
class EmitReduction:
    name: NameExpression
    at_occurrence: NameExpression
    scope: NameExpression
    input_claims: NameSequenceExpression
    side_inputs: tuple[RefExpression, ...]
    required_challenges: NameSequenceExpression
    required_publications: PairedNameSequences
    output_claims: NameSequenceExpression


@dataclass(frozen=True)
class EmitClaimUse:
    claim: NameExpression
    consumer: NameExpression


@dataclass(frozen=True)
class Static:
    commands: tuple["Command", ...]


@dataclass(frozen=True)
class Repeat:
    axis: str
    variable: str
    commands: tuple["Command", ...]


@dataclass(frozen=True)
class DynamicBranch:
    """Explicitly unsupported candidate used to test topology refusal."""

    condition: RefExpression
    when_true: tuple[object, ...]
    when_false: tuple[object, ...]


Command: TypeAlias = (
    DeclareInput
    | DeclareScope
    | DeclareExtension
    | DeclareInitialClaim
    | EmitOccurrence
    | EmitReduction
    | EmitClaimUse
    | Static
    | Repeat
)


@dataclass(frozen=True)
class CoreProgram:
    commands: tuple[Command, ...]


@dataclass(frozen=True)
class IndexAxis:
    name: str
    values: tuple[int, ...]


@dataclass(frozen=True)
class SemanticIndex:
    coordinates: tuple[tuple[str, int], ...]

    def value(self, name: str) -> int:
        for axis, value in self.coordinates:
            if axis == name:
                return value
        raise InvalidSemanticIndex(f"missing semantic index axis {name!r}")


@dataclass(frozen=True)
class ExpansionSize:
    inputs: int
    scopes: int
    occurrences: int
    reductions: int
    extensions: int
    initial_claims: int
    claim_uses: int
    command_steps: int

    def within(self, bound: "ExpansionSize") -> bool:
        return (
            self.inputs <= bound.inputs
            and self.scopes <= bound.scopes
            and self.occurrences <= bound.occurrences
            and self.reductions <= bound.reductions
            and self.extensions <= bound.extensions
            and self.initial_claims <= bound.initial_claims
            and self.claim_uses <= bound.claim_uses
            and self.command_steps <= bound.command_steps
        )

    def plus(self, other: "ExpansionSize") -> "ExpansionSize":
        return ExpansionSize(
            self.inputs + other.inputs,
            self.scopes + other.scopes,
            self.occurrences + other.occurrences,
            self.reductions + other.reductions,
            self.extensions + other.extensions,
            self.initial_claims + other.initial_claims,
            self.claim_uses + other.claim_uses,
            self.command_steps + other.command_steps,
        )

    def scale(self, factor: int) -> "ExpansionSize":
        return ExpansionSize(*(factor * value for value in self.__dict__.values()))


ZERO_SIZE = ExpansionSize(0, 0, 0, 0, 0, 0, 0, 0)


@dataclass(frozen=True)
class IndexedCoreSchema:
    index_domain: tuple[IndexAxis, ...]
    static_expansion_bound: ExpansionSize
    program: CoreProgram


SCHEMA_SUBJECT_KIND = "pir.indexed-core-schema"
MAX_PROGRAM_NODES = 1024
MAX_EXPRESSION_DEPTH = 32
MAX_COMMAND_STEPS = 4096
MAX_COMMAND_DEPTH = 32
MAX_INDEX_AXES = 4
MAX_INDEX_FIBERS = 64
MAX_RANGE_NAMES = 256
MAX_AST_NODES = 4096
MAX_AST_DEPTH = 32
MAX_AST_SEQUENCE = 256
MAX_IDENTIFIER_LENGTH = 128
NATURAL_LIMIT_EXCLUSIVE = 1 << 32
MIN_AXIS_VALUE = 1
MAX_AXIS_VALUE = 8
MAX_SCHEMA_EXTENSIONS = 16


def _profile_catalog(kind: str, *declarations: str) -> object:
    return k1.DatumSeq(
        (
            k1.DatumRecord(
                (
                    (0, k1.Symbol(kind)),
                    (1, k1.DatumSeq(tuple(k1.Symbol(item) for item in declarations))),
                )
            ),
        )
    )


GRAMMAR_NODE_TYPES = (
    NatConst,
    AxisValue,
    LoopValue,
    NatAdd,
    LiteralName,
    IndexedName,
    ExplicitNames,
    RangeNames,
    ConcatNames,
    PairedNameSequences,
    RefExpression,
    PredicateTemplate,
    DeclareInput,
    DeclareScope,
    DeclareExtension,
    DeclareInitialClaim,
    EmitOccurrence,
    EmitReduction,
    EmitClaimUse,
    Static,
    Repeat,
    CoreProgram,
)
GRAMMAR_NODE_LAWS = (
    ("NatConst", "returns its authenticated u32 natural"),
    ("AxisValue", "returns the selected authenticated index coordinate"),
    ("LoopValue", "returns the current Repeat ordinal"),
    ("NatAdd", "evaluates operands left-to-right and returns exact natural addition"),
    ("LiteralName", "returns its authenticated literal"),
    (
        "IndexedName",
        "returns prefix underscore decimal evaluated indices joined by underscores",
    ),
    ("ExplicitNames", "evaluates names left-to-right preserving order"),
    (
        "RangeNames",
        "returns prefix underscore n for the half-open evaluated natural range",
    ),
    ("ConcatNames", "concatenates evaluated parts left-to-right"),
    (
        "PairedNameSequences",
        "evaluates both sequences and requires equal length before ordered zip",
    ),
    ("RefExpression", "maps kind and evaluated name exactly to Core ValueRef"),
    (
        "PredicateTemplate",
        "maps kind ordered refs and ordered natural parameters exactly to Core Predicate",
    ),
    ("DeclareInput", "appends exact name role scope sort to Core inputs"),
    (
        "DeclareScope",
        "appends exact name optional parent optional opener to Core scopes",
    ),
    ("DeclareExtension", "appends evaluated name to Core extensions"),
    ("DeclareInitialClaim", "appends evaluated name to Core initial claims"),
    (
        "EmitOccurrence",
        "appends exact evaluated occurrence fields with Always guard and no verifier rule",
    ),
    (
        "EmitReduction",
        "appends exact evaluated reduction fields and ordered equal-length publication zip",
    ),
    ("EmitClaimUse", "appends exact evaluated claim and consumer to Core claim uses"),
    ("Static", "evaluates body depth-first left-to-right in current environments"),
    (
        "Repeat",
        "evaluates body for ordinals zero through selected-axis-value-minus-one in order with scoped binding",
    ),
    (
        "CoreProgram",
        "forms Core lanes from append order after complete command evaluation",
    ),
)
FORMATION_LAWS = (
    "schema, index-domain, program, command blocks, expression collections, "
    "reference collections, predicate collections, and profile carriers use "
    "their exact immutable dataclass and tuple shapes",
    f"identifiers contain 1 through {MAX_IDENTIFIER_LENGTH} printable ASCII bytes",
    f"NatConst values are naturals below {NATURAL_LIMIT_EXCLUSIVE}; AxisValue and "
    "LoopValue names resolve only in their current closed environments; NatAdd "
    f"is exact; natural-expression depth is at most {MAX_EXPRESSION_DEPTH}",
    "IndexedName has a nonempty immutable natural-index tuple; ExplicitNames has "
    "an immutable tuple; ConcatNames has a nonempty immutable part tuple; every "
    "nested name, reference, predicate, and paired-name sequence is formed "
    "recursively with exact Protocol enum types",
    f"the complete schema AST charges every accepted dataclass node and tuple "
    f"slot before encoding; total charge is at most {MAX_AST_NODES}, structural "
    f"depth at most {MAX_AST_DEPTH}, and tuple width at most {MAX_AST_SEQUENCE}",
    f"CoreProgram is nonempty, contains at most {MAX_PROGRAM_NODES} commands, and "
    f"has command nesting at most {MAX_COMMAND_DEPTH}; Static and Repeat bodies "
    "are nonempty; Repeat names one declared axis and one fresh scoped loop "
    "variable; dynamic branches and every command outside the closed grammar "
    "are rejected",
    f"the index domain has 1 through {MAX_INDEX_AXES} canonical sorted-unique "
    f"named axes; each axis has a nonempty sorted-unique value tuple in "
    f"[{MIN_AXIS_VALUE},{MAX_AXIS_VALUE}]; the product has at most "
    f"{MAX_INDEX_FIBERS} fibers",
    "ExpansionSize has exactly eight nonnegative natural coordinates in the "
    "order inputs, scopes, occurrences, reductions, extensions, initial_claims, "
    "claim_uses, command_steps",
    f"the semantic static bound is within the imported Core maxima for inputs, "
    "scopes, occurrences, reductions, and initial claims; its local claim-use "
    f"cap equals the imported MAX_CLAIMS value; it permits at most "
    f"{MAX_SCHEMA_EXTENSIONS} extensions and {MAX_COMMAND_STEPS} interpreted "
    "command steps",
    "schema admission enumerates every exact finite index fiber, computes all "
    "eight expansion coordinates by the authenticated command-size algebra, "
    "and requires each result to be within the semantic static bound",
    f"before schema admission, every reachable RangeNames in every index and "
    f"Repeat environment has count at most {MAX_RANGE_NAMES} and start plus count "
    f"at most {NATURAL_LIMIT_EXCLUSIVE}",
    "selected-index admission requires the exact axis order with no missing or "
    "extra coordinates and requires every coordinate to belong to its "
    "authenticated finite axis",
    "schema identity authenticates the canonical ordered index-domain bodies, "
    "all eight static-bound coordinates, and the complete canonical program AST",
)
GLOBAL_INTERPRETER_LAWS = (
    "all command dispatches and every emitted Core lane are statically counted before interpretation",
    "RangeNames materialization count is refused above 256 before allocation",
    "index domains have at most four axes and at most sixty-four fibers",
    "command nesting is refused above thirty-two",
    "the complete AST carrier is refused above 4096 nodes depth 32 or sequence width 256 before encoding",
    "unsupported dynamic branching recursion calls and runtime topology are rejected",
    "candidate Core is authenticated and admitted by the unchanged concrete Core authority",
)


def _law_bytes(
    node_laws=GRAMMAR_NODE_LAWS,
    formation_laws=FORMATION_LAWS,
    global_laws=GLOBAL_INTERPRETER_LAWS,
) -> bytes:
    expected = {item.__name__ for item in GRAMMAR_NODE_TYPES}
    names = [name for name, _ in node_laws]
    if len(names) != len(set(names)) or set(names) != expected:
        raise GrammarError("interpreter law descriptor is not closed over the grammar")
    if (
        any(not law for _, law in node_laws)
        or any(not law for law in formation_laws)
        or any(not law for law in global_laws)
    ):
        raise GrammarError("interpreter law entries must be nonempty")
    return k1.encode_datum(
        k1.DatumRecord(
            (
                (
                    0,
                    k1.DatumSeq(
                        tuple(
                            k1.DatumRecord(
                                (
                                    (0, k1.Symbol(name)),
                                    (1, k1.BytesValue(law.encode("ascii"))),
                                )
                            )
                            for name, law in node_laws
                        )
                    ),
                ),
                (
                    1,
                    k1.DatumSeq(
                        tuple(
                            k1.BytesValue(law.encode("ascii")) for law in formation_laws
                        )
                    ),
                ),
                (
                    2,
                    k1.DatumSeq(
                        tuple(k1.BytesValue(law.encode("ascii")) for law in global_laws)
                    ),
                ),
            )
        )
    )


def make_schema_profile(
    node_laws=GRAMMAR_NODE_LAWS,
    formation_laws=FORMATION_LAWS,
    global_laws=GLOBAL_INTERPRETER_LAWS,
):
    return k1.SemanticLanguageProfile(
        k1.Symbol("zkc.pir.indexed-core-authoring"),
        1,
        (protocol.PIR_INTERACTION_PROFILE_ID,),
        (k1.Symbol(SCHEMA_SUBJECT_KIND),),
        _profile_catalog(
            "pir.indexed-core-authoring-declaration",
            "closed-core-program-ast-v1",
            "static-sequence-interpreter-v1",
            "finite-index-repeat-interpreter-v1",
        ),
        _law_bytes(node_laws, formation_laws, global_laws),
    )


SCHEMA_PROFILE = make_schema_profile()
SCHEMA_PROFILE_ID = SCHEMA_PROFILE.identity
SCHEMA_PROFILE_PREIMAGES = {
    **protocol.PIR_INTERACTION_PROFILE_PREIMAGES,
    SCHEMA_PROFILE_ID: SCHEMA_PROFILE,
}
SUPPORTED_PROFILES = tuple(
    sorted(
        (protocol.PIR_INTERACTION_PROFILE_ID, SCHEMA_PROFILE_ID),
        key=lambda item: item.internal_reference(),
    )
)


# ---------------------------------------------------------------------------
# Grammar formation and canonical AST body
# ---------------------------------------------------------------------------


def _identifier(value: object, what: str) -> str:
    if type(value) is not str or not value or len(value) > MAX_IDENTIFIER_LENGTH:
        raise GrammarError(f"{what} must be nonempty bounded text")
    try:
        encoded = value.encode("ascii")
    except UnicodeEncodeError as error:
        raise GrammarError(f"{what} must be ASCII") from error
    if any(byte < 0x21 or byte > 0x7E for byte in encoded):
        raise GrammarError(f"{what} must use printable ASCII")
    return value


def _admit_ast_carrier(root: object) -> None:
    """Meter every grammar node and tuple slot before encoding or enumeration."""
    node_types = set(GRAMMAR_NODE_TYPES) | {
        IndexAxis,
        ExpansionSize,
        IndexedCoreSchema,
    }
    nodes = 0

    def visit(value: object, depth: int) -> None:
        nonlocal nodes
        if depth > MAX_AST_DEPTH:
            raise GrammarError("AST carrier exceeds the structural depth bound")
        if type(value) is tuple:
            if len(value) > MAX_AST_SEQUENCE:
                raise GrammarError("AST carrier sequence exceeds the width bound")
            nodes += len(value)  # tuple slots are independently charged
            if nodes > MAX_AST_NODES:
                raise GrammarError("AST carrier exceeds the total node bound")
            for item in value:
                visit(item, depth + 1)
            return
        if type(value) not in node_types and type(value) not in {
            PairedNameSequences,
            PredicateTemplate,
            RefExpression,
        }:
            return
        nodes += 1
        if nodes > MAX_AST_NODES:
            raise GrammarError("AST carrier exceeds the total node bound")
        for field_info in value.__dataclass_fields__.values():
            visit(getattr(value, field_info.name), depth + 1)

    visit(root, 0)


def _admit_nat(
    expression: object,
    axes: frozenset[str],
    loops: frozenset[str],
    depth: int = 0,
) -> None:
    if depth > MAX_EXPRESSION_DEPTH:
        raise GrammarError("natural expression exceeds the depth bound")
    if type(expression) is NatConst:
        if (
            type(expression.value) is not int
            or not 0 <= expression.value < NATURAL_LIMIT_EXCLUSIVE
        ):
            raise GrammarError("natural constant is outside the grammar bound")
    elif type(expression) is AxisValue:
        if expression.axis not in axes:
            raise GrammarError("natural expression names an unknown finite axis")
    elif type(expression) is LoopValue:
        if expression.variable not in loops:
            raise GrammarError("natural expression names an inactive loop variable")
    elif type(expression) is NatAdd:
        _admit_nat(expression.left, axes, loops, depth + 1)
        _admit_nat(expression.right, axes, loops, depth + 1)
    else:
        raise GrammarError("unsupported natural expression")


def _admit_name(
    expression: object,
    axes: frozenset[str],
    loops: frozenset[str],
) -> None:
    if type(expression) is LiteralName:
        _identifier(expression.value, "literal name")
    elif type(expression) is IndexedName:
        _identifier(expression.prefix, "indexed-name prefix")
        if type(expression.indices) is not tuple or not expression.indices:
            raise GrammarError("indexed name needs an immutable nonempty index tuple")
        for item in expression.indices:
            _admit_nat(item, axes, loops)
    else:
        raise GrammarError("unsupported name expression")


def _admit_names(
    expression: object,
    axes: frozenset[str],
    loops: frozenset[str],
) -> None:
    if type(expression) is ExplicitNames:
        if type(expression.names) is not tuple:
            raise GrammarError("explicit names must be an immutable tuple")
        for name in expression.names:
            _admit_name(name, axes, loops)
    elif type(expression) is RangeNames:
        _identifier(expression.prefix, "range-name prefix")
        _admit_nat(expression.start, axes, loops)
        _admit_nat(expression.count, axes, loops)
    elif type(expression) is ConcatNames:
        if type(expression.parts) is not tuple or not expression.parts:
            raise GrammarError("name concatenation needs immutable nonempty parts")
        for part in expression.parts:
            _admit_names(part, axes, loops)
    else:
        raise GrammarError("unsupported name-sequence expression")


def _admit_ref(
    expression: object,
    axes: frozenset[str],
    loops: frozenset[str],
) -> None:
    if (
        type(expression) is not RefExpression
        or type(expression.kind) is not protocol.RefKind
    ):
        raise GrammarError("reference expression has the wrong typed shape")
    _admit_name(expression.name, axes, loops)


def admit_program(program: CoreProgram, axes: frozenset[str]) -> None:
    if type(program) is not CoreProgram or type(program.commands) is not tuple:
        raise GrammarError("program needs the exact immutable carrier")
    _admit_ast_carrier(program)
    if not program.commands:
        raise GrammarError("program must contain at least one command")
    nodes = 0

    def visit(
        commands: tuple[object, ...], loops: frozenset[str], depth: int = 0
    ) -> None:
        nonlocal nodes
        if depth > MAX_COMMAND_DEPTH:
            raise GrammarError("command nesting exceeds the constitutional bound")
        if type(commands) is not tuple:
            raise GrammarError("command blocks must be immutable tuples")
        for command in commands:
            nodes += 1
            if nodes > MAX_PROGRAM_NODES:
                raise GrammarError("program exceeds the static AST-node bound")
            if type(command) is DynamicBranch:
                raise UnsupportedDynamicTopology(
                    "runtime-dependent Core topology is outside this grammar"
                )
            if type(command) is Static:
                if not command.commands:
                    raise GrammarError("Static needs a nonempty command block")
                visit(command.commands, loops, depth + 1)
            elif type(command) is Repeat:
                if command.axis not in axes:
                    raise GrammarError("Repeat names no authenticated finite axis")
                _identifier(command.variable, "loop variable")
                if command.variable in loops or not command.commands:
                    raise GrammarError(
                        "Repeat variable is shadowed or its body is empty"
                    )
                visit(command.commands, loops | {command.variable}, depth + 1)
            elif type(command) is DeclareInput:
                _admit_name(command.name, axes, loops)
                _admit_name(command.scope, axes, loops)
                if (
                    type(command.role) is not protocol.InputRole
                    or type(command.value_sort) is not protocol.ValueSort
                ):
                    raise GrammarError("input command has invalid typed axes")
            elif type(command) is DeclareScope:
                _admit_name(command.name, axes, loops)
                for optional in (command.parent, command.open_before):
                    if optional is not None:
                        _admit_name(optional, axes, loops)
            elif type(command) in {DeclareExtension, DeclareInitialClaim}:
                _admit_name(command.name, axes, loops)
            elif type(command) is EmitOccurrence:
                _admit_name(command.name, axes, loops)
                _admit_name(command.scope, axes, loops)
                if type(command.kind) is not protocol.OccurrenceKind:
                    raise GrammarError("occurrence command has an invalid kind")
                if type(command.dependencies) is not tuple:
                    raise GrammarError("occurrence dependencies must be immutable")
                for reference in command.dependencies:
                    _admit_ref(reference, axes, loops)
                if command.challenge_modulus is not None:
                    _admit_nat(command.challenge_modulus, axes, loops)
                if command.oracle_name is not None:
                    _admit_name(command.oracle_name, axes, loops)
                if command.check_predicate is not None:
                    predicate = command.check_predicate
                    if (
                        type(predicate) is not PredicateTemplate
                        or type(predicate.kind) is not protocol.PredicateKind
                        or type(predicate.refs) is not tuple
                        or type(predicate.parameters) is not tuple
                    ):
                        raise GrammarError("predicate template has the wrong shape")
                    for reference in predicate.refs:
                        _admit_ref(reference, axes, loops)
                    for parameter in predicate.parameters:
                        _admit_nat(parameter, axes, loops)
                if type(command.prover_value_sort) is not protocol.ValueSort:
                    raise GrammarError("occurrence prover sort is invalid")
            elif type(command) is EmitReduction:
                for name in (command.name, command.at_occurrence, command.scope):
                    _admit_name(name, axes, loops)
                for names in (
                    command.input_claims,
                    command.required_challenges,
                    command.output_claims,
                ):
                    _admit_names(names, axes, loops)
                if type(command.side_inputs) is not tuple:
                    raise GrammarError("reduction side inputs must be immutable")
                for reference in command.side_inputs:
                    _admit_ref(reference, axes, loops)
                pairs = command.required_publications
                if type(pairs) is not PairedNameSequences:
                    raise GrammarError("publication pairs have the wrong shape")
                _admit_names(pairs.publications, axes, loops)
                _admit_names(pairs.next_challenges, axes, loops)
            elif type(command) is EmitClaimUse:
                _admit_name(command.claim, axes, loops)
                _admit_name(command.consumer, axes, loops)
            else:
                raise GrammarError("unsupported command in the closed grammar")

    visit(program.commands, frozenset())


def _tagged(tag: str, *values: object) -> object:
    return k1.DatumRecord(
        ((0, k1.Symbol(tag)),)
        + tuple((ordinal + 1, value) for ordinal, value in enumerate(values))
    )


def _optional(value: object | None, encoder: object) -> object:
    if value is None:
        return k1.DatumVariant(0, k1.UNIT)
    return k1.DatumVariant(1, encoder(value))


def _nat_body(expression: NatExpression) -> object:
    if type(expression) is NatConst:
        return _tagged("nat-const", k1.Nat(expression.value))
    if type(expression) is AxisValue:
        return _tagged("axis-value", k1.Symbol(expression.axis))
    if type(expression) is LoopValue:
        return _tagged("loop-value", k1.Symbol(expression.variable))
    assert type(expression) is NatAdd
    return _tagged("nat-add", _nat_body(expression.left), _nat_body(expression.right))


def _name_body(expression: NameExpression) -> object:
    if type(expression) is LiteralName:
        return _tagged("literal-name", k1.Symbol(expression.value))
    assert type(expression) is IndexedName
    return _tagged(
        "indexed-name",
        k1.Symbol(expression.prefix),
        k1.DatumSeq(tuple(_nat_body(item) for item in expression.indices)),
    )


def _names_body(expression: NameSequenceExpression) -> object:
    if type(expression) is ExplicitNames:
        return _tagged(
            "explicit-names",
            k1.DatumSeq(tuple(_name_body(item) for item in expression.names)),
        )
    if type(expression) is RangeNames:
        return _tagged(
            "range-names",
            k1.Symbol(expression.prefix),
            _nat_body(expression.start),
            _nat_body(expression.count),
        )
    assert type(expression) is ConcatNames
    return _tagged(
        "concat-names",
        k1.DatumSeq(tuple(_names_body(item) for item in expression.parts)),
    )


def _ref_body(expression: RefExpression) -> object:
    return _tagged(
        "ref",
        k1.Symbol(expression.kind.value),
        _name_body(expression.name),
    )


def _predicate_body(expression: PredicateTemplate) -> object:
    return _tagged(
        "predicate",
        k1.Symbol(expression.kind.value),
        k1.DatumSeq(tuple(_ref_body(item) for item in expression.refs)),
        k1.DatumSeq(tuple(_nat_body(item) for item in expression.parameters)),
    )


def _command_body(command: Command) -> object:
    if type(command) is Static:
        return _tagged(
            "static",
            k1.DatumSeq(tuple(_command_body(item) for item in command.commands)),
        )
    if type(command) is Repeat:
        return _tagged(
            "repeat",
            k1.Symbol(command.axis),
            k1.Symbol(command.variable),
            k1.DatumSeq(tuple(_command_body(item) for item in command.commands)),
        )
    if type(command) is DeclareInput:
        return _tagged(
            "declare-input",
            _name_body(command.name),
            k1.Symbol(command.role.value),
            _name_body(command.scope),
            k1.Symbol(command.value_sort.value),
        )
    if type(command) is DeclareScope:
        return _tagged(
            "declare-scope",
            _name_body(command.name),
            _optional(command.parent, _name_body),
            _optional(command.open_before, _name_body),
        )
    if type(command) is DeclareExtension:
        return _tagged("declare-extension", _name_body(command.name))
    if type(command) is DeclareInitialClaim:
        return _tagged("declare-initial-claim", _name_body(command.name))
    if type(command) is EmitOccurrence:
        return _tagged(
            "emit-occurrence",
            _name_body(command.name),
            k1.Symbol(command.kind.value),
            _name_body(command.scope),
            k1.DatumSeq(tuple(_ref_body(item) for item in command.dependencies)),
            _optional(command.challenge_modulus, _nat_body),
            _optional(command.oracle_name, _name_body),
            _optional(command.check_predicate, _predicate_body),
            k1.Symbol(command.prover_value_sort.value),
        )
    if type(command) is EmitReduction:
        return _tagged(
            "emit-reduction",
            _name_body(command.name),
            _name_body(command.at_occurrence),
            _name_body(command.scope),
            _names_body(command.input_claims),
            k1.DatumSeq(tuple(_ref_body(item) for item in command.side_inputs)),
            _names_body(command.required_challenges),
            _tagged(
                "paired-name-sequences",
                _names_body(command.required_publications.publications),
                _names_body(command.required_publications.next_challenges),
            ),
            _names_body(command.output_claims),
        )
    assert type(command) is EmitClaimUse
    return _tagged(
        "emit-claim-use",
        _name_body(command.claim),
        _name_body(command.consumer),
    )


def program_body(program: CoreProgram) -> object:
    return _tagged(
        "closed-core-program-v1",
        k1.DatumSeq(tuple(_command_body(item) for item in program.commands)),
    )


# ---------------------------------------------------------------------------
# Schema, index, expansion, and generic interpretation
# ---------------------------------------------------------------------------


def semantic_index(**coordinates: int) -> SemanticIndex:
    return SemanticIndex(tuple(coordinates.items()))


def _admit_axis(axis: IndexAxis) -> None:
    if type(axis) is not IndexAxis:
        raise GrammarError("index axes need an exact immutable shape")
    _identifier(axis.name, "index-axis name")
    if type(axis.values) is not tuple or not axis.values:
        raise GrammarError("every index axis needs a nonempty finite domain")
    if axis.values != tuple(sorted(set(axis.values))):
        raise GrammarError("index axis values must be sorted and unique")
    if any(
        type(value) is not int or not MIN_AXIS_VALUE <= value <= MAX_AXIS_VALUE
        for value in axis.values
    ):
        raise GrammarError("index axis value is outside the closed repeat bound")


def _admit_size(size: object, what: str) -> None:
    if type(size) is not ExpansionSize or any(
        type(value) is not int or value < 0
        for value in (
            size.inputs,
            size.scopes,
            size.occurrences,
            size.reductions,
            size.extensions,
            size.initial_claims,
            size.claim_uses,
            size.command_steps,
        )
    ):
        raise ElaborationError(f"{what} has the wrong exact finite shape")


def _index_mapping(schema: IndexedCoreSchema, index: SemanticIndex) -> dict[str, int]:
    if type(index) is not SemanticIndex or type(index.coordinates) is not tuple:
        raise InvalidSemanticIndex("semantic index has the wrong exact shape")
    if len(index.coordinates) != len(schema.index_domain):
        raise InvalidSemanticIndex(
            "semantic index axes are missing, extra, or reordered"
        )
    if any(
        type(coordinate) is not tuple or len(coordinate) != 2
        for coordinate in index.coordinates
    ):
        raise InvalidSemanticIndex("semantic index has the wrong exact shape")
    expected_names = tuple(axis.name for axis in schema.index_domain)
    actual_names = tuple(name for name, _ in index.coordinates)
    if actual_names != expected_names:
        raise InvalidSemanticIndex(
            "semantic index axes are missing, extra, or reordered"
        )
    result: dict[str, int] = {}
    for (name, value), axis in zip(index.coordinates, schema.index_domain):
        if type(name) is not str or type(value) is not int or value not in axis.values:
            raise InvalidSemanticIndex(
                "semantic index is outside the exact finite domain"
            )
        result[name] = value
    return result


def _raw_indices(schema: IndexedCoreSchema) -> tuple[SemanticIndex, ...]:
    result = (SemanticIndex(()),)
    for axis in schema.index_domain:
        result = tuple(
            SemanticIndex((*prefix.coordinates, (axis.name, value)))
            for prefix in result
            for value in axis.values
        )
    return result


def _command_size(
    commands: tuple[Command, ...],
    index_values: dict[str, int],
) -> ExpansionSize:
    total = ZERO_SIZE
    for command in commands:
        total = total.plus(ExpansionSize(0, 0, 0, 0, 0, 0, 0, 1))
        if type(command) is Static:
            total = total.plus(_command_size(command.commands, index_values))
        elif type(command) is Repeat:
            body = _command_size(command.commands, index_values)
            total = total.plus(body.scale(index_values[command.axis]))
        elif type(command) is DeclareInput:
            total = total.plus(ExpansionSize(1, 0, 0, 0, 0, 0, 0, 0))
        elif type(command) is DeclareScope:
            total = total.plus(ExpansionSize(0, 1, 0, 0, 0, 0, 0, 0))
        elif type(command) is DeclareExtension:
            total = total.plus(ExpansionSize(0, 0, 0, 0, 1, 0, 0, 0))
        elif type(command) is DeclareInitialClaim:
            total = total.plus(ExpansionSize(0, 0, 0, 0, 0, 1, 0, 0))
        elif type(command) is EmitOccurrence:
            total = total.plus(ExpansionSize(0, 0, 1, 0, 0, 0, 0, 0))
        elif type(command) is EmitReduction:
            total = total.plus(ExpansionSize(0, 0, 0, 1, 0, 0, 0, 0))
        elif type(command) is EmitClaimUse:
            total = total.plus(ExpansionSize(0, 0, 0, 0, 0, 0, 1, 0))
    return total


def admit_schema(schema: IndexedCoreSchema) -> None:
    if type(schema) is not IndexedCoreSchema or type(schema.index_domain) is not tuple:
        raise ElaborationError("schema needs the exact immutable carrier")
    _admit_ast_carrier(schema)
    if not schema.index_domain:
        raise ElaborationError("schema needs a nonempty finite index domain")
    for axis in schema.index_domain:
        _admit_axis(axis)
    if len(schema.index_domain) > MAX_INDEX_AXES:
        raise ElaborationError("schema has too many index axes")
    fiber_count = 1
    for axis in schema.index_domain:
        fiber_count *= len(axis.values)
    if fiber_count > MAX_INDEX_FIBERS:
        raise ElaborationError("schema finite index product is too large")
    axis_names = tuple(axis.name for axis in schema.index_domain)
    if axis_names != tuple(sorted(set(axis_names))):
        raise ElaborationError("schema axes must be canonical sorted-unique")
    admit_program(schema.program, frozenset(axis_names))
    _admit_size(schema.static_expansion_bound, "schema expansion bound")
    constitutional = ExpansionSize(
        protocol.MAX_INPUTS,
        protocol.MAX_SCOPES,
        protocol.MAX_OCCURRENCES,
        protocol.MAX_CLAIMS,
        MAX_SCHEMA_EXTENSIONS,
        protocol.MAX_CLAIMS,
        protocol.MAX_CLAIMS,
        MAX_COMMAND_STEPS,
    )
    if not schema.static_expansion_bound.within(constitutional):
        raise ElaborationError("schema bound exceeds the existing Core envelope")
    for index in _raw_indices(schema):
        index_values = _index_mapping(schema, index)
        size = _command_size(schema.program.commands, index_values)
        if not size.within(schema.static_expansion_bound):
            raise StaticExpansionOverflow(
                "schema bound does not cover its complete finite index domain"
            )
        _preflight_materializations(schema.program.commands, index_values, {})


def admit_index(schema: IndexedCoreSchema, index: SemanticIndex) -> None:
    admit_schema(schema)
    _index_mapping(schema, index)


def _axis_body(axis: IndexAxis) -> object:
    return k1.DatumRecord(
        (
            (0, k1.Symbol(axis.name)),
            (1, k1.DatumSeq(tuple(k1.Nat(value) for value in axis.values))),
        )
    )


def _size_body(size: ExpansionSize) -> object:
    return k1.DatumRecord(
        (
            (0, k1.Nat(size.inputs)),
            (1, k1.Nat(size.scopes)),
            (2, k1.Nat(size.occurrences)),
            (3, k1.Nat(size.reductions)),
            (4, k1.Nat(size.extensions)),
            (5, k1.Nat(size.initial_claims)),
            (6, k1.Nat(size.claim_uses)),
            (7, k1.Nat(size.command_steps)),
        )
    )


def schema_body(schema: IndexedCoreSchema) -> object:
    admit_schema(schema)
    return k1.DatumRecord(
        (
            (0, k1.DatumSeq(tuple(_axis_body(axis) for axis in schema.index_domain))),
            (1, _size_body(schema.static_expansion_bound)),
            (2, program_body(schema.program)),
        )
    )


def schema_id(schema: IndexedCoreSchema) -> object:
    return k1.profiled_content_id(
        SCHEMA_SUBJECT_KIND,
        SCHEMA_PROFILE_ID,
        schema_body(schema),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def authenticate_schema(schema: IndexedCoreSchema) -> object:
    identifier = schema_id(schema)
    k1.authenticate_profiled_semantic_content(
        identifier,
        SCHEMA_PROFILE_ID,
        schema_body(schema),
        dict(SCHEMA_PROFILE_PREIMAGES),
        supported_profiles=SUPPORTED_PROFILES,
    )
    return identifier


def predicted_expansion(
    schema: IndexedCoreSchema,
    index: SemanticIndex,
) -> ExpansionSize:
    admit_index(schema, index)
    return _command_size(schema.program.commands, _index_mapping(schema, index))


def _eval_nat(
    expression: NatExpression,
    index_values: dict[str, int],
    loop_values: dict[str, int],
) -> int:
    if type(expression) is NatConst:
        return expression.value
    if type(expression) is AxisValue:
        return index_values[expression.axis]
    if type(expression) is LoopValue:
        return loop_values[expression.variable]
    assert type(expression) is NatAdd
    return _eval_nat(expression.left, index_values, loop_values) + _eval_nat(
        expression.right, index_values, loop_values
    )


def _eval_name(
    expression: NameExpression,
    index_values: dict[str, int],
    loop_values: dict[str, int],
) -> str:
    if type(expression) is LiteralName:
        return expression.value
    assert type(expression) is IndexedName
    suffix = "_".join(
        str(_eval_nat(item, index_values, loop_values)) for item in expression.indices
    )
    return f"{expression.prefix}_{suffix}"


def _eval_names(
    expression: NameSequenceExpression,
    index_values: dict[str, int],
    loop_values: dict[str, int],
) -> tuple[str, ...]:
    if type(expression) is ExplicitNames:
        return tuple(
            _eval_name(item, index_values, loop_values) for item in expression.names
        )
    if type(expression) is RangeNames:
        start = _eval_nat(expression.start, index_values, loop_values)
        count = _eval_nat(expression.count, index_values, loop_values)
        if count > MAX_RANGE_NAMES:
            raise EvaluatorLimitExceeded(
                "range-name materialization exceeds its exact cap"
            )
        return tuple(
            f"{expression.prefix}_{value}" for value in range(start, start + count)
        )
    assert type(expression) is ConcatNames
    return tuple(
        name
        for part in expression.parts
        for name in _eval_names(part, index_values, loop_values)
    )


def _eval_ref(
    expression: RefExpression,
    index_values: dict[str, int],
    loop_values: dict[str, int],
) -> object:
    name = _eval_name(expression.name, index_values, loop_values)
    return protocol.ValueRef(expression.kind, name)


def _preflight_names(
    expression: NameSequenceExpression,
    index_values: dict[str, int],
    loop_values: dict[str, int],
) -> None:
    if type(expression) is RangeNames:
        start = _eval_nat(expression.start, index_values, loop_values)
        count = _eval_nat(expression.count, index_values, loop_values)
        if count > MAX_RANGE_NAMES or start + count > NATURAL_LIMIT_EXCLUSIVE:
            raise EvaluatorLimitExceeded(
                "range-name materialization exceeds its exact cap"
            )
    elif type(expression) is ConcatNames:
        for part in expression.parts:
            _preflight_names(part, index_values, loop_values)


def _preflight_materializations(
    commands: tuple[Command, ...],
    index_values: dict[str, int],
    loop_values: dict[str, int],
) -> None:
    for command in commands:
        if type(command) is Static:
            _preflight_materializations(command.commands, index_values, loop_values)
        elif type(command) is Repeat:
            for ordinal in range(index_values[command.axis]):
                _preflight_materializations(
                    command.commands,
                    index_values,
                    {**loop_values, command.variable: ordinal},
                )
        elif type(command) is EmitReduction:
            for names in (
                command.input_claims,
                command.required_challenges,
                command.required_publications.publications,
                command.required_publications.next_challenges,
                command.output_claims,
            ):
                _preflight_names(names, index_values, loop_values)


@dataclass
class _Builder:
    inputs: list[object] = field(default_factory=list)
    scopes: list[object] = field(default_factory=list)
    schedule: list[object] = field(default_factory=list)
    extensions: list[str] = field(default_factory=list)
    initial_claims: list[str] = field(default_factory=list)
    reductions: list[object] = field(default_factory=list)
    claim_uses: list[object] = field(default_factory=list)
    command_steps: int = 0


def _interpret_commands(
    commands: tuple[Command, ...],
    index_values: dict[str, int],
    loop_values: dict[str, int],
    builder: _Builder,
) -> None:
    for command in commands:
        builder.command_steps += 1
        if type(command) is Static:
            _interpret_commands(command.commands, index_values, loop_values, builder)
        elif type(command) is Repeat:
            for ordinal in range(index_values[command.axis]):
                nested = {**loop_values, command.variable: ordinal}
                _interpret_commands(command.commands, index_values, nested, builder)
        elif type(command) is DeclareInput:
            builder.inputs.append(
                protocol.InputDecl(
                    _eval_name(command.name, index_values, loop_values),
                    command.role,
                    _eval_name(command.scope, index_values, loop_values),
                    command.value_sort,
                )
            )
        elif type(command) is DeclareScope:
            builder.scopes.append(
                protocol.ScopeDecl(
                    _eval_name(command.name, index_values, loop_values),
                    None
                    if command.parent is None
                    else _eval_name(command.parent, index_values, loop_values),
                    None
                    if command.open_before is None
                    else _eval_name(command.open_before, index_values, loop_values),
                )
            )
        elif type(command) is DeclareExtension:
            builder.extensions.append(
                _eval_name(command.name, index_values, loop_values)
            )
        elif type(command) is DeclareInitialClaim:
            builder.initial_claims.append(
                _eval_name(command.name, index_values, loop_values)
            )
        elif type(command) is EmitOccurrence:
            predicate = command.check_predicate
            builder.schedule.append(
                protocol.Occurrence(
                    _eval_name(command.name, index_values, loop_values),
                    command.kind,
                    _eval_name(command.scope, index_values, loop_values),
                    tuple(
                        _eval_ref(item, index_values, loop_values)
                        for item in command.dependencies
                    ),
                    challenge_domain=(
                        None
                        if command.challenge_modulus is None
                        else protocol.ChallengeDomain(
                            _eval_nat(
                                command.challenge_modulus,
                                index_values,
                                loop_values,
                            )
                        )
                    ),
                    oracle_name=(
                        None
                        if command.oracle_name is None
                        else _eval_name(command.oracle_name, index_values, loop_values)
                    ),
                    check_predicate=(
                        None
                        if predicate is None
                        else protocol.Predicate(
                            predicate.kind,
                            tuple(
                                _eval_ref(item, index_values, loop_values)
                                for item in predicate.refs
                            ),
                            tuple(
                                _eval_nat(item, index_values, loop_values)
                                for item in predicate.parameters
                            ),
                        )
                    ),
                    prover_value_sort=command.prover_value_sort,
                )
            )
        elif type(command) is EmitReduction:
            pairs = command.required_publications
            publications = _eval_names(pairs.publications, index_values, loop_values)
            challenges = _eval_names(pairs.next_challenges, index_values, loop_values)
            if len(publications) != len(challenges):
                raise GrammarError(
                    "publication and next-challenge sequences have unequal lengths"
                )
            builder.reductions.append(
                protocol.ReductionDecl(
                    _eval_name(command.name, index_values, loop_values),
                    _eval_name(command.at_occurrence, index_values, loop_values),
                    _eval_name(command.scope, index_values, loop_values),
                    _eval_names(command.input_claims, index_values, loop_values),
                    tuple(
                        _eval_ref(item, index_values, loop_values)
                        for item in command.side_inputs
                    ),
                    _eval_names(command.required_challenges, index_values, loop_values),
                    tuple(
                        protocol.RequiredPublication(publication, challenge)
                        for publication, challenge in zip(publications, challenges)
                    ),
                    _eval_names(command.output_claims, index_values, loop_values),
                )
            )
        else:
            assert type(command) is EmitClaimUse
            builder.claim_uses.append(
                protocol.ClaimConsumerUse(
                    _eval_name(command.claim, index_values, loop_values),
                    _eval_name(command.consumer, index_values, loop_values),
                )
            )


def elaborate_core_candidate(
    schema: IndexedCoreSchema,
    index: SemanticIndex,
) -> object:
    admit_index(schema, index)
    index_values = _index_mapping(schema, index)
    builder = _Builder()
    _interpret_commands(schema.program.commands, index_values, {}, builder)
    core = protocol.Core(
        tuple(builder.inputs),
        tuple(builder.scopes),
        tuple(builder.schedule),
        tuple(builder.extensions),
        tuple(builder.initial_claims),
        tuple(builder.reductions),
        tuple(builder.claim_uses),
    )
    _LIVE_METRICS[id(core)] = builder.command_steps
    return core


def _actual_size(core: object, command_steps: int) -> ExpansionSize:
    return ExpansionSize(
        len(core.inputs),
        len(core.scopes),
        len(core.schedule),
        len(core.reductions),
        len(core.extensions),
        len(core.initial_claims),
        len(core.claim_uses),
        command_steps,
    )


def _authenticate_core(core: object) -> object:
    protocol.admit_core(core)
    identifier = protocol.core_id(core)
    k1.authenticate_profiled_semantic_content(
        identifier,
        protocol.PIR_INTERACTION_PROFILE_ID,
        k1.decode_datum(protocol.core_body(core)),
        dict(protocol.PIR_INTERACTION_PROFILE_PREIMAGES),
        supported_profiles=(protocol.PIR_INTERACTION_PROFILE_ID,),
    )
    return identifier


DEFAULT_EVALUATOR_LIMITS = ExpansionSize(128, 64, 512, 256, 16, 256, 256, 4096)
_ELABORATION_ISSUER = object()
_LIVE_RESULTS: dict[int, object] = {}
_LIVE_METRICS: dict[int, int] = {}


@dataclass(frozen=True, eq=False, repr=False)
class CheckedCoreElaborationAt:
    schema_id: object
    index: SemanticIndex
    core_id: object
    core: object
    expansion: ExpansionSize
    _issuer: object = field(repr=False, compare=False)

    def __post_init__(self) -> None:
        if self._issuer is not _ELABORATION_ISSUER:
            raise ElaborationError("only the elaboration checker may issue a result")


def check_core_elaboration_at(
    schema: IndexedCoreSchema,
    index: SemanticIndex,
    *,
    evaluator_limits: ExpansionSize = DEFAULT_EVALUATOR_LIMITS,
) -> CheckedCoreElaborationAt:
    admit_index(schema, index)
    authenticated_schema_id = authenticate_schema(schema)
    predicted = predicted_expansion(schema, index)
    _admit_size(evaluator_limits, "evaluator limit")
    if not predicted.within(evaluator_limits):
        raise EvaluatorLimitExceeded(
            "selected fiber exceeds this evaluator's nonsemantic work limit"
        )
    core = elaborate_core_candidate(schema, index)
    actual = _actual_size(core, _LIVE_METRICS.pop(id(core)))
    if actual != predicted:
        raise ElaborationError("interpreter output disagrees with its static size law")
    authenticated_core_id = _authenticate_core(core)
    result = CheckedCoreElaborationAt(
        authenticated_schema_id,
        index,
        authenticated_core_id,
        core,
        actual,
        _ELABORATION_ISSUER,
    )
    _LIVE_RESULTS[id(result)] = result
    return result


def require_live_result(result: object) -> CheckedCoreElaborationAt:
    if (
        type(result) is not CheckedCoreElaborationAt
        or result._issuer is not _ELABORATION_ISSUER
        or _LIVE_RESULTS.get(id(result)) is not result
    ):
        raise ElaborationError("checked elaboration result is absent or not live")
    return result


# ---------------------------------------------------------------------------
# Two programs in the same grammar
# ---------------------------------------------------------------------------


def _literal(value: str) -> LiteralName:
    return LiteralName(value)


def _indexed(prefix: str, *indices: NatExpression) -> IndexedName:
    return IndexedName(prefix, tuple(indices))


def _input(name: str) -> RefExpression:
    return RefExpression(protocol.RefKind.INPUT, _literal(name))


def _occurrence(name: NameExpression) -> RefExpression:
    return RefExpression(protocol.RefKind.OCCURRENCE, name)


def _explicit(*names: NameExpression) -> ExplicitNames:
    return ExplicitNames(tuple(names))


def _common_prelude(initial_claim: str, *, native_oracle: bool) -> tuple[Command, ...]:
    commands: tuple[Command, ...] = (
        DeclareInput(
            _literal("statement"),
            protocol.InputRole.STATEMENT,
            _literal("root"),
            protocol.ValueSort.BYTES,
        ),
        DeclareInput(
            _literal("session"),
            protocol.InputRole.PUBLIC_CONTEXT,
            _literal("root"),
            protocol.ValueSort.BYTES,
        ),
        DeclareInput(
            _literal("field_modulus"),
            protocol.InputRole.PUBLIC_PARAMETER,
            _literal("root"),
            protocol.ValueSort.NAT,
        ),
        DeclareScope(_literal("root"), None, None),
        DeclareInitialClaim(_literal(initial_claim)),
    )
    if native_oracle:
        return (
            *commands,
            DeclareExtension(_literal("native-oracle-v0")),
        )
    return commands


def fri_program(*, grouped: bool) -> CoreProgram:
    fold = LoopValue("fold")
    query = LoopValue("query")
    fold_depth = AxisValue("fold_depth")
    query_count = AxisValue("query_count")
    statement = _input("statement")
    layer_at_fold = _indexed("fri_layer", NatAdd(fold, NatConst(1)))
    query_coin = _indexed("query_coin", query)
    query_name = _indexed("query", query)
    answer = _indexed("answer", query)
    check = _indexed("check", query)
    reduction = _indexed("fri_reduce", query)

    prelude: tuple[Command, ...] = (
        *_common_prelude("fri_claim_0", native_oracle=True),
        EmitOccurrence(
            _indexed("fri_layer", NatConst(0)),
            protocol.OccurrenceKind.ORACLE_PUBLISH,
            oracle_name=_indexed("fri_layer", NatConst(0)),
        ),
    )
    fold_body: tuple[Command, ...] = (
        EmitOccurrence(
            _indexed("fold_coin", fold),
            protocol.OccurrenceKind.CHALLENGE,
            dependencies=(statement,),
            challenge_modulus=NatAdd(NatConst(97), fold),
        ),
        EmitOccurrence(
            layer_at_fold,
            protocol.OccurrenceKind.ORACLE_PUBLISH,
            oracle_name=layer_at_fold,
        ),
    )
    required_challenges = ConcatNames(
        (
            RangeNames("fold_coin", NatConst(0), fold_depth),
            RangeNames("query_coin", NatConst(0), NatAdd(query, NatConst(1))),
        )
    )
    required_publications = PairedNameSequences(
        RangeNames(
            "fri_layer",
            NatConst(0),
            NatAdd(fold_depth, NatConst(1)),
        ),
        ConcatNames(
            (
                RangeNames("fold_coin", NatConst(0), fold_depth),
                _explicit(_indexed("query_coin", NatConst(0))),
            )
        ),
    )
    query_body: tuple[Command, ...] = (
        EmitOccurrence(
            query_coin,
            protocol.OccurrenceKind.CHALLENGE,
            dependencies=(statement,),
            challenge_modulus=NatAdd(NatConst(131), query),
        ),
        EmitOccurrence(
            query_name,
            protocol.OccurrenceKind.ORACLE_QUERY,
            dependencies=(_occurrence(query_coin),),
            oracle_name=_indexed("fri_layer", fold_depth),
        ),
        EmitOccurrence(
            answer,
            protocol.OccurrenceKind.ORACLE_ANSWER,
            dependencies=(_occurrence(query_name),),
            oracle_name=_indexed("fri_layer", fold_depth),
        ),
        EmitOccurrence(
            check,
            protocol.OccurrenceKind.CHECK,
            dependencies=(_occurrence(answer), statement),
            check_predicate=PredicateTemplate(
                protocol.PredicateKind.BYTES_EQUAL,
                (_occurrence(answer), statement),
            ),
        ),
        EmitReduction(
            reduction,
            check,
            _literal("root"),
            _explicit(_indexed("fri_claim", query)),
            (_occurrence(answer), statement),
            required_challenges,
            required_publications,
            _explicit(_indexed("fri_claim", NatAdd(query, NatConst(1)))),
        ),
        EmitClaimUse(_indexed("fri_claim", query), reduction),
    )
    tail: tuple[Command, ...] = (
        EmitOccurrence(_literal("terminal"), protocol.OccurrenceKind.TERMINAL),
        EmitClaimUse(_indexed("fri_claim", query_count), _literal("terminal")),
    )
    repeated: tuple[Command, ...] = (
        Repeat("fold_depth", "fold", fold_body),
        Repeat("query_count", "query", query_body),
    )
    if grouped:
        return CoreProgram((Static(prelude), *repeated, Static(tail)))
    return CoreProgram((*prelude, *repeated, *tail))


def sumcheck_program() -> CoreProgram:
    round_index = LoopValue("round")
    round_count = AxisValue("round_count")
    statement = _input("statement")
    message = _indexed("round_poly", round_index)
    challenge = _indexed("round_coin", round_index)
    check = _indexed("round_check", round_index)
    reduction = _indexed("sumcheck_reduce", round_index)
    body: tuple[Command, ...] = (
        EmitOccurrence(message, protocol.OccurrenceKind.PROVER_MESSAGE),
        EmitOccurrence(
            challenge,
            protocol.OccurrenceKind.CHALLENGE,
            dependencies=(statement, _occurrence(message)),
            challenge_modulus=NatAdd(NatConst(193), round_index),
        ),
        EmitOccurrence(
            check,
            protocol.OccurrenceKind.CHECK,
            dependencies=(_occurrence(message), statement),
            check_predicate=PredicateTemplate(
                protocol.PredicateKind.BYTES_EQUAL,
                (_occurrence(message), statement),
            ),
        ),
        EmitReduction(
            reduction,
            check,
            _literal("root"),
            _explicit(_indexed("sumcheck_claim", round_index)),
            (_occurrence(message), statement),
            _explicit(challenge),
            PairedNameSequences(_explicit(message), _explicit(challenge)),
            _explicit(_indexed("sumcheck_claim", NatAdd(round_index, NatConst(1)))),
        ),
        EmitClaimUse(_indexed("sumcheck_claim", round_index), reduction),
    )
    return CoreProgram(
        (
            Static(_common_prelude("sumcheck_claim_0", native_oracle=False)),
            Repeat("round_count", "round", body),
            Static(
                (
                    EmitOccurrence(
                        _literal("terminal"), protocol.OccurrenceKind.TERMINAL
                    ),
                    EmitClaimUse(
                        _indexed("sumcheck_claim", round_count),
                        _literal("terminal"),
                    ),
                )
            ),
        )
    )


def fri_schema(
    *,
    grouped: bool = True,
    fold_depths: tuple[int, ...] = (2, 3, 4),
    query_counts: tuple[int, ...] = (1, 2),
    bound: ExpansionSize = ExpansionSize(3, 1, 18, 2, 1, 1, 3, 33),
    program: CoreProgram | None = None,
) -> IndexedCoreSchema:
    return IndexedCoreSchema(
        (
            IndexAxis("fold_depth", fold_depths),
            IndexAxis("query_count", query_counts),
        ),
        bound,
        fri_program(grouped=grouped) if program is None else program,
    )


def sumcheck_schema(
    *,
    round_counts: tuple[int, ...] = (1, 2, 4),
    bound: ExpansionSize = ExpansionSize(3, 1, 13, 4, 0, 1, 5, 30),
    program: CoreProgram | None = None,
) -> IndexedCoreSchema:
    return IndexedCoreSchema(
        (IndexAxis("round_count", round_counts),),
        bound,
        sumcheck_program() if program is None else program,
    )


# ---------------------------------------------------------------------------
# Existing Fresh/FS execution and narrow measurement
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class FiberProtocolPair:
    fresh_protocol_id: object
    fiat_shamir_protocol_id: object
    core_id: object
    fresh_terminal: bool
    fiat_shamir_terminal: bool


def _fiber_runtime_inputs(result: CheckedCoreElaborationAt) -> tuple[object, object]:
    core = result.core
    moves: dict[str, object] = {}
    if any(
        item.kind is protocol.OccurrenceKind.ORACLE_PUBLISH for item in core.schedule
    ):
        for item in core.schedule:
            if item.kind is protocol.OccurrenceKind.ORACLE_PUBLISH:
                moves[item.name] = protocol.OracleObject((b"claim",) * 8)
    else:
        for item in core.schedule:
            if item.kind is protocol.OccurrenceKind.PROVER_MESSAGE:
                moves[item.name] = b"claim"
    invocation = protocol.Invocation(
        MappingProxyType(
            {
                "statement": b"claim",
                "session": b"indexed-elaboration",
                "field_modulus": 257,
            }
        )
    )
    return invocation, protocol.ScriptedStrategy(moves)


def execute_fresh_fs_pair(result: CheckedCoreElaborationAt) -> FiberProtocolPair:
    checked = require_live_result(result)
    core = checked.core
    construction = protocol.TranscriptConstruction(b"zkc/indexed-core-elaboration/v1")
    construction_check = protocol.check_fs_construction(core, core, construction)
    if construction_check.kind is not protocol.QualifiedViewOutcomeKind.AFFIRMATIVE:
        raise ElaborationError(
            "existing Fresh/FS construction checker refused the fiber"
        )
    invocation, strategy = _fiber_runtime_inputs(checked)
    fresh_values = {
        item.name: 1
        for item in core.schedule
        if item.kind is protocol.OccurrenceKind.CHALLENGE
    }
    fresh_result = protocol.generate(
        core,
        construction,
        protocol.ChallengeInterpretation.FRESH,
        invocation,
        strategy,
        fresh_resolver=protocol.ScriptedFreshResolver(fresh_values),
    )
    fs_result = protocol.generate(
        core,
        construction,
        protocol.ChallengeInterpretation.FIAT_SHAMIR,
        invocation,
        strategy,
    )
    if (
        type(fresh_result) is not protocol.Completed
        or type(fs_result) is not protocol.Completed
    ):
        raise ElaborationError("selected strategy did not complete the finite fiber")
    evidence = protocol.check_fresh_fs_pair(
        core,
        construction,
        invocation,
        fresh_result.record,
        fs_result.record,
    )
    return FiberProtocolPair(
        protocol.protocol_id(
            core,
            None,
            protocol.ChallengeInterpretation.FRESH,
        ),
        protocol.protocol_id(
            core,
            construction,
            protocol.ChallengeInterpretation.FIAT_SHAMIR,
        ),
        checked.core_id,
        evidence.fresh_terminal,
        evidence.fiat_shamir_terminal,
    )


@dataclass(frozen=True)
class AuthoringMeasurement:
    selected_indices: int
    expanded_occurrences: int
    schema_occurrence_clauses: int
    expansion_minus_schema_clauses: int


def program_occurrence_clause_count(program: CoreProgram) -> int:
    def count(commands: tuple[Command, ...]) -> int:
        return sum(
            1
            if type(command) is EmitOccurrence
            else count(command.commands)
            if type(command) in {Static, Repeat}
            else 0
            for command in commands
        )

    return count(program.commands)


def measure_occurrence_authoring(
    schema: IndexedCoreSchema,
    indices: Iterable[SemanticIndex],
) -> AuthoringMeasurement:
    selected = tuple(indices)
    if not selected:
        raise ElaborationError("measurement needs at least one selected index")
    expanded = sum(predicted_expansion(schema, index).occurrences for index in selected)
    clauses = program_occurrence_clause_count(schema.program)
    return AuthoringMeasurement(
        len(selected),
        expanded,
        clauses,
        expanded - clauses,
    )


def enumerate_indices(schema: IndexedCoreSchema) -> tuple[SemanticIndex, ...]:
    admit_schema(schema)
    return _raw_indices(schema)


def infer_asymptotic_theorem(
    _schema: IndexedCoreSchema,
    _checked_fibers: Iterable[CheckedCoreElaborationAt],
) -> None:
    raise UnsupportedFamilyClaim(
        "finite elaboration witnesses cannot establish an all-index theorem"
    )
