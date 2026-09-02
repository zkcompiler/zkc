#!/usr/bin/env python3
"""Untrusted generator for the provider-observable audit.

The generator reads the exact admitted finite Schnorr Core and Fresh Protocol
through the F0-V2B1 owner-view derivation and emits two artifacts:

- ``generated/Schnorr.lean``: one VCVio-shaped interaction with one construct
  per Core occurrence, the Fresh challenge interpretation, the Check, both
  terminals, and a ``ChallengeVerifyProtocol`` shape binding; and
- ``generated/ledger.json``: every emitted construct mapped to exactly one
  source coordinate of the six normalized owner views, or to a typed
  ``no_source_coordinate`` entry naming the missing observable, why no view
  leaf determines it, what needs it, and where the fact actually lives.

The output carries no authority.  Every fact that no view leaf determines is
left as a Lean parameter and recorded as a gap; the generator never fills such
a hole by reading a semantic-module body, a portable-algorithm preimage, or a
Relations body.  The independent checker in ``checker.py`` decides whether the
ledger is total, injective, valid, and free of invented observables.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass, field
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
B1_MODEL = ROOT / "evaluation/formal-source-view-bodies-f0v2b1/model.py"
GENERATED_LEAN = HERE / "generated" / "Schnorr.lean"
GENERATED_LEDGER = HERE / "generated" / "ledger.json"

LEDGER_FORMAT = "zkc.formal-provider-observables-f2o0.ledger.v0"
MARKER_PREFIX = "-- [f2o0:"
PROVIDER = {
    "name": "VCVio",
    "revision": "de0a3108140e3e04a7ebf0075aa110b459ee6e8a",
    "toolchain": "leanprover/lean4:v4.33.1",
    "imported_module": "VCVio.CryptoFoundations.SigmaProtocol",
    "interaction_monad": "ProbComp (OracleComp unifSpec)",
    "shape": "ChallengeVerifyProtocol",
}

EFFECT_NAMES = {0: "ProverMessage", 2: "Challenge", 3: "InvokeCheck", 5: "ReachTerminal"}
VERDICT_NAMES = {0: "accept", 1: "reject", 2: "abort"}
READ_KINDS = {
    1: ("public-invocation-input", "publicInput"),
    2: ("opened-binding", "openedBinding"),
    3: ("observed-message", "observedMessage"),
    4: ("observed-challenge", "observedChallenge"),
    9: ("prior-own-move", "priorOwnMove"),
}
INTERPRETATION_NAMES = {0: "Fresh"}
ROOT_DOMAIN_KIND = "foundation.root-value-domain"

TARGET = "docs-next/pir/interactive-core.md"
FOUNDATION = "docs-next/foundation/executable-foundations.md"
RELATIONS = "docs-next/relations/relation-model.md"
PLANS = "docs-next/pir/interfaces-and-plans.md"
OWNER_MODEL = "evaluation/formal-source-target-core-f1r1b/reference_model.py"
K1_MODEL = "evaluation/k1-executable-foundations/reference_model.py"
TERMINAL_CONTRACTS = (
    "docs-next/notes/semantic-revalidation-and-redesign/formal-assurance-research/"
    "f0v2b2c1b5b1-terminal-owner-contracts.md"
)
PROVIDER_SIGMA = "VCVio/CryptoFoundations/SigmaProtocol.lean"
PROVIDER_SCHNORR = "Examples/Schnorr/SigmaProtocol.lean"
PROVIDER_SAMPLE = "VCVio/OracleComp/Constructions/SampleableType.lean"
PROVIDER_ORACLE_COMP = "VCVio/OracleComp/OracleComp.lean"


class GeneratorError(ValueError):
    """The generator cannot form its output from the admitted subject."""


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


b1 = _load_module("_zkc_f2o0_generator_b1_model", B1_MODEL)
owner = b1.owner
k1 = owner.k1


def _steps(spec: str) -> tuple[tuple[str, int], ...]:
    kinds = {"f": "field", "s": "sequence", "v": "variant"}
    result: list[tuple[str, int]] = []
    for token in spec.split():
        if len(token) < 2 or token[0] not in kinds or not token[1:].isdigit():
            raise GeneratorError(f"malformed path spec {spec!r}")
        result.append((kinds[token[0]], int(token[1:])))
    return tuple(result)


class ViewUniverse:
    """Exact view values plus the complete active-leaf manifests of B1."""

    def __init__(self, values: dict[str, Any], manifests: dict[str, Any]) -> None:
        self.values = values
        self.manifests = manifests
        self._index: dict[str, dict[tuple[tuple[str, int], ...], dict[str, Any]]] = {}
        for view, coordinates in manifests.items():
            table: dict[tuple[tuple[str, int], ...], dict[str, Any]] = {}
            for coordinate in coordinates:
                key = tuple(
                    (step["step"], step["ordinal"]) for step in coordinate["path"]
                )
                if key in table:
                    raise GeneratorError("B1 manifest repeats a coordinate")
                table[key] = coordinate
            self._index[view] = table

    def coordinate(self, view: str, spec: str) -> dict[str, Any]:
        table = self._index.get(view)
        if table is None:
            raise GeneratorError(f"unknown view {view}")
        coordinate = table.get(_steps(spec))
        if coordinate is None:
            raise GeneratorError(f"no active leaf at {view} {spec}")
        return copy.deepcopy(coordinate)

    def node(self, view: str, spec: str) -> Any:
        current: Any = self.values[view]
        for step, ordinal in _steps(spec):
            if step == "field":
                if type(current) is not dict or ordinal not in current:
                    raise GeneratorError(f"no field {ordinal} at {view} {spec}")
                current = current[ordinal]
            elif step == "sequence":
                if type(current) is not list or ordinal >= len(current):
                    raise GeneratorError(f"no element {ordinal} at {view} {spec}")
                current = current[ordinal]
            else:
                if type(current) is not dict or current.get("case") != ordinal:
                    raise GeneratorError(f"variant case {ordinal} absent at {view} {spec}")
                current = current["value"]
        return current

    def leaf(self, view: str, spec: str) -> tuple[dict[str, Any], Any]:
        return self.coordinate(view, spec), self.node(view, spec)


def _decode(leaf: Any) -> Any:
    if type(leaf) is not dict or set(leaf) != {"compiler", "body"}:
        raise GeneratorError("leaf is not a canonical body")
    try:
        return k1.decode_datum(bytes.fromhex(leaf["body"]))
    except Exception as error:
        raise GeneratorError(f"leaf body does not decode: {error}") from error


def _nat(leaf: Any) -> int:
    datum = _decode(leaf)
    if type(datum) is not k1.Nat:
        raise GeneratorError("ordinal leaf is not a natural datum")
    return datum.value


def _value_ref(leaf: Any) -> tuple[Any, ...]:
    datum = _decode(leaf)
    if type(datum) is not k1.DatumVariant:
        raise GeneratorError("value reference leaf is not a variant datum")
    if datum.case == 0 and type(datum.payload) is k1.Nat:
        return ("PublicInput", datum.payload.value)
    if datum.case == 4 and type(datum.payload) is k1.DatumRecord:
        fields = dict(datum.payload.fields)
        return ("OccurrenceOutput", fields[0].value, fields[1].value)
    raise GeneratorError("value reference is outside the finite Schnorr slice")


def _value_type(leaf: Any) -> dict[str, int]:
    datum = _decode(leaf)
    if type(datum) is not k1.DatumRecord:
        raise GeneratorError("value type leaf is not a record datum")
    fields = dict(datum.fields)
    domain = fields[0]
    schema = fields[1]
    if (
        type(domain) is not k1.DatumVariant
        or domain.case != 0
        or type(domain.payload) is not k1.DatumRecord
    ):
        raise GeneratorError("value type domain is not a root declaration")
    domain_fields = dict(domain.payload.fields)
    if domain_fields[1] != k1.Symbol(ROOT_DOMAIN_KIND):
        raise GeneratorError("value type domain kind is not the root value domain")
    if type(schema) is not k1.DatumVariant:
        raise GeneratorError("value type schema is not a variant datum")
    bound = schema.payload.value if type(schema.payload) is k1.Nat else None
    return {
        "root_domain_ordinal": domain_fields[2].value,
        "schema_case": schema.case,
        "schema_bound": bound,
    }


def _carrier(value_type: dict[str, int]) -> str:
    """Rendering rule: root nat with bound m is Fin (m + 1); root bool is Bool."""

    if value_type["root_domain_ordinal"] == 2 and value_type["schema_case"] == 2:
        return f"Fin {value_type['schema_bound'] + 1}"
    if value_type["root_domain_ordinal"] == 1 and value_type["schema_case"] == 1:
        return "Bool"
    raise GeneratorError("value type has no declared Lean carrier rendering")


def _module_ref(leaf: Any) -> dict[str, Any]:
    datum = _decode(leaf)
    if (
        type(datum) is not k1.DatumVariant
        or datum.case != 1
        or type(datum.payload) is not k1.DatumRecord
    ):
        raise GeneratorError("module declaration reference has another shape")
    fields = dict(datum.payload.fields)
    return {
        "module": _content_ref_carrier(fields[0].value),
        "declaration_kind": fields[1].value,
        "local_ordinal": fields[2].value,
    }


def _guard(leaf: Any) -> dict[str, Any]:
    datum = _decode(leaf)
    if type(datum) is not k1.DatumVariant:
        raise GeneratorError("guard leaf is not a variant datum")
    if datum.case == 0:
        return {"guard": "Always"}
    if datum.case == 1 and type(datum.payload) is k1.DatumRecord:
        fields = dict(datum.payload.fields)
        return {
            "guard": "Evaluate",
            "algorithm": _content_ref_carrier(fields[0].value),
            "evaluation_contract": _content_ref_carrier(fields[1].value),
            "inputs": [_value_ref_datum(item) for item in fields[2].values],
        }
    raise GeneratorError("guard constructor is outside the finite Schnorr slice")


def _value_ref_datum(datum: Any) -> list[Any]:
    if type(datum) is k1.DatumVariant and datum.case == 0:
        return ["PublicInput", datum.payload.value]
    if type(datum) is k1.DatumVariant and datum.case == 4:
        fields = dict(datum.payload.fields)
        return ["OccurrenceOutput", fields[0].value, fields[1].value]
    raise GeneratorError("value reference datum is outside the finite Schnorr slice")


def _content_ref_carrier(reference: bytes) -> str:
    """Render a framed ContentRefV0 as its diagnostic carrier text."""

    frames: list[bytes] = []
    offset = 0
    while len(frames) < 5:
        if offset + 8 > len(reference):
            raise GeneratorError("content reference is truncated")
        length = int.from_bytes(reference[offset : offset + 8], "big")
        offset += 8
        frames.append(reference[offset : offset + length])
        offset += length
    digest = reference[offset:]
    if len(digest) != 32:
        raise GeneratorError("content reference digest has the wrong length")
    return f"zkcidv0:{frames[3].decode('ascii')}:{digest.hex()}"


def _identifier_carrier(leaf: Any) -> str:
    if type(leaf) is not dict or set(leaf) != {"compiler", "body"}:
        raise GeneratorError("identifier leaf is not a canonical body")
    return _content_ref_carrier(bytes.fromhex(leaf["body"]))


@dataclass
class Construct:
    id: str
    kind: str
    layer: str
    lean_name: str
    lean_text: str
    source: dict[str, Any]
    consulted: list[dict[str, Any]] = field(default_factory=list)
    realizes: dict[str, Any] | None = None
    trailing: list[str] = field(default_factory=list)


@dataclass
class Draft:
    """Constructs and layout before rendering; mutations edit this."""

    constructs: dict[str, Construct]
    layout: list[tuple[str, str]]
    subject: dict[str, Any]
    universe: ViewUniverse
    premises: list[dict[str, Any]]
    rendering_rules: list[dict[str, str]]
    lean_edits: list[tuple[str, str]] = field(default_factory=list)
    ledger_edits: list[Any] = field(default_factory=list)


def load_subject() -> dict[str, Any]:
    core, protocol = b1.admitted_handles()
    candidate = b1.build_candidate(core, protocol)
    return {
        "core_id": core.core_id.carrier(),
        "protocol_id": protocol.protocol_id.carrier(),
        "source_digest": candidate["source_digest"],
        "values": candidate["values"],
        "manifests": candidate["requested_manifests"],
    }


def _gap(
    gap_class: str,
    reason: str,
    needed_for: str,
    lives_in: list[str],
    named_by: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    return {
        "no_source_coordinate": {
            "class": gap_class,
            "reason": reason,
            "needed_for": needed_for,
            "named_by": named_by or [],
            "lives_in": lives_in,
        }
    }


def _sourced(coordinate: dict[str, Any]) -> dict[str, Any]:
    return {"coordinate": coordinate}


def draft(subject: dict[str, Any] | None = None) -> Draft:
    subject = subject or load_subject()
    universe = ViewUniverse(subject["values"], subject["manifests"])
    constructs: dict[str, Construct] = {}
    layout: list[tuple[str, str]] = []

    def raw(text: str = "") -> None:
        layout.append(("raw", text))

    def add(construct: Construct) -> None:
        if construct.id in constructs:
            raise GeneratorError(f"duplicate construct {construct.id}")
        constructs[construct.id] = construct
        layout.append(("construct", construct.id))

    effect_view = universe.values["EffectView"]
    strategy_view = universe.values["StrategyDecisionView"]
    coin_view = universe.values["PublicCoinView"]
    execution_view = universe.values["ExecutionView"]

    # Occurrence schedule from the EffectView occurrence table.
    occurrences: list[dict[str, Any]] = []
    for ordinal, row in enumerate(effect_view[1]):
        if _nat(row[0]) != ordinal:
            raise GeneratorError("occurrence row ordinal disagrees with its ref")
        effect_case = row[3]["case"]
        if effect_case not in EFFECT_NAMES:
            raise GeneratorError("effect constructor is outside the finite slice")
        entry: dict[str, Any] = {
            "ordinal": ordinal,
            "effect_case": effect_case,
            "effect": EFFECT_NAMES[effect_case],
            "guard": _guard(row[2]),
            "output_types": [_value_type(item) for item in row[4]],
        }
        if effect_case == 0:
            entry["channel"] = _module_ref(row[3]["value"][0])
            entry["payload_type"] = _value_type(row[3]["value"][1])
        else:
            entry["target"] = _nat(row[3]["value"])
        occurrences.append(entry)

    value_rows = {
        _value_ref(row[0]): (index, _value_type(row[1]))
        for index, row in enumerate(effect_view[2])
    }
    public_inputs = sorted(
        key[1] for key in value_rows if key[0] == "PublicInput"
    )
    if public_inputs != [0]:
        raise GeneratorError("the finite slice has exactly one public input")
    input_row, input_type = value_rows[("PublicInput", 0)]
    output_rows = {
        (key[1], key[2]): value_rows[key]
        for key in value_rows
        if key[0] == "OccurrenceOutput"
    }

    def variable_name(reference: tuple[Any, ...]) -> str:
        if reference[0] == "PublicInput":
            return f"publicInput{reference[1]}"
        occurrence = occurrences[reference[1]]
        prefix = {
            "ProverMessage": "msg",
            "Challenge": "chal",
            "InvokeCheck": "chk",
        }[occurrence["effect"]]
        suffix = f"_{reference[2]}" if reference[2] else ""
        return f"{prefix}{reference[1]}{suffix}"

    # Value carriers.
    carriers: dict[str, tuple[str, dict[str, Any], str]] = {}

    def carrier_alias(value_type: dict[str, int]) -> str:
        rendering = _carrier(value_type)
        if rendering.startswith("Fin "):
            return f"Z{rendering.split()[1]}"
        return "CheckOutput" if rendering == "Bool" else rendering

    z_alias = carrier_alias(input_type)
    carriers[z_alias] = (
        _carrier(input_type),
        universe.coordinate("EffectView", f"f2 s{input_row} f1"),
        "type.z3",
    )
    check_rows = list(enumerate(effect_view[5]))
    if len(check_rows) != 1:
        raise GeneratorError("the finite slice has exactly one Check")
    check_ordinal, check_row = check_rows[0]
    check_occurrence = _nat(check_row[4])
    check_inputs = [_value_ref(item) for item in check_row[3]]
    check_output_row, check_output_type = output_rows[(check_occurrence, 0)]
    bool_alias = carrier_alias(check_output_type)
    carriers[bool_alias] = (
        _carrier(check_output_type),
        universe.coordinate("EffectView", f"f2 s{check_output_row} f1"),
        "type.bool",
    )

    # Header.
    raw("/-")
    raw("Generated by evaluation/formal-provider-observables-f2o0/generator.py from")
    raw("the admitted F1-R1B subject through the F0-V2B1 owner views. UNTRUSTED")
    raw("OUTPUT. It states one VCVio-shaped interaction that is parametric in exactly")
    raw("the observables no owner view carries. Each construct line ends with a")
    raw("ledger marker `-- [f2o0:<id>]`; generated/ledger.json maps every marker to")
    raw("one source coordinate or to a typed no_source_coordinate entry.")
    raw("")
    raw("Subject:")
    raw(f"  Core      {subject['core_id']}")
    raw(f"  Protocol  {subject['protocol_id']}")
    raw("Provider:")
    raw(f"  {PROVIDER['name']} {PROVIDER['revision']}, {PROVIDER['toolchain']},")
    raw(f"  imported module {PROVIDER['imported_module']}")
    raw("-/")
    raw(f"import {PROVIDER['imported_module']}")
    raw("")
    raw("open OracleComp")
    raw("")
    raw("namespace ZkcF2O0")
    raw("")
    raw("/-! ### Subject identity -/")
    raw("")
    core_leaf = universe.leaf("EffectView", "f0")
    add(
        Construct(
            "subject.core",
            "subject-identity",
            "interaction",
            "coreIdBody",
            f'def coreIdBody : String := "{core_leaf[1]["body"]}"',
            _sourced(core_leaf[0]),
        )
    )
    protocol_leaf = universe.leaf("ExecutionView", "f0")
    add(
        Construct(
            "subject.protocol",
            "subject-identity",
            "interaction",
            "protocolIdBody",
            f'def protocolIdBody : String := "{protocol_leaf[1]["body"]}"',
            _sourced(protocol_leaf[0]),
        )
    )
    raw("")
    raw("/-! ### Value carriers")
    raw("Rendering rule (declared in the ledger): a root `nat` value type with schema")
    raw("bound `m` is carried by `Fin (m + 1)`; the root `bool` value type by `Bool`. -/")
    raw("")
    for alias, (rendering, coordinate, construct_id) in carriers.items():
        add(
            Construct(
                construct_id,
                "value-carrier",
                "interaction",
                alias,
                f"abbrev {alias} : Type := {rendering}",
                _sourced(coordinate),
            )
        )

    # Prover decision interface.
    raw("")
    raw("/-! ### Prover decision interface (StrategyDecisionView) -/")
    decisions: list[dict[str, Any]] = []
    for index, row in enumerate(strategy_view[1]):
        decisions.append(
            {
                "index": index,
                "decision": _nat(row[0]),
                "occurrence": _nat(row[1]),
                "move_type": _value_type(row[4]["value"]),
                "prior": [_nat(item) for item in row[5]],
            }
        )
    reads: list[dict[str, Any]] = []
    for index, row in enumerate(strategy_view[3]):
        case = row[1]["case"]
        if case not in READ_KINDS:
            raise GeneratorError("read coordinate kind is outside the finite slice")
        reads.append(
            {
                "index": index,
                "decision": _nat(row[0]),
                "case": case,
                "kind": READ_KINDS[case][0],
                "field": f"{READ_KINDS[case][1]}{_nat(row[1]['value'])}",
                "target": _nat(row[1]["value"]),
                "type": _value_type(row[2]),
            }
        )
    legal_moves = {
        _nat(row[0]): (index, _value_type(row[1]["value"]))
        for index, row in enumerate(strategy_view[4])
    }
    for decision in decisions:
        raw("")
        raw(
            f"/-- Guaranteed reads at decision point {decision['decision']} "
            f"(occurrence {decision['occurrence']}). -/"
        )
        raw(f"structure ProverView{decision['decision']} where")
        for read in reads:
            if read["decision"] != decision["decision"]:
                continue
            add(
                Construct(
                    f"read.{read['decision']}.{read['kind']}.{read['target']}",
                    "prover-read",
                    "interaction",
                    read["field"],
                    f"  {read['field']} : {carrier_alias(read['type'])}",
                    _sourced(
                        universe.coordinate(
                            "StrategyDecisionView",
                            f"f3 s{read['index']} f1 v{read['case']}",
                        )
                    ),
                    consulted=[
                        universe.coordinate(
                            "StrategyDecisionView", f"f3 s{read['index']} f2"
                        )
                    ],
                    realizes={
                        "decision": read["decision"],
                        "read": read["kind"],
                        "target": read["target"],
                    },
                )
            )
    raw("")
    raw("/-- One field per Prover decision point; the result type is the legal move type. -/")
    raw("structure Prover where")
    for decision in decisions:
        move_index, move_type = legal_moves[decision["decision"]]
        consulted = [
            universe.coordinate("StrategyDecisionView", f"f1 s{decision['index']} f1"),
            universe.coordinate("StrategyDecisionView", f"f1 s{decision['index']} f3"),
            universe.coordinate(
                "StrategyDecisionView", f"f1 s{decision['index']} f4 v0"
            ),
            universe.coordinate("StrategyDecisionView", f"f4 s{move_index} f1 v0"),
        ]
        consulted.extend(
            universe.coordinate(
                "StrategyDecisionView", f"f1 s{decision['index']} f5 s{position}"
            )
            for position in range(len(decision["prior"]))
        )
        add(
            Construct(
                f"decision.{decision['decision']}",
                "prover-decision",
                "interaction",
                f"decide{decision['decision']}",
                f"  decide{decision['decision']} : ProverView{decision['decision']} "
                f"→ ProbComp {carrier_alias(move_type)}",
                _sourced(
                    universe.coordinate(
                        "StrategyDecisionView", f"f1 s{decision['index']} f0"
                    )
                ),
                consulted=consulted,
                realizes={
                    "decision": decision["decision"],
                    "occurrence": decision["occurrence"],
                },
            )
        )

    # Terminal verdicts.
    raw("")
    raw("/-! ### Terminal verdicts declared by the Core -/")
    raw("")
    raw("inductive Verdict where")
    terminals: list[dict[str, Any]] = []
    for index, row in enumerate(effect_view[6]):
        verdict_case = row[1]["case"]
        terminal = {
            "index": index,
            "terminal": _nat(row[0]),
            "verdict_case": verdict_case,
            "verdict": VERDICT_NAMES[verdict_case],
            "required_checks": [_nat(item) for item in row[3]],
            "occurrence": _nat(row[5]),
        }
        terminals.append(terminal)
        add(
            Construct(
                f"terminal.{terminal['terminal']}.verdict",
                "terminal-verdict",
                "interaction",
                terminal["verdict"],
                f"  | {terminal['verdict']}",
                _sourced(
                    universe.coordinate("EffectView", f"f6 s{index} f1 v{verdict_case}")
                ),
                consulted=[universe.coordinate("EffectView", f"f6 s{index} f5")],
                realizes={"terminal": terminal["terminal"], "verdict": terminal["verdict"]},
            )
        )
    raw("  deriving DecidableEq, Repr")

    # Challenge interpretation.
    interpretation_case = execution_view[2]["case"]
    interpretation = INTERPRETATION_NAMES.get(interpretation_case)
    if interpretation != "Fresh":
        raise GeneratorError("the Protocol is not a Fresh interpretation")
    challenge_rows = list(enumerate(coin_view[4]))
    resolver_rows = list(enumerate(execution_view[4]))
    if len(challenge_rows) != 1 or len(resolver_rows) != 1:
        raise GeneratorError("the finite slice has exactly one Challenge")
    challenge_index, challenge_row = challenge_rows[0]
    resolver_index, resolver_row = resolver_rows[0]
    challenge_ref = _nat(challenge_row[0])
    challenge_type = _value_type(challenge_row[3])
    domain_ref = _module_ref(challenge_row[4])
    law_ref = _module_ref(challenge_row[5])
    challenge_alias = carrier_alias(challenge_type)
    raw("")
    raw("/-! ### Challenge interpretation -/")
    raw("")
    raw("/-- Fresh interpretation: challenge 0 is a runtime sample, so its provider type")
    raw("is a probabilistic computation rather than a function of the transcript. -/")
    add(
        Construct(
            f"challenge.{challenge_ref}.interpretation",
            "challenge-interpretation",
            "interaction",
            f"FreshChallenge{challenge_ref}",
            f"abbrev FreshChallenge{challenge_ref} : Type := ProbComp {challenge_alias}",
            _sourced(universe.coordinate("ExecutionView", f"f2 v{interpretation_case}")),
            consulted=[
                universe.coordinate("ExecutionView", "f7 v0"),
                universe.coordinate("ExecutionView", f"f4 s{resolver_index} f0"),
                universe.coordinate("ExecutionView", f"f4 s{resolver_index} f1"),
                universe.coordinate("ExecutionView", f"f4 s{resolver_index} f2"),
                universe.coordinate("PublicCoinView", f"f4 s{challenge_index} f3"),
            ],
            realizes={"challenge": challenge_ref, "interpretation": interpretation},
        )
    )

    # Observables without a source coordinate: the interaction's parameters.
    raw("")
    raw("/-! ### Observables with no source coordinate")
    raw("Each parameter below is an observable that a provider interpretation needs and")
    raw("that no owner-view leaf determines; the ledger records why and where it lives. -/")
    raw("")
    raw("section Observables")
    raw("")
    law_named_by = [
        universe.coordinate("PublicCoinView", f"f4 s{challenge_index} f4"),
        universe.coordinate("PublicCoinView", f"f4 s{challenge_index} f5"),
        universe.coordinate("ExecutionView", f"f4 s{resolver_index} f3"),
        universe.coordinate("ExecutionView", f"f4 s{resolver_index} f4"),
    ]
    add(
        Construct(
            f"challenge.{challenge_ref}.law",
            "distribution",
            "interaction",
            f"freshLaw{challenge_ref}",
            f"variable (freshLaw{challenge_ref} : FreshChallenge{challenge_ref})",
            _gap(
                "operational-distribution",
                "The six views carry the Fresh interpretation, the challenge's value "
                f"type ({_carrier(challenge_type)}), and nominal references to the "
                f"declarations {domain_ref['declaration_kind']} #"
                f"{domain_ref['local_ordinal']} and {law_ref['declaration_kind']} #"
                f"{law_ref['local_ordinal']} of module {law_ref['module']}. No leaf "
                "carries the distribution those references denote; the referenced "
                "declaration bodies are nominal symbols (finite-additive-z3, "
                "fresh-uniform-z3) whose formation, by the target text, proves no "
                "distribution.",
                f"occurrence.{occurrences_of_challenge(occurrences, challenge_ref)} "
                "(the sampling step) and the provider's challenge draw, which "
                "ChallengeVerifyProtocol.PerfectlyComplete fixes as `$ᵗ Chal`, the "
                "uniform draw of SampleableType",
                [
                    f"{TARGET} Section 5.2: the Fresh law denotes a distribution "
                    "independent of prover-controlled history; distribution truth is "
                    "an Analysis/evidence obligation",
                    f"{TARGET} Section 12.1: FreshResolver obtains one value from a "
                    "scoped public-coin capability; source identity proves no "
                    "distribution",
                    f"{TARGET} Section 2: a nominal ProtocolDeclarationRef proves no "
                    "distribution",
                    f"{OWNER_MODEL} protocol_module: the nominal declaration bodies "
                    "finite-additive-z3 and fresh-uniform-z3",
                    f"{PROVIDER_SIGMA} PerfectlyComplete and {PROVIDER_SAMPLE}: the "
                    "provider-side uniform draw",
                ],
                law_named_by,
            ),
            realizes={"challenge": challenge_ref},
        )
    )
    check_algorithm = _identifier_carrier(check_row[1])
    check_contract = _identifier_carrier(check_row[2])
    check_signature = " → ".join(
        carrier_alias(value_rows[item][1]) for item in check_inputs
    )
    add(
        Construct(
            f"check.{check_ordinal}.denotation",
            "denotation",
            "interaction",
            f"check{check_ordinal}",
            f"variable (check{check_ordinal} : {check_signature} → {bool_alias})",
            _gap(
                "operational-denotation",
                "The views carry the Check's portable-algorithm identity "
                f"({check_algorithm}), its evaluation contract ({check_contract}), "
                f"its {len(check_inputs)} ordered input value references, and its "
                "Boolean output type. No leaf carries the algorithm's term; the "
                "identity is a content reference to a K1 portable-algorithm "
                "preimage that lives outside every view.",
                f"occurrence.{check_occurrence} (the Check step) and "
                "ChallengeVerifyProtocol.verify",
                [
                    f"{OWNER_MODEL} finite_schnorr_algorithm: the authenticated "
                    "179,147-octet preimage",
                    f"{K1_MODEL} Evaluator.evaluate: the evaluation semantics",
                    f"{FOUNDATION} Sections 5.1, 5.2, and 7.2: denotation boundary, "
                    "canonical calculus, evaluation contract",
                    f"{TARGET} Section 6.1: Checks",
                ],
                [
                    universe.coordinate("EffectView", f"f5 s{check_ordinal} f1"),
                    universe.coordinate("EffectView", f"f5 s{check_ordinal} f2"),
                ],
            ),
            consulted=[
                universe.coordinate("EffectView", f"f5 s{check_ordinal} f3 s{position}")
                for position in range(len(check_inputs))
            ]
            + [universe.coordinate("EffectView", f"f2 s{check_output_row} f1")],
            realizes={"check": check_ordinal},
        )
    )
    guarded = [
        item
        for item in occurrences
        if item["effect"] == "ReachTerminal" and item["guard"]["guard"] == "Evaluate"
    ]
    if len(guarded) != 1:
        raise GeneratorError("the finite slice has exactly one guarded terminal")
    guard_occurrence = guarded[0]
    guard = guard_occurrence["guard"]
    guard_inputs = guard["inputs"]
    guard_signature = " → ".join(
        carrier_alias(output_rows[(item[1], item[2])][1]) for item in guard_inputs
    )
    add(
        Construct(
            f"guard.{guard_occurrence['ordinal']}.denotation",
            "denotation",
            "interaction",
            f"guard{guard_occurrence['ordinal']}",
            f"variable (guard{guard_occurrence['ordinal']} : {guard_signature} → Bool)",
            _gap(
                "operational-denotation",
                "The views carry the Accept terminal's guard as one opaque "
                "guard-body-v0 leaf; decoded under the codec premise it names the "
                f"portable algorithm {guard['algorithm']}, the evaluation contract "
                f"{guard['evaluation_contract']}, and the input "
                f"{guard_inputs[0]}. No leaf carries that algorithm's term, and no "
                "view states that the guard's truth equals the required Check's "
                "truth.",
                f"occurrence.{guard_occurrence['ordinal']} (first-active guarded "
                "Accept) and ChallengeVerifyProtocol.verify",
                [
                    f"{OWNER_MODEL} boolean_identity_algorithm: the authenticated "
                    "preimage",
                    f"{TARGET} Sections 5.1 and 6.4: Guards; terminal required checks",
                    f"{TERMINAL_CONTRACTS}: the later selected Check-use predicate, "
                    "absent from the B1 views",
                ],
                [universe.coordinate("EffectView", f"f1 s{guard_occurrence['ordinal']} f2")],
            ),
            realizes={"occurrence": guard_occurrence["ordinal"], "role": "guard"},
        )
    )

    # The interaction.
    raw("")
    raw("/-! ### The interaction: one step per Core occurrence in schedule order -/")
    raw("")
    raw("def interaction")
    add(
        Construct(
            "strategy.parameter",
            "strategy-parameter",
            "interaction",
            "prover",
            "    (prover : Prover)",
            _sourced(universe.coordinate("StrategyDecisionView", "f2")),
            consulted=[
                universe.coordinate("StrategyDecisionView", f"f4 s{index} f0")
                for index in range(len(strategy_view[4]))
            ],
        )
    )
    add(
        Construct(
            "input.public.0",
            "public-input",
            "interaction",
            "publicInput0",
            f"    (publicInput0 : {z_alias})",
            _sourced(universe.coordinate("EffectView", f"f2 s{input_row} f0")),
            consulted=[
                universe.coordinate("PublicBindingView", "f2 s0 f3"),
                universe.coordinate("PublicBindingView", "f2 s0 f4"),
            ],
            realizes={"public_input": 0},
        )
    )
    raw("    : ProbComp Verdict := do")
    read_by_decision = {
        decision["decision"]: [
            read for read in reads if read["decision"] == decision["decision"]
        ]
        for decision in decisions
    }

    def read_value(read: dict[str, Any]) -> str:
        if read["kind"] == "public-invocation-input":
            return f"publicInput{read['target']}"
        if read["kind"] == "opened-binding":
            binding_value = _value_ref(universe.node("PublicBindingView", "f2 s0 f3"))
            return variable_name(binding_value)
        if read["kind"] in ("observed-message", "observed-challenge"):
            return variable_name(("OccurrenceOutput", read["target"], 0))
        if read["kind"] == "prior-own-move":
            return variable_name(("OccurrenceOutput", read["target"], 0))
        raise GeneratorError("unknown read kind")

    fallback_pending: Construct | None = None
    for occurrence in occurrences:
        ordinal = occurrence["ordinal"]
        row = f"f1 s{ordinal}"
        if occurrence["effect"] == "ProverMessage":
            reads_here = read_by_decision[ordinal]
            arguments = ", ".join(read_value(read) for read in reads_here)
            name = variable_name(("OccurrenceOutput", ordinal, 0))
            add(
                Construct(
                    f"occurrence.{ordinal}",
                    "occurrence-step",
                    "interaction",
                    name,
                    f"  let {name} ← prover.decide{ordinal} ⟨{arguments}⟩",
                    _sourced(universe.coordinate("EffectView", f"{row} f3 v0 f0")),
                    consulted=[
                        universe.coordinate("EffectView", f"{row} f3 v0 f1"),
                        universe.coordinate("EffectView", f"{row} f4 s0"),
                        universe.coordinate("EffectView", f"{row} f2"),
                    ]
                    + [
                        universe.coordinate(
                            "StrategyDecisionView", f"f3 s{read['index']} f1 v{read['case']}"
                        )
                        for read in reads_here
                    ],
                    realizes={
                        "occurrence": ordinal,
                        "effect": "ProverMessage",
                        "decision": ordinal,
                        "realization": "strategy-move",
                    },
                )
            )
        elif occurrence["effect"] == "Challenge":
            name = variable_name(("OccurrenceOutput", ordinal, 0))
            add(
                Construct(
                    f"occurrence.{ordinal}",
                    "occurrence-step",
                    "interaction",
                    name,
                    f"  let {name} ← freshLaw{occurrence['target']}",
                    _sourced(universe.coordinate("EffectView", f"{row} f3 v2")),
                    consulted=[
                        universe.coordinate("EffectView", f"{row} f4 s0"),
                        universe.coordinate("EffectView", f"{row} f2"),
                        universe.coordinate("PublicCoinView", f"f4 s{challenge_index} f1"),
                    ],
                    realizes={
                        "occurrence": ordinal,
                        "effect": "Challenge",
                        "challenge": occurrence["target"],
                        "realization": "sample",
                        "samples_from": f"challenge.{occurrence['target']}.law",
                    },
                )
            )
        elif occurrence["effect"] == "InvokeCheck":
            name = variable_name(("OccurrenceOutput", ordinal, 0))
            arguments = " ".join(variable_name(item) for item in check_inputs)
            add(
                Construct(
                    f"occurrence.{ordinal}",
                    "occurrence-step",
                    "interaction",
                    name,
                    f"  let {name} : {bool_alias} := check{occurrence['target']} {arguments}",
                    _sourced(universe.coordinate("EffectView", f"{row} f3 v3")),
                    consulted=[
                        universe.coordinate("EffectView", f"{row} f4 s0"),
                        universe.coordinate("EffectView", f"{row} f2"),
                    ]
                    + [
                        universe.coordinate(
                            "EffectView", f"f5 s{occurrence['target']} f3 s{position}"
                        )
                        for position in range(len(check_inputs))
                    ],
                    realizes={
                        "occurrence": ordinal,
                        "effect": "InvokeCheck",
                        "check": occurrence["target"],
                        "realization": "denotation-application",
                    },
                )
            )
        else:
            terminal = next(
                item for item in terminals if item["terminal"] == occurrence["target"]
            )
            if occurrence["guard"]["guard"] == "Evaluate":
                guard_arguments = " ".join(
                    variable_name(tuple(item)) for item in occurrence["guard"]["inputs"]
                )
                add(
                    Construct(
                        f"occurrence.{ordinal}",
                        "occurrence-step",
                        "interaction",
                        f"terminal{occurrence['target']}",
                        f"  if guard{ordinal} {guard_arguments} then",
                        _sourced(universe.coordinate("EffectView", f"{row} f3 v5")),
                        consulted=[
                            universe.coordinate("EffectView", f"{row} f2"),
                            universe.coordinate(
                                "EffectView", f"f6 s{terminal['index']} f1 v{terminal['verdict_case']}"
                            ),
                        ]
                        + [
                            universe.coordinate(
                                "EffectView", f"f6 s{terminal['index']} f3 s{position}"
                            )
                            for position in range(len(terminal["required_checks"]))
                        ],
                        realizes={
                            "occurrence": ordinal,
                            "effect": "ReachTerminal",
                            "terminal": occurrence["target"],
                            "verdict": terminal["verdict"],
                            "realization": "guarded-terminal",
                        },
                        trailing=[f"    return Verdict.{terminal['verdict']}"],
                    )
                )
                fallback_pending = None
            else:
                if fallback_pending is not None:
                    raise GeneratorError("two unconditional terminals in the slice")
                raw("  else")
                add(
                    Construct(
                        f"occurrence.{ordinal}",
                        "occurrence-step",
                        "interaction",
                        f"terminal{occurrence['target']}",
                        f"    return Verdict.{terminal['verdict']}",
                        _sourced(universe.coordinate("EffectView", f"{row} f3 v5")),
                        consulted=[
                            universe.coordinate("EffectView", f"{row} f2"),
                            universe.coordinate(
                                "EffectView", f"f6 s{terminal['index']} f1 v{terminal['verdict_case']}"
                            ),
                        ],
                        realizes={
                            "occurrence": ordinal,
                            "effect": "ReachTerminal",
                            "terminal": occurrence["target"],
                            "verdict": terminal["verdict"],
                            "realization": "fallback-terminal",
                        },
                    )
                )

    # Provider shape.
    raw("")
    raw("/-! ### Provider shape: ChallengeVerifyProtocol type parameters and fields -/")
    raw("")
    message_rows = {
        _nat(row[0]): (index, _module_ref(row[2]), _value_type(row[3]))
        for index, row in enumerate(effect_view[3])
    }
    message_occurrences = sorted(message_rows)
    if len(message_occurrences) != 2:
        raise GeneratorError("the finite slice has exactly two Prover messages")
    commit_occurrence, response_occurrence = message_occurrences
    commit_index, _commit_channel, commit_type = message_rows[commit_occurrence]
    response_index, _response_channel, response_type = message_rows[response_occurrence]
    binding_class_case = universe.node("PublicBindingView", "f2 s0 f2")["case"]
    if binding_class_case != 0:
        raise GeneratorError("the public binding is not a Statement binding")
    add(
        Construct(
            "provider.statement-type",
            "provider-type-parameter",
            "provider-shape",
            "Stmt",
            f"abbrev Stmt : Type := {z_alias}",
            _sourced(universe.coordinate("PublicBindingView", "f2 s0 f2 v0")),
            consulted=[
                universe.coordinate("PublicBindingView", "f2 s0 f3"),
                universe.coordinate("PublicBindingView", "f2 s0 f4"),
            ],
            realizes={"provider_parameter": "Stmt"},
        )
    )
    add(
        Construct(
            "provider.commit-type",
            "provider-type-parameter",
            "provider-shape",
            "Commit",
            f"abbrev Commit : Type := {carrier_alias(commit_type)}",
            _sourced(universe.coordinate("EffectView", f"f3 s{commit_index} f3")),
            consulted=[universe.coordinate("EffectView", f"f3 s{commit_index} f0")],
            realizes={"provider_parameter": "Commit", "occurrence": commit_occurrence},
        )
    )
    add(
        Construct(
            "provider.challenge-type",
            "provider-type-parameter",
            "provider-shape",
            "Chal",
            f"abbrev Chal : Type := {challenge_alias}",
            _sourced(universe.coordinate("PublicCoinView", f"f4 s{challenge_index} f3")),
            consulted=[universe.coordinate("PublicCoinView", f"f4 s{challenge_index} f0")],
            realizes={"provider_parameter": "Chal", "challenge": challenge_ref},
        )
    )
    add(
        Construct(
            "provider.response-type",
            "provider-type-parameter",
            "provider-shape",
            "Resp",
            f"abbrev Resp : Type := {carrier_alias(response_type)}",
            _sourced(universe.coordinate("EffectView", f"f3 s{response_index} f3")),
            consulted=[universe.coordinate("EffectView", f"f3 s{response_index} f0")],
            realizes={"provider_parameter": "Resp", "occurrence": response_occurrence},
        )
    )
    raw("")
    add(
        Construct(
            "provider.witness-type",
            "private-type",
            "provider-shape",
            "Wit",
            "variable (Wit : Type)",
            _gap(
                "property-premise",
                "No view carries a witness type. The Core has no Verifier-private "
                "input, no Claim, and no Relations binding, and the Prover's private "
                "inputs are not Core observables by design.",
                "ChallengeVerifyProtocol's Wit parameter and PerfectlyComplete's "
                "quantification over witnesses",
                [
                    f"{RELATIONS} Sections 3, 4, and 7.2: relation definitions, "
                    "confidential assignments, Protocol relation binding",
                    "no Relations binding exists for this admitted subject "
                    "(evaluation/formal-source-target-core-f1r1b/README.md)",
                ],
            ),
            realizes={"provider_parameter": "Wit"},
        )
    )
    add(
        Construct(
            "provider.prover-state-type",
            "private-type",
            "provider-shape",
            "PrvState",
            "variable (PrvState : Type)",
            _gap(
                "property-premise",
                "The Prover's private state between decisions is a strategy-owned "
                "object. The views expose only the guaranteed reads, including the "
                "Prover's own prior move, and no private state field.",
                "ChallengeVerifyProtocol's PrvState parameter",
                [
                    f"{TARGET} Section 9.2: ProverView has no private state field; "
                    "Section 12.3: ProverStrategyCapability",
                    f"{PLANS}: Plan-owned strategy execution and StrategyStateSlot",
                    f"{PROVIDER_SCHNORR}: the provider's commit returns (r • g, r)",
                ],
            ),
            realizes={"provider_parameter": "PrvState"},
        )
    )
    add(
        Construct(
            "provider.relation",
            "relation",
            "provider-shape",
            "rel",
            "variable (rel : Stmt → Wit → Bool)",
            _gap(
                "property-premise",
                "No view carries a relation predicate. The ClaimReductionView of this "
                "subject is empty and no relation is bound to the Statement binding.",
                "ChallengeVerifyProtocol's rel parameter and PerfectlyComplete's "
                "hypothesis rel x w = true",
                [
                    f"{RELATIONS} Sections 3 and 7.2",
                    "docs-next/analysis/semantic-relations.md",
                    f"{PROVIDER_SCHNORR}: fun pk sk => decide (sk • g = pk)",
                ],
                [universe.coordinate("PublicBindingView", "f2 s0 f2 v0")],
            ),
            realizes={"provider_parameter": "rel"},
        )
    )
    add(
        Construct(
            "provider.commit",
            "honest-strategy",
            "provider-shape",
            "honestCommit",
            "variable (honestCommit : Stmt → Wit → ProbComp (Commit × PrvState))",
            _gap(
                "property-premise",
                f"The views fix decision point {commit_occurrence}'s guaranteed reads "
                "and legal move type, not an honest algorithm producing the move; "
                "strategies are execution inputs, not Core observables.",
                "ChallengeVerifyProtocol.commit and the honest execution inside "
                "PerfectlyComplete",
                [
                    f"{TARGET} Sections 9.2 and 12.3",
                    f"{PLANS}",
                    f"{PROVIDER_SCHNORR}: Schnorr.sigma commit",
                ],
                [universe.coordinate("StrategyDecisionView", "f1 s0 f0")],
            ),
            realizes={"provider_field": "commit", "decision": commit_occurrence},
        )
    )
    add(
        Construct(
            "provider.respond",
            "honest-strategy",
            "provider-shape",
            "honestRespond",
            "variable (honestRespond : Stmt → Wit → PrvState → Chal → ProbComp Resp)",
            _gap(
                "property-premise",
                f"The views fix decision point {response_occurrence}'s guaranteed "
                "reads and legal move type, not an honest algorithm producing the "
                "move; strategies are execution inputs, not Core observables.",
                "ChallengeVerifyProtocol.respond and the honest execution inside "
                "PerfectlyComplete",
                [
                    f"{TARGET} Sections 9.2 and 12.3",
                    f"{PLANS}",
                    f"{PROVIDER_SCHNORR}: Schnorr.sigma respond",
                ],
                [universe.coordinate("StrategyDecisionView", "f1 s1 f0")],
            ),
            realizes={"provider_field": "respond", "decision": response_occurrence},
        )
    )
    raw("")
    raw("def providerShape : ChallengeVerifyProtocol Stmt Wit Commit PrvState Chal Resp rel where")
    raw("  commit := honestCommit")
    raw("  respond := honestRespond")
    guard_name = f"guard{guard_occurrence['ordinal']}"
    check_name = f"check{check_ordinal}"
    add(
        Construct(
            "provider.verify",
            "outcome-map",
            "provider-shape",
            "verify",
            f"  verify := fun x pc c z => {guard_name} ({check_name} x pc c z)",
            _gap(
                "operational-outcome-map",
                "The views carry the two terminal verdict cases Accept and Reject and "
                "an interpretation-failure schema of None. No leaf maps the Core's "
                "terminal verdicts (Accept | Reject | Abort) and run-outcome lanes "
                "(CompletedRun, InterpretationFailed, StrategyStopped, and the "
                "qualified operational noncompletion partition) into the provider's "
                "Boolean verify result and OptionT failure layer. The generator "
                "renders Accept as true and Reject as false and has no image for "
                "Abort or for any noncompletion outcome.",
                "ChallengeVerifyProtocol.verify and any operational trace relation "
                "that must include every failure or noncompletion branch",
                [
                    f"{TARGET} Sections 6.4, 12.3, and 12.4",
                    f"{FOUNDATION} Section 8",
                    f"{PROVIDER_SIGMA}: verify : Bool; {PROVIDER_ORACLE_COMP}: "
                    "OptionT failure",
                ],
                [
                    universe.coordinate("EffectView", "f6 s0 f1 v0"),
                    universe.coordinate("EffectView", "f6 s1 f1 v1"),
                    universe.coordinate("ExecutionView", "f7 v0"),
                ],
            ),
            realizes={"provider_field": "verify"},
        )
    )
    raw("")
    raw("end Observables")
    raw("")
    raw("end ZkcF2O0")
    raw("")
    raw("#print axioms ZkcF2O0.interaction")
    raw("#print axioms ZkcF2O0.providerShape")

    premises = [
        {
            "id": "body-compiler-codec",
            "statement": (
                "Reading any view leaf requires the decoders of the body compilers "
                "named in the F0-V2B1 schema source and the K1 canonical datum codec. "
                "The generator decoded ordinal references, value references, value "
                "types, module declaration references, the guard body, and content "
                "identifiers under that premise; the premise is a Foundation and PIR "
                "law, not a view leaf."
            ),
            "compilers_decoded": [
                "algorithm-ref-body-v0",
                "binding-ref-body-v0",
                "challenge-ref-body-v0",
                "check-ref-body-v0",
                "core-id-body-v0",
                "decision-ref-body-v0",
                "evaluation-contract-id-body-v0",
                "guard-body-v0",
                "module-declaration-ref-body-v0",
                "occurrence-ref-body-v0",
                "protocol-id-body-v0",
                "public-input-ref-body-v0",
                "terminal-ref-body-v0",
                "value-ref-body-v0",
                "value-type-body-v0",
            ],
            "lives_in": [
                f"{FOUNDATION} Section 4 and Appendices A.2 and A.3",
                f"{K1_MODEL} decode_datum, value_type_datum, schema_datum",
                f"{OWNER_MODEL} value_ref_datum, module_declaration_ref_datum, "
                "_guard_datum",
            ],
        }
    ]
    rendering_rules = [
        {
            "id": "root-nat-carrier",
            "rule": "a value type whose domain is root ordinal 2 (nat) with schema "
            "Nat(m) is carried by Fin (m + 1)",
        },
        {
            "id": "root-bool-carrier",
            "rule": "the root ordinal 1 (bool) value type is carried by Bool",
        },
        {
            "id": "message-step",
            "rule": "a ProverMessage occurrence is a monadic bind of the strategy's "
            "decision at that point applied to its guaranteed reads in view order",
        },
        {
            "id": "challenge-step",
            "rule": "a Challenge occurrence under the Fresh interpretation is a monadic "
            "bind of its public-coin law parameter",
        },
        {
            "id": "check-step",
            "rule": "an InvokeCheck occurrence is a let-binding of the Check's "
            "denotation parameter applied to its ordered inputs",
        },
        {
            "id": "terminal-steps",
            "rule": "a guarded ReachTerminal occurrence is an if on the guard's "
            "denotation parameter applied to its inputs; the unconditional final "
            "ReachTerminal is the else branch; first-active selection is the if/else "
            "order",
        },
        {
            "id": "verdict-cases",
            "rule": "the Verdict inductive has one constructor per Terminal in Core "
            "order named by its verdict",
        },
    ]
    return Draft(constructs, layout, subject, universe, premises, rendering_rules)


def occurrences_of_challenge(occurrences: list[dict[str, Any]], challenge: int) -> int:
    for item in occurrences:
        if item["effect"] == "Challenge" and item["target"] == challenge:
            return item["ordinal"]
    raise GeneratorError("challenge has no occurrence")


def render(current: Draft) -> tuple[str, dict[str, Any]]:
    lines: list[str] = []
    positions: dict[str, int] = {}
    for kind, payload in current.layout:
        if kind == "raw":
            lines.append(payload)
            continue
        construct = current.constructs[payload]
        lines.append(f"{construct.lean_text}  {MARKER_PREFIX}{construct.id}]")
        positions[construct.id] = len(lines)
        lines.extend(construct.trailing)
    text = "\n".join(lines) + "\n"
    for old, new in current.lean_edits:
        if old not in text:
            raise GeneratorError(f"lean edit target {old!r} is absent")
        text = text.replace(old, new, 1)
    ordered = [
        current.constructs[payload]
        for kind, payload in current.layout
        if kind == "construct"
    ]
    entries = []
    for construct in ordered:
        entries.append(
            {
                "id": construct.id,
                "kind": construct.kind,
                "layer": construct.layer,
                "lean": {
                    "name": construct.lean_name,
                    "line": positions[construct.id],
                    "text": construct.lean_text.strip(),
                },
                "realizes": construct.realizes,
                "source": copy.deepcopy(construct.source),
                "consulted": copy.deepcopy(construct.consulted),
            }
        )
    gaps = [
        {
            "construct": entry["id"],
            "class": entry["source"]["no_source_coordinate"]["class"],
            "needed_for": entry["source"]["no_source_coordinate"]["needed_for"],
        }
        for entry in entries
        if "no_source_coordinate" in entry["source"]
    ]
    ledger = {
        "format": LEDGER_FORMAT,
        "authority": "none; untrusted generator output",
        "subject": {
            "core_id": current.subject["core_id"],
            "protocol_id": current.subject["protocol_id"],
            "view_source_digest": current.subject["source_digest"],
            "view_leaf_counts": {
                view: len(coordinates)
                for view, coordinates in current.subject["manifests"].items()
            },
        },
        "provider": dict(PROVIDER),
        "marker": MARKER_PREFIX + "<id>]",
        "premises": copy.deepcopy(current.premises),
        "rendering_rules": copy.deepcopy(current.rendering_rules),
        "constructs": entries,
        "gaps": gaps,
    }
    for edit in current.ledger_edits:
        edit(ledger)
    return text, ledger


def _construct(ledger: dict[str, Any], construct_id: str) -> dict[str, Any]:
    for entry in ledger["constructs"]:
        if entry["id"] == construct_id:
            return entry
    raise GeneratorError(f"ledger has no construct {construct_id}")


def _remove_construct(current: Draft, construct_id: str, keep_text: bool) -> None:
    construct = current.constructs.pop(construct_id)
    for index, (kind, payload) in enumerate(current.layout):
        if kind == "construct" and payload == construct_id:
            replacement: list[tuple[str, str]] = []
            if keep_text:
                replacement.append(("raw", construct.lean_text))
                replacement.extend(("raw", line) for line in construct.trailing)
            current.layout[index : index + 1] = replacement
            return
    raise GeneratorError(f"layout has no construct {construct_id}")


def _mutate(current: Draft, mutation: str) -> None:
    constructs = current.constructs
    if mutation == "alias-equal-valued-read-coordinates":

        def alias(ledger: dict[str, Any]) -> None:
            source = _construct(ledger, "read.0.public-invocation-input.0")["source"]
            _construct(ledger, "read.2.public-invocation-input.0")["source"] = (
                copy.deepcopy(source)
            )

        current.ledger_edits.append(alias)
    elif mutation == "drop-response-producer":
        _remove_construct(current, "occurrence.2", keep_text=True)
    elif mutation == "strip-response-producer-coordinate":
        current.ledger_edits.append(
            lambda ledger: _construct(ledger, "occurrence.2").__setitem__("source", {})
        )
    elif mutation == "constant-fresh-challenge":
        step = constructs["occurrence.1"]
        step.lean_text = f"  let {step.lean_name} : Z3 := 0"
        step.realizes = {
            "occurrence": 1,
            "effect": "Challenge",
            "challenge": 0,
            "realization": "constant",
        }
        _remove_construct(current, "challenge.0.law", keep_text=False)
    elif mutation == "omit-reject-terminal":
        _remove_construct(current, "terminal.1.verdict", keep_text=False)
        _remove_construct(current, "occurrence.5", keep_text=False)
        for index, (kind, payload) in enumerate(current.layout):
            if kind == "raw" and payload == "  else":
                current.layout[index + 1 : index + 1] = [
                    ("raw", "    return Verdict.accept")
                ]
                break
    elif mutation == "unknown-coordinate-ordinal":

        def out_of_range(ledger: dict[str, Any]) -> None:
            coordinate = _construct(ledger, "occurrence.0")["source"]["coordinate"]
            coordinate["path"][1]["ordinal"] = 99

        current.ledger_edits.append(out_of_range)
    elif mutation == "cross-view-coordinate-replay":

        def replay(ledger: dict[str, Any]) -> None:
            coordinate = _construct(ledger, "type.z3")["source"]["coordinate"]
            coordinate["view"] = "PublicBindingView"

        current.ledger_edits.append(replay)
    elif mutation == "invent-check-denotation":
        construct = constructs["check.0.denotation"]
        construct.lean_text = (
            "def check0 : Z3 → Z3 → Z3 → Z3 → CheckOutput := fun _ _ _ _ => true"
        )
        construct.source = _sourced(
            current.universe.coordinate("EffectView", "f5 s0 f1")
        )
    elif mutation == "unledgered-lean-marker":
        current.lean_edits.append(
            ("open OracleComp\n", f"open OracleComp  {MARKER_PREFIX}phantom.construct]\n")
        )
    elif mutation == "reorder-challenge-after-response":
        first = current.layout.index(("construct", "occurrence.1"))
        second = current.layout.index(("construct", "occurrence.2"))
        current.layout[first], current.layout[second] = (
            current.layout[second],
            current.layout[first],
        )
    elif mutation == "untyped-gap-entry":
        current.ledger_edits.append(
            lambda ledger: _construct(ledger, "check.0.denotation")["source"][
                "no_source_coordinate"
            ].__setitem__("reason", "")
        )
    elif mutation == "duplicate-lean-marker":
        current.lean_edits.append(
            (
                "    return Verdict.accept\n",
                f"    return Verdict.accept  {MARKER_PREFIX}occurrence.3]\n",
            )
        )
    elif mutation == "verdict-swap":

        def swap(ledger: dict[str, Any]) -> None:
            first = _construct(ledger, "terminal.0.verdict")["realizes"]
            second = _construct(ledger, "terminal.1.verdict")["realizes"]
            first["verdict"], second["verdict"] = second["verdict"], first["verdict"]

        current.ledger_edits.append(swap)
    elif mutation == "effect-kind-mismatch":
        current.ledger_edits.append(
            lambda ledger: _construct(ledger, "occurrence.1")["realizes"].__setitem__(
                "effect", "ProverMessage"
            )
        )
    else:
        raise GeneratorError(f"unknown mutation {mutation}")


MUTATIONS: tuple[str, ...] = (
    "alias-equal-valued-read-coordinates",
    "drop-response-producer",
    "strip-response-producer-coordinate",
    "constant-fresh-challenge",
    "omit-reject-terminal",
    "unknown-coordinate-ordinal",
    "cross-view-coordinate-replay",
    "invent-check-denotation",
    "unledgered-lean-marker",
    "reorder-challenge-after-response",
    "untyped-gap-entry",
    "duplicate-lean-marker",
    "verdict-swap",
    "effect-kind-mismatch",
)


def generate(
    mutation: str | None = None, subject: dict[str, Any] | None = None
) -> tuple[str, dict[str, Any]]:
    current = draft(subject)
    if mutation is not None:
        _mutate(current, mutation)
    return render(current)


def ledger_bytes(ledger: dict[str, Any]) -> bytes:
    return (json.dumps(ledger, indent=2, sort_keys=True) + "\n").encode("utf-8")


def write_generated() -> tuple[Path, Path]:
    text, ledger = generate()
    GENERATED_LEAN.parent.mkdir(parents=True, exist_ok=True)
    GENERATED_LEAN.write_bytes(text.encode("utf-8"))
    GENERATED_LEDGER.write_bytes(ledger_bytes(ledger))
    return GENERATED_LEAN, GENERATED_LEDGER


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write generated/ files")
    parser.add_argument("--mutation", choices=MUTATIONS)
    arguments = parser.parse_args()
    if arguments.write:
        lean_path, ledger_path = write_generated()
        print(f"wrote {lean_path} and {ledger_path}")
        return 0
    text, ledger = generate(arguments.mutation)
    print(text)
    print(ledger_bytes(ledger).decode("utf-8"))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
