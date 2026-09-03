"""Typed projection model for the migrated Terminal owner contract.

The model reads the authored profile manifests directly, admits one bounded
exact Core under the resulting Interaction profile, and derives the six
normalized owner views.  It never synthesizes or publishes a profile overlay.
"""

from __future__ import annotations

import copy
from dataclasses import dataclass, replace
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import MappingProxyType, ModuleType
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
B3_MODEL = (
    ROOT
    / "evaluation"
    / "formal-source-claim-reduction-owner-projections-f0v2b2c1b3"
    / "model.py"
)
B5B1_MODEL = (
    ROOT
    / "evaluation"
    / "formal-source-terminal-owner-contracts-f0v2b2c1b5b1"
    / "model.py"
)
PUBLICATION_MODEL = (
    ROOT / "evaluation" / "semantic-profile-publication" / "reference_model.py"
)
B2B_MODEL = ROOT / "evaluation" / "formal-source-view-schema-f0v2b2b" / "model.py"
CODEC_MODEL = ROOT / "evaluation" / "formal-source-view-codec-f0v2b2c1a" / "model.py"
SCHEMA_DELTA = HERE / "schema-delta.json"


def _load(name: str, path: Path) -> ModuleType:
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load module at {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


b3 = _load("_zkc_f0v2b2c1b5b2_b3", B3_MODEL)
terminal_contracts = _load("_zkc_f0v2b2c1b5b2_b5b1", B5B1_MODEL)
publication = _load("_zkc_f0v2b2c1b5b2_publication", PUBLICATION_MODEL)
b2b = _load("_zkc_f0v2b2c1b5b2_b2b", B2B_MODEL)
codec = _load("_zkc_f0v2b2c1b5b2_codec", CODEC_MODEL)

foundation = b3.foundation
base = b3.base
b2c0 = b3.b2c0
k1 = b3.k1

EVALUATOR_FINGERPRINT = hashlib.sha256(
    b"zkc-f0-v2b2c1b5b2-terminal-owner-evaluator-v0"
).digest()
MAX_LOCAL_ITEMS = 1 << 14
CANDIDATE_SCHEMA_FORMAT = (
    "zkc.formal-source-terminal-owner-projections-f0v2b2c1b5b2.schema-source.v0"
)
CANDIDATE_SCHEMA_SCOPE = "interaction-r2-expanded-terminal-normalized-six-view-grammar"


class FamilyFailure(ValueError):
    """One classified failure at the bounded candidate owner boundary."""

    def __init__(self, outcome: str, code: str, detail: str) -> None:
        super().__init__(detail)
        self.outcome = outcome
        self.code = code
        self.detail = detail


@dataclass(frozen=True)
class AdmissionResult:
    outcome: str
    code: str
    detail: str
    handle: object | None = None


@dataclass(frozen=True)
class TerminalDecl:
    verdict: object
    public_outputs: tuple[object, ...]
    required_true_checks: tuple[int, ...]
    required_applied_reductions: tuple[int, ...]
    terminal_claims: tuple[int, ...]


@dataclass(frozen=True)
class ValidationEvidence:
    outputs: tuple[tuple[object, ...], ...]
    paths: tuple[tuple[int, ...], ...]
    check_positions: Mapping[int, int]
    reduction_positions: Mapping[int, int]
    terminal_positions: Mapping[int, int]
    claim_uses: Mapping[int, tuple[tuple[str, int, int, int], ...]]
    terminal_analysis: object


@dataclass(frozen=True)
class Fixture:
    environment: object
    core: object
    candidate: object
    protocol_candidate: object
    module: object
    algorithms: tuple[object, ...]


def _fail(outcome: str, code: str, detail: str) -> None:
    raise FamilyFailure(outcome, code, detail)


def _wire(value: object) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    ).encode("ascii")


def _digest(value: object) -> str:
    return hashlib.sha256(_wire(value)).hexdigest()


def _strict_delta() -> dict[str, Any]:
    try:
        value = json.loads(SCHEMA_DELTA.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise FamilyFailure(
            "Malformed", "F0V2B2C1B5B2-M-SCHEMA-DELTA", str(error)
        ) from error
    expected = {
        "format",
        "predecessor",
        "candidate_format",
        "candidate_scope",
        "remove_definitions",
        "replace_definitions",
        "add_definitions",
    }
    if type(value) is not dict or set(value) != expected:
        _fail(
            "Malformed",
            "F0V2B2C1B5B2-M-SCHEMA-DELTA",
            "schema delta has another exact outer shape",
        )
    return value


def _candidate_schema_template() -> tuple[dict[str, Any], str]:
    """Apply the pinned B5B2 delta and return owner-free grammar identity."""

    try:
        source = json.loads(
            (B2B_MODEL.parent / "schema-source.json").read_text(encoding="utf-8")
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise FamilyFailure(
            "Malformed", "F0V2B2C1B5B2-M-SCHEMA-SOURCE", str(error)
        ) from error
    if type(source) is not dict:
        _fail(
            "Malformed",
            "F0V2B2C1B5B2-M-SCHEMA-SOURCE",
            "B2B schema source has another outer carrier",
        )
    delta = _strict_delta()
    if (
        delta["predecessor"] != {"format": source["format"], "sha256": _digest(source)}
        or delta["candidate_format"] != CANDIDATE_SCHEMA_FORMAT
        or delta["candidate_scope"] != CANDIDATE_SCHEMA_SCOPE
    ):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-SCHEMA-PREDECESSOR",
            "schema delta does not name the exact B2B predecessor",
        )
    candidate = copy.deepcopy(source)
    candidate["format"] = CANDIDATE_SCHEMA_FORMAT
    candidate["scope"] = CANDIDATE_SCHEMA_SCOPE
    definitions = candidate["definitions"]
    for name, prior_digest in delta["remove_definitions"].items():
        if name not in definitions or _digest(definitions[name]) != prior_digest:
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-SCHEMA-REMOVE",
                f"cannot remove drifted definition {name}",
            )
        del definitions[name]
    for name, replacement in delta["replace_definitions"].items():
        if (
            name not in definitions
            or type(replacement) is not dict
            or set(replacement) != {"prior_sha256", "value"}
            or _digest(definitions[name]) != replacement["prior_sha256"]
        ):
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-SCHEMA-REPLACE",
                f"cannot replace drifted definition {name}",
            )
        definitions[name] = copy.deepcopy(replacement["value"])
    for name, definition in delta["add_definitions"].items():
        if name in definitions:
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-SCHEMA-ADD",
                f"candidate definition {name} already exists",
            )
        definitions[name] = copy.deepcopy(definition)
    candidate["definitions"] = {name: definitions[name] for name in sorted(definitions)}
    grammar = {key: value for key, value in candidate.items() if key != "owner_profile"}
    return candidate, _digest(grammar)


_PUBLICATION_CACHE: tuple[object, str] | None = None


def candidate_publication() -> tuple[object, str]:
    """Return the authored migration publication and bound view grammar."""

    global _PUBLICATION_CACHE
    if _PUBLICATION_CACHE is not None:
        return _PUBLICATION_CACHE
    _template, grammar_digest = _candidate_schema_template()
    candidate = publication.compile_repository()
    _PUBLICATION_CACHE = candidate, grammar_digest
    return _PUBLICATION_CACHE


def candidate_profile_artifact() -> object:
    return candidate_publication()[0].profiles["interaction"]


def candidate_schema_source() -> dict[str, Any]:
    template, grammar_digest = _candidate_schema_template()
    artifact = candidate_profile_artifact()
    template["owner_profile"] = {
        "key": "interaction",
        "revision": 2,
        "profile_digest": artifact.profile_id.digest.hex(),
        "profile_body_sha256": hashlib.sha256(artifact.body_bytes).hexdigest(),
    }
    observed = _digest(
        {key: value for key, value in template.items() if key != "owner_profile"}
    )
    if observed != grammar_digest:
        _fail(
            "CheckerFailure",
            "F0V2B2C1B5B2-C-SCHEMA-CYCLE",
            "owner attachment changed the bound grammar",
        )
    return template


def _compile_candidate_schema() -> tuple[
    dict[str, Any], dict[str, str], dict[str, int]
]:
    source = candidate_schema_source()
    b2b.FORMAT = CANDIDATE_SCHEMA_FORMAT
    b2b.SCOPE = CANDIDATE_SCHEMA_SCOPE
    b2b.PROFILE = copy.deepcopy(source["owner_profile"])
    codec.b2b.PROFILE = copy.deepcopy(source["owner_profile"])
    return b2b.compile_source(source)


VIEW_SCHEMAS, VIEW_OWNERS, VIEW_SCHEMA_STATS = _compile_candidate_schema()
_PC_GRAPH_SCHEMA = codec.record_field(VIEW_SCHEMAS["PublicCoinView"], 1)
_PC_NODE_SCHEMA = codec.record_field(_PC_GRAPH_SCHEMA, 0)["element"]
_PC_EDGE_SCHEMA = codec.record_field(_PC_GRAPH_SCHEMA, 1)["element"]


def profile_evidence() -> dict[str, Any]:
    candidate, grammar_digest = candidate_publication()
    artifact = candidate.profiles["interaction"]
    return {
        "candidate_interaction_digest": artifact.profile_id.digest.hex(),
        "candidate_interaction_body_sha256": hashlib.sha256(
            artifact.body_bytes
        ).hexdigest(),
        "schema_grammar_sha256": grammar_digest,
        "schema_source_sha256": _digest(candidate_schema_source()),
        "profiles_compiled": sorted(publication.PROFILE_KEYS),
    }


def _record(*values: object) -> object:
    return k1.DatumRecord(tuple((index, value) for index, value in enumerate(values)))


def _seq(values: tuple[object, ...]) -> object:
    return k1.DatumSeq(values)


def _variant(case: int, payload: object = k1.UNIT) -> object:
    return k1.DatumVariant(case, payload)


def _terminal_datum(terminal: object) -> object:
    if type(terminal) is not TerminalDecl:
        raise k1.ModelError("Terminal has another exact carrier")
    return _record(
        _variant(terminal.verdict.value),
        _seq(tuple(base.value_ref_datum(item) for item in terminal.public_outputs)),
        _seq(tuple(k1.Nat(item) for item in terminal.required_true_checks)),
        _seq(tuple(k1.Nat(item) for item in terminal.required_applied_reductions)),
        _seq(tuple(k1.Nat(item) for item in terminal.terminal_claims)),
    )


def _effect_datum(effect: object) -> object:
    if type(effect) is base.CheckEffect:
        return _variant(3, k1.Nat(effect.check))
    if type(effect) is b3.ApplyReductionEffect:
        return _variant(4, k1.Nat(effect.reduction))
    if type(effect) is base.TerminalEffect:
        return _variant(5, k1.Nat(effect.terminal))
    raise k1.ModelError("effect is outside the expanded-Terminal slice")


def core_domain_datum(core: object) -> object:
    if type(core) is not base.InteractiveCore:
        raise k1.ModelError("Core has another carrier")
    return _record(
        _seq(
            tuple(
                k1.BytesValue(item.internal_reference()) for item in core.used_modules
            )
        ),
        _seq(tuple(base._input_datum(item) for item in core.public_inputs)),
        _seq(()),
        _seq(()),
        _seq(()),
        _seq(tuple(base._scope_datum(item) for item in core.scopes)),
        _seq(tuple(base._binding_datum(item) for item in core.public_bindings)),
        _seq(()),
        _seq(()),
        _seq(tuple(base._check_datum(item) for item in core.checks)),
        _seq(tuple(b3._claim_datum(item) for item in core.claims)),
        _seq(tuple(b3._reduction_datum(item) for item in core.reductions)),
        _seq(tuple(_terminal_datum(item) for item in core.terminals)),
        _seq(
            tuple(
                _record(
                    k1.Nat(item.scope),
                    base._guard_datum(item.guard),
                    _effect_datum(item.effect),
                )
                for item in core.occurrences
            )
        ),
    )


def core_profiled_body(core: object, profile_id: object) -> bytes:
    return k1.encode_datum(
        k1.profiled_semantic_body(profile_id, core_domain_datum(core))
    )


def core_id(core: object, profile_id: object) -> object:
    return k1.profiled_content_id(
        base.TARGET_CORE_KIND,
        profile_id,
        core_domain_datum(core),
        semantic_regime=k1.SEMANTIC_REGIME_ID,
    )


def make_candidate(core: object, profile_id: object) -> object:
    return b2c0.CanonicalCoreCandidate(
        core_id(core, profile_id), profile_id, core_profiled_body(core, profile_id)
    )


def _decode_terminal(value: object) -> TerminalDecl:
    fields = b2c0._record(value, tuple(range(5)), "candidate Terminal")
    verdict_case, verdict_payload = b2c0._variant(
        fields[0], (0, 1, 2), "Terminal verdict"
    )
    b2c0._unit(verdict_payload, "Terminal verdict payload")
    return TerminalDecl(
        base.TerminalVerdict(verdict_case),
        tuple(
            b2c0._decode_value_ref(item)
            for item in b2c0._sequence(fields[1], "Terminal public outputs")
        ),
        tuple(
            b2c0._nat(item, "required Check")
            for item in b2c0._sequence(fields[2], "required Checks")
        ),
        tuple(
            b2c0._nat(item, "required Reduction")
            for item in b2c0._sequence(fields[3], "required Reductions")
        ),
        tuple(
            b2c0._nat(item, "terminal Claim")
            for item in b2c0._sequence(fields[4], "terminal Claims")
        ),
    )


def _decode_effect(value: object) -> object:
    case, payload = b2c0._variant(value, tuple(range(8)), "Core effect")
    if case == 3:
        return base.CheckEffect(b2c0._nat(payload, "Check backlink"))
    if case == 4:
        return b3.ApplyReductionEffect(b2c0._nat(payload, "Reduction backlink"))
    if case == 5:
        return base.TerminalEffect(b2c0._nat(payload, "Terminal backlink"))
    _fail(
        "Unsupported",
        "F0V2B2C1B5B2-U-EFFECT",
        f"effect tag {case} is outside the expanded-Terminal slice",
    )
    raise AssertionError("unreachable")


def decode_core(domain: object) -> object:
    """Strictly decode the exact bounded candidate Core body."""

    fields = b2c0._record(domain, tuple(range(14)), "InteractiveCore")
    tables = tuple(
        b2c0._sequence(value, f"InteractiveCore field {ordinal}")
        for ordinal, value in enumerate(fields)
    )
    if any(tables[index] for index in (2, 3, 4, 7, 8)):
        _fail(
            "Unsupported",
            "F0V2B2C1B5B2-U-OTHER-SLICE",
            "private, constant, derived, Challenge, and Oracle tables are outside B5B2",
        )
    used_modules = tuple(b2c0._content_ref(item, "used module") for item in tables[0])
    public_inputs = tuple(
        base.InputDecl(
            b2c0._decode_value_type(b2c0._record(item, (0,), "public input")[0])
        )
        for item in tables[1]
    )
    scopes: list[object] = []
    for item in tables[5]:
        parent, opening = b2c0._record(item, (0, 1), "scope")
        parent_case, parent_payload = b2c0._variant(parent, (0, 1), "scope parent")
        opening_case, opening_payload = b2c0._variant(opening, (0, 1), "scope opening")
        if parent_case == 0:
            b2c0._unit(parent_payload, "absent parent")
        if opening_case == 0:
            b2c0._unit(opening_payload, "initial opening")
        scopes.append(
            base.ScopeDecl(
                None if parent_case == 0 else b2c0._nat(parent_payload, "parent scope"),
                None
                if opening_case == 0
                else b2c0._nat(opening_payload, "opening occurrence"),
            )
        )
    bindings: list[object] = []
    for item in tables[6]:
        scope, binding_class, value = b2c0._record(item, (0, 1, 2), "binding")
        class_case, class_payload = b2c0._variant(
            binding_class, (0, 1, 2), "binding class"
        )
        b2c0._unit(class_payload, "binding-class payload")
        bindings.append(
            base.PublicBindingDecl(
                b2c0._nat(scope, "binding scope"),
                base.BindingClass(class_case),
                b2c0._decode_value_ref(value),
            )
        )
    checks: list[object] = []
    for item in tables[9]:
        algorithm, contract, inputs = b2c0._record(item, (0, 1, 2), "Check")
        checks.append(
            base.CheckDecl(
                b2c0._content_ref(algorithm, "Check algorithm"),
                b2c0._content_ref(contract, "Check contract"),
                tuple(
                    b2c0._decode_value_ref(value)
                    for value in b2c0._sequence(inputs, "Check inputs")
                ),
            )
        )
    occurrences: list[object] = []
    for item in tables[13]:
        scope, guard, effect = b2c0._record(item, (0, 1, 2), "occurrence")
        occurrences.append(
            base.OccurrenceDecl(
                b2c0._nat(scope, "occurrence scope"),
                b2c0._decode_guard(guard),
                _decode_effect(effect),
            )
        )
    return base.InteractiveCore(
        used_modules,
        public_inputs,
        (),
        (),
        (),
        tuple(scopes),
        tuple(bindings),
        (),
        (),
        tuple(checks),
        tuple(b3._decode_claim(item) for item in tables[10]),
        tuple(b3._decode_reduction(item) for item in tables[11]),
        tuple(_decode_terminal(item) for item in tables[12]),
        tuple(occurrences),
    )


def _module_references(core: object) -> tuple[object, ...]:
    refs: list[object] = [claim.contract for claim in core.claims]
    for reduction in core.reductions:
        refs.append(reduction.contract)
        refs.extend(reduction.output_contracts)
    return tuple(refs)


def _ordinary_references(core: object) -> tuple[tuple[object, ...], tuple[object, ...]]:
    algorithms = {check.algorithm for check in core.checks}
    contracts = {check.evaluation_contract for check in core.checks}
    for occurrence in core.occurrences:
        if type(occurrence.guard) is base.EvaluateGuard:
            algorithms.add(occurrence.guard.algorithm)
            contracts.add(occurrence.guard.evaluation_contract)

    def key(item: object) -> bytes:
        return item.internal_reference()

    return tuple(sorted(algorithms, key=key)), tuple(sorted(contracts, key=key))


def _authenticate_algorithms(
    core: object, environment: object
) -> Mapping[object, object]:
    algorithms, contracts = _ordinary_references(core)
    if set(environment.algorithm_preimages) != set(algorithms):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-EXACT-ALGORITHMS",
            "guard and Check algorithm closure is not exact",
        )
    if set(environment.algorithm_modules) != set(algorithms):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-EXACT-ALGORITHM-MODULES",
            "algorithm module-closure map is not exact",
        )
    if set(environment.contract_preimages) != set(contracts):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-EXACT-CONTRACTS",
            "evaluation-contract closure is not exact",
        )
    functions: dict[object, object] = {}
    ledger = k1.AuthenticationLedger()
    try:
        for identifier in algorithms:
            algorithm = environment.algorithm_preimages[identifier]
            if (
                k1.authenticate_algorithm_identity(algorithm, ledger=ledger)
                != identifier
            ):
                _fail(
                    "Refused",
                    "F0V2B2C1B5B2-R-ALGORITHM-ID",
                    "algorithm identity differs from its exact reference",
                )
            modules = environment.algorithm_modules[identifier]
            dependencies = k1.direct_module_dependencies(algorithm, ledger=ledger)
            k1.authenticate_module_closure(
                dependencies,
                dict(modules),
                semantic_regime=k1.SEMANTIC_REGIME_ID,
                ledger=ledger,
            )
            k1.authenticate_algorithm_declaration_references(
                algorithm, dict(modules), ledger=ledger
            )
            functions[identifier] = algorithm.function_type
        for identifier in contracts:
            contract = environment.contract_preimages[identifier]
            if contract.identity != identifier:
                _fail(
                    "Refused",
                    "F0V2B2C1B5B2-R-CONTRACT-ID",
                    "evaluation-contract identity differs",
                )
            k1.authenticate_content_id(
                identifier,
                contract.body(),
                environment.prior_meta_preimages,
                ledger=ledger,
            )
    except FamilyFailure:
        raise
    except Exception as error:
        outcome = getattr(getattr(error, "outcome", None), "value", None)
        _fail(outcome or "Refused", "F0V2B2C1B5B2-R-DEPENDENCY", str(error))
    return MappingProxyType(functions)


def _validate_nominal(reference: object, kind: str, environment: object) -> None:
    if type(reference) is not base.ModuleDeclarationRef:
        _fail(
            "Malformed",
            "F0V2B2C1B5B2-M-MODULE-REFERENCE",
            "module declaration reference has another carrier",
        )
    if reference.declaration_kind != kind:
        _fail(
            "KindMismatch",
            "F0V2B2C1B5B2-K-DECLARATION",
            f"expected {kind}, got {reference.declaration_kind}",
        )
    module = environment.module_preimages.get(reference.module)
    if module is None:
        _fail(
            "MissingDependency",
            "F0V2B2C1B5B2-D-MODULE",
            "module preimage is missing",
        )
    try:
        body = k1.resolve_module_declaration(
            module, reference.declaration_kind, reference.local_ordinal
        )
    except Exception as error:
        _fail("Refused", "F0V2B2C1B5B2-R-DECLARATION", str(error))
    if (
        type(body) is not k1.DatumRecord
        or tuple(ordinal for ordinal, _ in body.fields) != (0,)
        or type(body.fields[0][1]) is not k1.Symbol
    ):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-NOMINAL-BODY",
            f"{kind} is not the selected nominal declaration",
        )


def _output_types(core: object) -> tuple[tuple[object, ...], ...]:
    result: list[tuple[object, ...]] = []
    for occurrence in core.occurrences:
        if type(occurrence.effect) is base.CheckEffect:
            result.append((k1.BOOL,))
        elif type(occurrence.effect) in (b3.ApplyReductionEffect, base.TerminalEffect):
            result.append(())
        else:
            _fail(
                "Unsupported",
                "F0V2B2C1B5B2-U-EFFECT",
                "effect is outside the bounded family",
            )
    return tuple(result)


def _value_type(
    core: object, outputs: tuple[tuple[object, ...], ...], reference: object
) -> object:
    if type(reference) is base.PublicInputRef:
        if not 0 <= reference.ordinal < len(core.public_inputs):
            _fail("Refused", "F0V2B2C1B5B2-R-VALUE-REF", "public input is absent")
        return core.public_inputs[reference.ordinal].value_type
    if type(reference) is base.OccurrenceOutputRef:
        if not 0 <= reference.occurrence < len(outputs):
            _fail("Refused", "F0V2B2C1B5B2-R-VALUE-REF", "occurrence is absent")
        row = outputs[reference.occurrence]
        if not 0 <= reference.output_ordinal < len(row):
            _fail("Refused", "F0V2B2C1B5B2-R-VALUE-REF", "output is absent")
        return row[reference.output_ordinal]
    _fail(
        "Unsupported",
        "F0V2B2C1B5B2-U-VALUE-REF",
        "ValueRef is outside the Boolean Terminal slice",
    )
    raise AssertionError("unreachable")


def _producer_node(reference: object) -> tuple[int, ...]:
    if type(reference) is base.PublicInputRef:
        return (0, reference.ordinal)
    if type(reference) is base.OccurrenceOutputRef:
        return (8, reference.occurrence, reference.output_ordinal)
    _fail(
        "Unsupported",
        "F0V2B2C1B5B2-U-VALUE-REF",
        "ValueRef has no producer in this slice",
    )
    raise AssertionError("unreachable")


def _canonical_refs(values: tuple[int, ...], label: str) -> None:
    if values != tuple(sorted(set(values))):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-CANONICAL-SET",
            f"{label} is not ascending and unique",
        )


def _term_value(term: object) -> dict[str, Any]:
    if type(term) is k1.Literal:
        if term.value.value_type != k1.BOOL or type(term.value.datum) is not bool:
            _fail(
                "KindMismatch",
                "F0V2B2C1B5B2-K-BOOLEAN-TERM",
                "Terminal analysis encountered a non-Boolean literal",
            )
        return {"tag": "Literal", "value": term.value.datum}
    if type(term) is k1.Variable:
        if term.value_type != k1.BOOL:
            _fail(
                "KindMismatch",
                "F0V2B2C1B5B2-K-BOOLEAN-TERM",
                "Terminal analysis encountered a non-Boolean variable",
            )
        return {"tag": "Variable", "index": term.index}
    if type(term) is k1.Let:
        return {
            "tag": "Let",
            "bound": _term_value(term.bound),
            "body": _term_value(term.body),
        }
    if type(term) is k1.Conditional:
        return {
            "tag": "Conditional",
            "condition": _term_value(term.condition),
            "when_true": _term_value(term.when_true),
            "when_false": _term_value(term.when_false),
        }
    if type(term) is k1.PrimitiveCall:
        return {
            "tag": "PrimitiveCall",
            "primitive": term.primitive.identifier.internal_reference().hex(),
            "arguments": [_term_value(item) for item in term.arguments],
        }
    _fail(
        "Unsupported",
        "F0V2B2C1B5B2-U-BOOLEAN-TERM",
        "Foundation term constructor is outside the selected must-fact fragment",
    )
    raise AssertionError("unreachable")


def _algorithm_value(algorithm: object) -> dict[str, Any]:
    return {
        "algorithm_kind": algorithm.algorithm_kind.value,
        "ordered_inputs": len(algorithm.inputs),
        "term": _term_value(algorithm.term),
    }


def _guard_value(
    core: object, guard: object, algorithms: Mapping[object, object]
) -> dict[str, Any] | None:
    if type(guard) is base.AlwaysGuard:
        return None
    if type(guard) is not base.EvaluateGuard:
        _fail("Malformed", "F0V2B2C1B5B2-M-GUARD", "Guard carrier differs")
    inputs: list[dict[str, Any]] = []
    for reference in guard.inputs:
        if type(reference) is base.PublicInputRef:
            inputs.append({"kind": "PublicBoolean", "ref": reference.ordinal})
            continue
        if type(reference) is base.OccurrenceOutputRef:
            if (
                reference.output_ordinal == 0
                and 0 <= reference.occurrence < len(core.occurrences)
                and type(core.occurrences[reference.occurrence].effect)
                is base.CheckEffect
            ):
                inputs.append(
                    {
                        "kind": "CheckOutput",
                        "ref": core.occurrences[reference.occurrence].effect.check,
                    }
                )
                continue
        _fail(
            "Unsupported",
            "F0V2B2C1B5B2-U-GUARD-INPUT",
            "Terminal contract analysis requires direct public/Check Boolean inputs",
        )
    return {
        "algorithm": _algorithm_value(algorithms[guard.algorithm]),
        "evaluation_contract": "portable-evaluation-v0",
        "inputs": inputs,
    }


def _terminal_program(
    core: object, algorithms: Mapping[object, object]
) -> dict[str, Any]:
    outputs: dict[tuple[int, int], int] = {}
    for claim_ref, claim in enumerate(core.claims):
        if type(claim.source) is b3.ReductionOutputClaimSource:
            outputs[(claim.source.reduction, claim.source.output_ordinal)] = claim_ref
    return {
        "claims": [
            {
                "usage": "Linear"
                if claim.usage is base.ClaimUsage.LINEAR
                else "Reusable",
                "source": {
                    "kind": "Initial"
                    if type(claim.source) is b3.InitialClaimSource
                    else "ReductionOutput",
                    "reduction": None
                    if type(claim.source) is b3.InitialClaimSource
                    else claim.source.reduction,
                    "output": None
                    if type(claim.source) is b3.InitialClaimSource
                    else claim.source.output_ordinal,
                },
            }
            for claim in core.claims
        ],
        "reductions": [
            {
                "inputs": list(reduction.input_claims),
                "outputs": [
                    outputs[(reduction_ref, ordinal)]
                    for ordinal in range(len(reduction.output_contracts))
                ],
            }
            for reduction_ref, reduction in enumerate(core.reductions)
        ],
        "checks": [
            {"label": f"check-{check_ref}"}
            for check_ref, _check in enumerate(core.checks)
        ],
        "terminals": [
            {
                "verdict": ("Accept", "Reject", "Abort")[terminal.verdict.value],
                "public_outputs": [
                    k1.encode_datum(base.value_ref_datum(item)).hex()
                    for item in terminal.public_outputs
                ],
                "required_true_checks": list(terminal.required_true_checks),
                "required_applied_reductions": list(
                    terminal.required_applied_reductions
                ),
                "terminal_claims": list(terminal.terminal_claims),
            }
            for terminal in core.terminals
        ],
        "occurrences": [
            {
                "guard": _guard_value(core, occurrence.guard, algorithms),
                "effect": {
                    "kind": (
                        "Check"
                        if type(occurrence.effect) is base.CheckEffect
                        else "Reduction"
                        if type(occurrence.effect) is b3.ApplyReductionEffect
                        else "Terminal"
                    ),
                    "ref": (
                        occurrence.effect.check
                        if type(occurrence.effect) is base.CheckEffect
                        else occurrence.effect.reduction
                        if type(occurrence.effect) is b3.ApplyReductionEffect
                        else occurrence.effect.terminal
                    ),
                },
            }
            for occurrence in core.occurrences
        ],
    }


def _validate_core(
    core: object, environment: object, functions: Mapping[object, object]
) -> ValidationEvidence:
    if (
        not core.public_inputs
        or not core.scopes
        or not core.checks
        or not core.claims
        or not core.reductions
        or not core.terminals
        or not core.occurrences
    ):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-NONEMPTY",
            "the expanded-Terminal carrier omits a required table",
        )
    if any(
        len(table) > MAX_LOCAL_ITEMS
        for table in (
            core.public_inputs,
            core.public_bindings,
            core.checks,
            core.claims,
            core.reductions,
            core.terminals,
            core.occurrences,
        )
    ):
        _fail(
            "DeterministicLimitExceeded",
            "F0V2B2C1B5B2-L-TABLE",
            "a local table crosses the bounded candidate limit",
        )
    if core.scopes != (base.ScopeDecl(None, None),):
        _fail(
            "Unsupported",
            "F0V2B2C1B5B2-U-SCOPE",
            "B5B2 isolates one root scope",
        )
    if any(item.value_type != k1.BOOL for item in core.public_inputs):
        _fail(
            "Unsupported",
            "F0V2B2C1B5B2-U-INPUT-TYPE",
            "the independent finite oracle requires Boolean public inputs",
        )
    try:
        for item in core.public_inputs:
            item.value_type.__post_init__()
            k1.authenticate_value_type_reference(
                item.value_type,
                dict(environment.module_preimages),
                semantic_regime=k1.SEMANTIC_REGIME_ID,
            )
    except Exception as error:
        _fail("KindMismatch", "F0V2B2C1B5B2-K-VALUE-TYPE", str(error))

    module_refs = _module_references(core)
    direct_modules = tuple(
        sorted(
            {item.module for item in module_refs},
            key=lambda item: item.internal_reference(),
        )
    )
    if core.used_modules != direct_modules:
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-USED-MODULES",
            "used_modules differs from the exact declaration-owner set",
        )
    if set(environment.module_preimages) != set(direct_modules):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-MODULE-CLOSURE",
            "module preimage closure is not exact",
        )
    for claim in core.claims:
        if type(claim) is not b3.ClaimDecl:
            _fail("Malformed", "F0V2B2C1B5B2-M-CLAIM", "Claim carrier differs")
        _validate_nominal(claim.contract, "pir.claim-contract", environment)
    for reduction in core.reductions:
        if type(reduction) is not b3.ReductionDecl:
            _fail(
                "Malformed",
                "F0V2B2C1B5B2-M-REDUCTION",
                "Reduction carrier differs",
            )
        _validate_nominal(reduction.contract, "pir.reduction-contract", environment)
        for contract in reduction.output_contracts:
            _validate_nominal(contract, "pir.claim-contract", environment)
        if (
            reduction.scope != 0
            or reduction.side_inputs
            or reduction.required_challenges
            or reduction.required_publications
        ):
            _fail(
                "Unsupported",
                "F0V2B2C1B5B2-U-REDUCTION-SURFACE",
                "B5B2 isolates root reductions without challenge/publication inputs",
            )

    bound_public: set[int] = set()
    binding_triples: set[tuple[object, ...]] = set()
    outputs = _output_types(core)
    for binding in core.public_bindings:
        if binding.scope != 0:
            _fail("Refused", "F0V2B2C1B5B2-R-BINDING-SCOPE", "binding is not root")
        _value_type(core, outputs, binding.value)
        triple = (binding.scope, binding.binding_class, binding.value)
        if triple in binding_triples:
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-DUPLICATE-BINDING",
                "public binding triple repeats",
            )
        binding_triples.add(triple)
        if type(binding.value) is base.PublicInputRef:
            bound_public.add(binding.value.ordinal)
    if bound_public != set(range(len(core.public_inputs))):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-BINDING-COMPLETENESS",
            "public-input binding coverage is incomplete",
        )

    check_positions: dict[int, list[int]] = {
        index: [] for index in range(len(core.checks))
    }
    reduction_positions: dict[int, list[int]] = {
        index: [] for index in range(len(core.reductions))
    }
    terminal_positions: dict[int, list[int]] = {
        index: [] for index in range(len(core.terminals))
    }
    available: set[object] = {
        base.PublicInputRef(index) for index in range(len(core.public_inputs))
    }
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        if occurrence.scope != 0:
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-OCCURRENCE-SCOPE",
                "occurrence is not in the isolated root scope",
            )
        guard_reads: tuple[object, ...] = ()
        if type(occurrence.guard) is base.EvaluateGuard:
            guard_reads = occurrence.guard.inputs
            observed = tuple(_value_type(core, outputs, item) for item in guard_reads)
            function = functions.get(occurrence.guard.algorithm)
            if (
                function is None
                or function.inputs != observed
                or function.output != k1.BOOL
                or function.failures
            ):
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B5B2-K-GUARD-ABI",
                    "Guard is not one exact total Boolean function",
                )
        elif type(occurrence.guard) is not base.AlwaysGuard:
            _fail("Malformed", "F0V2B2C1B5B2-M-GUARD", "Guard carrier differs")
        if any(item not in available for item in guard_reads):
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-GUARD-AVAILABILITY",
                "Guard reads a future or absent value",
            )

        effect = occurrence.effect
        reads: tuple[object, ...]
        if type(effect) is base.CheckEffect:
            if effect.check not in check_positions:
                _fail("Refused", "F0V2B2C1B5B2-R-CHECK-REF", "Check is absent")
            check_positions[effect.check].append(occurrence_ref)
            check = core.checks[effect.check]
            reads = check.inputs
            observed = tuple(_value_type(core, outputs, item) for item in reads)
            function = functions.get(check.algorithm)
            if (
                function is None
                or function.inputs != observed
                or function.output != k1.BOOL
                or function.failures
            ):
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B5B2-K-CHECK-ABI",
                    "Check is not one exact total Boolean function",
                )
        elif type(effect) is b3.ApplyReductionEffect:
            if effect.reduction not in reduction_positions:
                _fail(
                    "Refused",
                    "F0V2B2C1B5B2-R-REDUCTION-REF",
                    "Reduction is absent",
                )
            reduction_positions[effect.reduction].append(occurrence_ref)
            reads = core.reductions[effect.reduction].side_inputs
        elif type(effect) is base.TerminalEffect:
            if effect.terminal not in terminal_positions:
                _fail(
                    "Refused",
                    "F0V2B2C1B5B2-R-TERMINAL-REF",
                    "Terminal is absent",
                )
            terminal_positions[effect.terminal].append(occurrence_ref)
            reads = core.terminals[effect.terminal].public_outputs
        else:  # pragma: no cover - decoder closes the sum
            _fail("Unsupported", "F0V2B2C1B5B2-U-EFFECT", "effect differs")
        if any(item not in available for item in reads):
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-VALUE-AVAILABILITY",
                "effect reads a future or absent value",
            )
        for output in range(len(outputs[occurrence_ref])):
            available.add(base.OccurrenceOutputRef(occurrence_ref, output))

    exact_positions: list[dict[int, int]] = []
    for positions, label in (
        (check_positions, "CHECK"),
        (reduction_positions, "REDUCTION"),
        (terminal_positions, "TERMINAL"),
    ):
        if any(len(items) != 1 for items in positions.values()):
            _fail(
                "Refused",
                f"F0V2B2C1B5B2-R-{label}-BACKLINK",
                f"{label} occurrence backlink is not one-to-one",
            )
        exact_positions.append({key: value[0] for key, value in positions.items()})
    exact_checks, exact_reductions, exact_terminals = exact_positions

    output_claims: dict[tuple[int, int], int] = {}
    for claim_ref, claim in enumerate(core.claims):
        if type(claim.usage) is not base.ClaimUsage:
            _fail(
                "Malformed",
                "F0V2B2C1B5B2-M-CLAIM-USAGE",
                "Claim usage differs",
            )
        if claim.scope != 0:
            _fail("Refused", "F0V2B2C1B5B2-R-CLAIM-SCOPE", "Claim is not root")
        if type(claim.source) is b3.InitialClaimSource:
            if not 0 <= claim.source.binding < len(core.public_bindings):
                _fail(
                    "Refused",
                    "F0V2B2C1B5B2-R-CLAIM-SOURCE",
                    "initial Claim binding is absent",
                )
            binding = core.public_bindings[claim.source.binding]
            if binding.binding_class is not base.BindingClass.STATEMENT:
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B5B2-K-CLAIM-SOURCE",
                    "initial Claim does not cite a Statement binding",
                )
        elif type(claim.source) is b3.ReductionOutputClaimSource:
            source = claim.source
            if not 0 <= source.reduction < len(core.reductions):
                _fail(
                    "Refused",
                    "F0V2B2C1B5B2-R-CLAIM-SOURCE",
                    "Claim source Reduction is absent",
                )
            reduction = core.reductions[source.reduction]
            if not 0 <= source.output_ordinal < len(reduction.output_contracts):
                _fail(
                    "Refused",
                    "F0V2B2C1B5B2-R-CLAIM-OUTPUT",
                    "Claim output ordinal is absent",
                )
            if (
                claim.contract != reduction.output_contracts[source.output_ordinal]
                or claim.scope != reduction.scope
            ):
                _fail(
                    "KindMismatch",
                    "F0V2B2C1B5B2-K-CLAIM-OUTPUT",
                    "Claim and Reduction output contracts differ",
                )
            coordinate = (source.reduction, source.output_ordinal)
            if coordinate in output_claims:
                _fail(
                    "Refused",
                    "F0V2B2C1B5B2-R-CLAIM-SSA",
                    "two Claims share one Reduction output",
                )
            output_claims[coordinate] = claim_ref
        else:
            _fail(
                "Malformed",
                "F0V2B2C1B5B2-M-CLAIM-SOURCE",
                "Claim source differs",
            )
    expected_outputs = {
        (reduction_ref, ordinal)
        for reduction_ref, reduction in enumerate(core.reductions)
        for ordinal in range(len(reduction.output_contracts))
    }
    if set(output_claims) != expected_outputs:
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-CLAIM-OUTPUT-CLOSURE",
            "Reduction outputs and Claim sources are not a bijection",
        )

    for terminal in core.terminals:
        if type(terminal) is not TerminalDecl:
            _fail(
                "Malformed",
                "F0V2B2C1B5B2-M-TERMINAL",
                "Terminal carrier differs",
            )
        if type(terminal.verdict) is not base.TerminalVerdict:
            _fail(
                "Malformed",
                "F0V2B2C1B5B2-M-VERDICT",
                "Terminal verdict differs",
            )
        _canonical_refs(terminal.required_true_checks, "required Checks")
        _canonical_refs(terminal.required_applied_reductions, "required Reductions")
        _canonical_refs(terminal.terminal_claims, "terminal Claims")

    try:
        analysis = terminal_contracts.analyze(
            _terminal_program(core, environment.algorithm_preimages)
        )
    except terminal_contracts.ContractFailure as error:
        _fail(
            error.outcome,
            "F0V2B2C1B5B2-R-TERMINAL-CONTRACT",
            f"{error.code}: {error.detail}",
        )

    claim_uses: dict[int, list[tuple[str, int, int, int]]] = {
        index: [] for index in range(len(core.claims))
    }
    for reduction_ref, reduction in enumerate(core.reductions):
        occurrence_ref = exact_reductions[reduction_ref]
        for ordinal, claim_ref in enumerate(reduction.input_claims):
            if claim_ref not in claim_uses:
                _fail(
                    "Refused",
                    "F0V2B2C1B5B2-R-CLAIM-REF",
                    "Reduction input Claim is absent",
                )
            claim_uses[claim_ref].append(
                ("reduction", occurrence_ref, reduction_ref, ordinal)
            )
    for terminal_ref, terminal in enumerate(core.terminals):
        occurrence_ref = exact_terminals[terminal_ref]
        for ordinal, claim_ref in enumerate(terminal.terminal_claims):
            if claim_ref not in claim_uses:
                _fail(
                    "Refused",
                    "F0V2B2C1B5B2-R-CLAIM-REF",
                    "Terminal Claim is absent",
                )
            claim_uses[claim_ref].append(
                ("terminal", occurrence_ref, terminal_ref, ordinal)
            )
    return ValidationEvidence(
        outputs,
        ((0,),),
        MappingProxyType(exact_checks),
        MappingProxyType(exact_reductions),
        MappingProxyType(exact_terminals),
        MappingProxyType({key: tuple(value) for key, value in claim_uses.items()}),
        analysis,
    )


def admit_core(candidate: object, environment: object) -> AdmissionResult:
    try:
        if type(candidate) is not b2c0.CanonicalCoreCandidate:
            _fail("Malformed", "F0V2B2C1B5B2-M-REQUEST", "Core request differs")
        if type(environment) is not base.Environment:
            _fail(
                "Malformed",
                "F0V2B2C1B5B2-M-ENVIRONMENT",
                "environment carrier differs",
            )
        expected_profile = candidate_profile_artifact().profile_id
        if candidate.profile_id != environment.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2C1B5B2-K-REQUEST-PROFILE",
                "request and environment profiles differ",
            )
        if environment.profile_id != expected_profile:
            _fail(
                "KindMismatch",
                "F0V2B2C1B5B2-K-CANDIDATE-PROFILE",
                "Core does not use the synthetic B5B2 profile",
            )
        if set(environment.profile_preimages) != {expected_profile}:
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-PROFILE-CLOSURE",
                "candidate profile-preimage closure is not exact",
            )
        profile, domain, domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "B5B2 expanded-Terminal Core"
        )
        if profile != candidate.profile_id:
            _fail(
                "KindMismatch",
                "F0V2B2C1B5B2-K-BODY-PROFILE",
                "profiled Core body names another profile",
            )
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_CORE_KIND
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B5B2-K-CORE-ID",
                "Core ID has another kind",
            )
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C1B5B2-M-CORE-ID", str(error))
        core = decode_core(domain)
        closure = b2c0.snapshot_environment(environment)
        functions = _authenticate_algorithms(core, environment)
        validation = _validate_core(core, environment, functions)
        _graph_value, graph_evidence = _graph(core, validation)
        handle = b2c0.AdmittedCoreSnapshot(
            candidate.asserted_id.internal_reference(),
            candidate.profile_id.internal_reference(),
            bytes(candidate.profiled_body),
            bytes(domain_body),
            closure,
            (
                ("slice", "F0-V2B2C1B5B2"),
                ("core", core),
                ("validation", validation),
                ("graph_evidence", graph_evidence),
            ),
            EVALUATOR_FINGERPRINT,
            tuple(range(1, 18)),
            b2c0._CORE_ISSUER,
        )
        return AdmissionResult(
            "Affirmative",
            "F0V2B2C1B5B2-A-CORE-ADMITTED",
            "exact candidate bytes passed expanded-Terminal owner admission",
            handle,
        )
    except FamilyFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return AdmissionResult("CheckerFailure", "F0V2B2C1B5B2-CHECKER", str(error))


def _retained_core(handle: object) -> tuple[object, ValidationEvidence]:
    if (
        type(handle) is not b2c0.AdmittedCoreSnapshot
        or not handle._issued_by(b2c0._CORE_ISSUER)
        or handle.evaluator_fingerprint != EVALUATOR_FINGERPRINT
    ):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-CORE-AUTHORITY",
            "Core authority belongs to another evaluator",
        )
    summary = dict(handle.structural_summary)
    if (
        summary.get("slice") != "F0-V2B2C1B5B2"
        or type(summary.get("core")) is not base.InteractiveCore
        or type(summary.get("validation")) is not ValidationEvidence
    ):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-RETAINED-FACTS",
            "retained owner facts differ",
        )
    core = summary["core"]
    profile = k1.decode_content_reference(handle.profile_reference)
    if core_profiled_body(core, profile) != handle.profiled_body:
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-RETAINED-BODY",
            "retained Core does not reproduce exact bytes",
        )
    return core, summary["validation"]


def admit_fresh_protocol(
    core_handle: object, candidate: object, environment: object
) -> AdmissionResult:
    try:
        _retained_core(core_handle)
        if type(candidate) is not b2c0.CanonicalFreshProtocolCandidate:
            _fail(
                "Malformed",
                "F0V2B2C1B5B2-M-PROTOCOL-REQUEST",
                "Protocol request differs",
            )
        profile, domain, _domain_body = b2c0._strict_profiled_body(
            candidate.profiled_body, "B5B2 Fresh Protocol"
        )
        if (
            profile.internal_reference() != core_handle.profile_reference
            or candidate.profile_id.internal_reference()
            != core_handle.profile_reference
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B5B2-K-PROTOCOL-PROFILE",
                "Protocol profile differs from its Core",
            )
        core_ref, interpretation = b2c0._record(domain, (0, 1), "Fresh Protocol")
        referenced_core = b2c0._content_ref(core_ref, "Protocol Core")
        if referenced_core.internal_reference() != core_handle.core_reference:
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-PROTOCOL-CORE",
                "Protocol names another Core",
            )
        interpretation_case, payload = b2c0._variant(
            interpretation, (0,), "Fresh interpretation"
        )
        if interpretation_case != 0:  # pragma: no cover - parser closes the sum
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-INTERPRETATION",
                "Protocol is not Fresh",
            )
        b2c0._unit(payload, "Fresh interpretation payload")
        if (
            type(candidate.asserted_id) is not k1.TypedContentId
            or candidate.asserted_id.subject_kind != base.TARGET_PROTOCOL_KIND
        ):
            _fail(
                "KindMismatch",
                "F0V2B2C1B5B2-K-PROTOCOL-ID",
                "Protocol ID has another kind",
            )
        try:
            k1.authenticate_content_id(
                candidate.asserted_id,
                candidate.profiled_body,
                environment.prior_meta_preimages,
            )
        except Exception as error:
            _fail("Malformed", "F0V2B2C1B5B2-M-PROTOCOL-ID", str(error))
        closure = b2c0.snapshot_environment(environment)
        if closure.fingerprint != core_handle.closure.fingerprint:
            _fail(
                "Refused",
                "F0V2B2C1B5B2-R-CLOSURE-PAIR",
                "Core and Protocol closure snapshots differ",
            )
        handle = b2c0.AdmittedFreshProtocolSnapshot(
            candidate.asserted_id.internal_reference(),
            candidate.profile_id.internal_reference(),
            bytes(candidate.profiled_body),
            core_handle,
            closure.fingerprint,
            EVALUATOR_FINGERPRINT,
            b2c0._PROTOCOL_ISSUER,
        )
        return AdmissionResult(
            "Affirmative",
            "F0V2B2C1B5B2-A-FRESH-ADMITTED",
            "Fresh Protocol is paired to the exact candidate Core and evaluator",
            handle,
        )
    except FamilyFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except b2c0.SnapshotFailure as error:
        return AdmissionResult(error.outcome, error.code, error.detail)
    except Exception as error:  # pragma: no cover - fail-closed defect lane
        return AdmissionResult("CheckerFailure", "F0V2B2C1B5B2-CHECKER", str(error))


def _pc_value(node: tuple[int, ...]) -> dict[str, Any]:
    tag, *arguments = node
    if tag in (8, 12, 13):
        if len(arguments) != 2:
            _fail("CheckerFailure", "F0V2B2C1B5B2-C-PCNODE", "output arity differs")
        return foundation._v(
            tag,
            {
                0: foundation._ordinal("occurrence-ref-body-v0", arguments[0]),
                1: arguments[1],
            },
        )
    compiler = {
        0: "public-input-ref-body-v0",
        4: "scope-ref-body-v0",
        5: "binding-ref-body-v0",
        6: "occurrence-ref-body-v0",
        7: "occurrence-ref-body-v0",
        9: "claim-ref-body-v0",
        10: "reduction-ref-body-v0",
        11: "terminal-ref-body-v0",
    }.get(tag)
    if compiler is None or len(arguments) != 1:
        _fail(
            "CheckerFailure",
            "F0V2B2C1B5B2-C-PCNODE",
            "PCNode is outside the selected graph carrier",
        )
    return foundation._v(tag, foundation._ordinal(compiler, arguments[0]))


def _pc_key(node: tuple[int, ...]) -> bytes:
    return codec.encode_value(_PC_NODE_SCHEMA, _pc_value(node))


def _edge_value(edge: tuple[tuple[int, ...], tuple[int, ...]]) -> dict[int, Any]:
    return {0: _pc_value(edge[0]), 1: _pc_value(edge[1])}


def _edge_key(edge: tuple[tuple[int, ...], tuple[int, ...]]) -> bytes:
    return codec.encode_value(_PC_EDGE_SCHEMA, _edge_value(edge))


def _graph(
    core: object, validation: ValidationEvidence
) -> tuple[dict[int, Any], dict[str, Any]]:
    incoming: dict[tuple[int, ...], set[tuple[int, ...]]] = {}
    outgoing: dict[tuple[int, ...], set[tuple[int, ...]]] = {}

    def node(value: tuple[int, ...]) -> tuple[int, ...]:
        incoming.setdefault(value, set())
        outgoing.setdefault(value, set())
        return value

    def edge(source: tuple[int, ...], target: tuple[int, ...]) -> None:
        source, target = node(source), node(target)
        incoming[target].add(source)
        outgoing[source].add(target)

    for ordinal in range(len(core.public_inputs)):
        node((0, ordinal))
    node((4, 0))
    for binding_ref, binding in enumerate(core.public_bindings):
        edge((4, binding.scope), (5, binding_ref))
        edge(_producer_node(binding.value), (5, binding_ref))

    prior_terminals: list[tuple[int, ...]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        activity = node((6, occurrence_ref))
        effect_node = node((7, occurrence_ref))
        edge((4, occurrence.scope), activity)
        if type(occurrence.guard) is base.EvaluateGuard:
            for reference in occurrence.guard.inputs:
                edge(_producer_node(reference), activity)
        for terminal_node in prior_terminals:
            edge(terminal_node, activity)
        edge(activity, effect_node)
        effect = occurrence.effect
        if type(effect) is base.CheckEffect:
            for reference in core.checks[effect.check].inputs:
                edge(_producer_node(reference), effect_node)
        elif type(effect) is b3.ApplyReductionEffect:
            reduction = core.reductions[effect.reduction]
            for claim_ref in reduction.input_claims:
                edge((9, claim_ref), effect_node)
            edge(effect_node, (10, effect.reduction))
        elif type(effect) is base.TerminalEffect:
            terminal = core.terminals[effect.terminal]
            for reference in terminal.public_outputs:
                edge(_producer_node(reference), effect_node)
            for check_ref in terminal.required_true_checks:
                edge((8, validation.check_positions[check_ref], 0), effect_node)
            for reduction_ref in terminal.required_applied_reductions:
                edge((10, reduction_ref), effect_node)
            for claim_ref in terminal.terminal_claims:
                edge((9, claim_ref), effect_node)
            terminal_node = node((11, effect.terminal))
            edge(effect_node, terminal_node)
            prior_terminals.append(terminal_node)
        for output_ordinal in range(len(validation.outputs[occurrence_ref])):
            edge(effect_node, (8, occurrence_ref, output_ordinal))

    for claim_ref, claim in enumerate(core.claims):
        if type(claim.source) is b3.InitialClaimSource:
            edge((5, claim.source.binding), (9, claim_ref))
        else:
            edge((10, claim.source.reduction), (9, claim_ref))
    for reduction_ref, occurrence_ref in validation.reduction_positions.items():
        edge((7, occurrence_ref), (10, reduction_ref))

    remaining = {item: set(parents) for item, parents in incoming.items()}
    available = sorted(
        (item for item, parents in remaining.items() if not parents), key=_pc_key
    )
    topological: list[tuple[int, ...]] = []
    while available:
        current = available.pop(0)
        topological.append(current)
        for child in outgoing[current]:
            remaining[child].remove(current)
            if (
                not remaining[child]
                and child not in topological
                and child not in available
            ):
                available.append(child)
        available.sort(key=_pc_key)
    if len(topological) != len(incoming):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-PCGRAPH-CYCLE",
            "expanded-Terminal PCGraph is cyclic",
        )
    classes: dict[tuple[int, ...], int] = {}
    for current in topological:
        classes[current] = max((classes[item] for item in incoming[current]), default=0)

    activity_sinks = {(6, index) for index in range(len(core.occurrences))}
    check_sinks = {(7, item) for item in validation.check_positions.values()}
    reduction_sinks = {(10, index) for index in range(len(core.reductions))}
    terminal_sinks = {(11, index) for index in range(len(core.terminals))}
    sinks = activity_sinks | check_sinks | reduction_sinks | terminal_sinks
    acceptance = (
        check_sinks
        | reduction_sinks
        | {
            (11, terminal_ref)
            for terminal_ref, terminal in enumerate(core.terminals)
            if terminal.verdict is base.TerminalVerdict.ACCEPT
        }
    )
    ordered_nodes = sorted(incoming, key=_pc_key)
    ordered_edges = sorted(
        (
            (source, target)
            for target, parents in incoming.items()
            for source in parents
        ),
        key=_edge_key,
    )
    value = {
        0: [_pc_value(item) for item in ordered_nodes],
        1: [_edge_value(item) for item in ordered_edges],
        2: [_pc_value(item) for item in topological],
        3: [
            {0: _pc_value(item), 1: foundation._v(classes[item])}
            for item in ordered_nodes
        ],
        4: [_pc_value(item) for item in sorted(sinks, key=_pc_key)],
        5: [_pc_value(item) for item in sorted(acceptance, key=_pc_key)],
        6: [],
    }
    return value, {
        "nodes": len(incoming),
        "edges": len(ordered_edges),
        "eligible": all(classes[item] in (0, 1) for item in sinks),
        "check_sinks": len(check_sinks),
        "reduction_sinks": len(reduction_sinks),
        "terminal_sinks": len(terminal_sinks),
    }


def _effect_value(effect: object) -> dict[str, Any]:
    if type(effect) is base.CheckEffect:
        return foundation._v(3, foundation._ordinal("check-ref-body-v0", effect.check))
    if type(effect) is b3.ApplyReductionEffect:
        return foundation._v(
            4, foundation._ordinal("reduction-ref-body-v0", effect.reduction)
        )
    if type(effect) is base.TerminalEffect:
        return foundation._v(
            5, foundation._ordinal("terminal-ref-body-v0", effect.terminal)
        )
    _fail("Unsupported", "F0V2B2C1B5B2-U-EFFECT", "effect differs")
    raise AssertionError("unreachable")


def _law(name: str) -> dict[str, str]:
    return {
        "profile": candidate_profile_artifact().profile_id.digest.hex(),
        "kind": "pir.semantic-law",
        "name": name,
    }


def _claim_creation_value(
    core: object, validation: ValidationEvidence, source: object
) -> dict[str, Any]:
    if type(source) is b3.InitialClaimSource:
        return foundation._v(
            0,
            {
                0: foundation._ordinal("binding-ref-body-v0", source.binding),
                1: foundation._v(0),
            },
        )
    return foundation._v(
        1,
        {
            0: foundation._ordinal(
                "occurrence-ref-body-v0",
                validation.reduction_positions[source.reduction],
            ),
            1: foundation._ordinal("reduction-ref-body-v0", source.reduction),
            2: source.output_ordinal,
        },
    )


def project_views(core_handle: object, protocol_handle: object) -> dict[str, Any]:
    core, validation = _retained_core(core_handle)
    if (
        type(protocol_handle) is not b2c0.AdmittedFreshProtocolSnapshot
        or not protocol_handle._issued_by(b2c0._PROTOCOL_ISSUER)
        or protocol_handle.core_handle is not core_handle
        or protocol_handle.profile_reference != core_handle.profile_reference
        or protocol_handle.closure_fingerprint != core_handle.closure.fingerprint
        or protocol_handle.evaluator_fingerprint != EVALUATOR_FINGERPRINT
    ):
        _fail(
            "Refused",
            "F0V2B2C1B5B2-R-PROTOCOL-AUTHORITY",
            "Protocol authority differs",
        )
    core_identifier = k1.decode_content_reference(core_handle.core_reference)
    protocol_identifier = k1.decode_content_reference(
        protocol_handle.protocol_reference
    )
    core_atom = foundation._identifier("core-id-body-v0", core_identifier)
    protocol_atom = foundation._identifier("protocol-id-body-v0", protocol_identifier)
    graph, graph_evidence = _graph(core, validation)

    public_binding = {
        0: core_atom,
        1: [
            {
                0: foundation._ordinal("scope-ref-body-v0", 0),
                1: foundation._v(0),
                2: foundation._v(0),
                3: [foundation._ordinal("scope-ref-body-v0", 0)],
            }
        ],
        2: [
            {
                0: foundation._ordinal("binding-ref-body-v0", binding_ref),
                1: foundation._ordinal("scope-ref-body-v0", binding.scope),
                2: foundation._v(binding.binding_class.value),
                3: foundation._value_ref(binding.value),
                4: foundation._value_type_body(
                    _value_type(core, validation.outputs, binding.value)
                ),
            }
            for binding_ref, binding in enumerate(core.public_bindings)
        ],
    }
    strategy = {
        0: core_atom,
        1: [],
        2: _law("core-admission-v0"),
        3: [],
        4: [],
    }
    public_coin = {
        0: core_atom,
        1: graph,
        2: graph_evidence["eligible"],
        3: [],
        4: [],
    }

    value_rows: list[dict[int, Any]] = [
        {
            0: foundation._value_ref(base.PublicInputRef(input_ref)),
            1: foundation._value_type_body(declaration.value_type),
            2: [],
        }
        for input_ref, declaration in enumerate(core.public_inputs)
    ]
    occurrence_rows: list[dict[int, Any]] = []
    for occurrence_ref, occurrence in enumerate(core.occurrences):
        occurrence_rows.append(
            {
                0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [foundation._ordinal("scope-ref-body-v0", 0)],
                2: foundation._guard_body(occurrence.guard),
                3: _effect_value(occurrence.effect),
                4: [
                    foundation._value_type_body(item)
                    for item in validation.outputs[occurrence_ref]
                ],
            }
        )
        for output_ordinal, output_type in enumerate(
            validation.outputs[occurrence_ref]
        ):
            predecessors = (
                core.checks[occurrence.effect.check].inputs
                if type(occurrence.effect) is base.CheckEffect
                else ()
            )
            value_rows.append(
                {
                    0: foundation._value_ref(
                        base.OccurrenceOutputRef(occurrence_ref, output_ordinal)
                    ),
                    1: foundation._value_type_body(output_type),
                    2: [foundation._value_ref(item) for item in predecessors],
                }
            )
    check_rows = [
        {
            0: foundation._ordinal("check-ref-body-v0", check_ref),
            1: foundation._identifier("algorithm-ref-body-v0", check.algorithm),
            2: foundation._identifier(
                "evaluation-contract-id-body-v0", check.evaluation_contract
            ),
            3: [foundation._value_ref(item) for item in check.inputs],
            4: foundation._ordinal(
                "occurrence-ref-body-v0", validation.check_positions[check_ref]
            ),
        }
        for check_ref, check in enumerate(core.checks)
    ]
    terminal_rows = [
        {
            0: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
            1: foundation._v(terminal.verdict.value),
            2: [foundation._value_ref(item) for item in terminal.public_outputs],
            3: [
                foundation._ordinal("check-ref-body-v0", item)
                for item in terminal.required_true_checks
            ],
            4: [
                foundation._ordinal("reduction-ref-body-v0", item)
                for item in terminal.required_applied_reductions
            ],
            5: [
                foundation._ordinal("claim-ref-body-v0", item)
                for item in terminal.terminal_claims
            ],
            6: foundation._ordinal(
                "occurrence-ref-body-v0", validation.terminal_positions[terminal_ref]
            ),
        }
        for terminal_ref, terminal in enumerate(core.terminals)
    ]
    effect = {
        0: core_atom,
        1: occurrence_rows,
        2: value_rows,
        3: [],
        4: [],
        5: check_rows,
        6: terminal_rows,
        7: [],
    }

    claim_rows: list[dict[int, Any]] = []
    for claim_ref, claim in enumerate(core.claims):
        uses: list[dict[str, Any]] = []
        for kind, occurrence_ref, owner_ref, ordinal in sorted(
            validation.claim_uses[claim_ref],
            key=lambda item: (item[1], item[0], item[3]),
        ):
            uses.append(
                foundation._v(
                    0 if kind == "reduction" else 1,
                    {
                        0: foundation._ordinal(
                            "occurrence-ref-body-v0", occurrence_ref
                        ),
                        1: foundation._ordinal(
                            "reduction-ref-body-v0"
                            if kind == "reduction"
                            else "terminal-ref-body-v0",
                            owner_ref,
                        ),
                        2: ordinal,
                    },
                )
            )
        claim_rows.append(
            {
                0: foundation._ordinal("claim-ref-body-v0", claim_ref),
                1: foundation._module_ref(claim.contract),
                2: foundation._ordinal("scope-ref-body-v0", claim.scope),
                3: foundation._v(claim.usage.value),
                4: b3._claim_source_value(claim.source),
                5: _claim_creation_value(core, validation, claim.source),
                6: uses,
            }
        )
    reduction_rows = [
        {
            0: foundation._ordinal("reduction-ref-body-v0", reduction_ref),
            1: foundation._module_ref(reduction.contract),
            2: foundation._ordinal("scope-ref-body-v0", reduction.scope),
            3: foundation._ordinal(
                "occurrence-ref-body-v0",
                validation.reduction_positions[reduction_ref],
            ),
            4: [
                foundation._ordinal("claim-ref-body-v0", item)
                for item in reduction.input_claims
            ],
            5: [],
            6: [],
            7: [],
            8: [foundation._module_ref(item) for item in reduction.output_contracts],
        }
        for reduction_ref, reduction in enumerate(core.reductions)
    ]
    disposition_rows = [
        {
            0: foundation._ordinal(
                "occurrence-ref-body-v0", validation.terminal_positions[terminal_ref]
            ),
            1: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
            2: foundation._ordinal("claim-ref-body-v0", claim_ref),
            3: foundation._v(
                0 if terminal.verdict is base.TerminalVerdict.ACCEPT else 1
            ),
        }
        for terminal_ref, terminal in enumerate(core.terminals)
        for claim_ref in terminal.terminal_claims
    ]
    requirement_rows = [
        {
            0: foundation._ordinal(
                "occurrence-ref-body-v0", validation.terminal_positions[terminal_ref]
            ),
            1: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
            2: [
                foundation._ordinal("reduction-ref-body-v0", item)
                for item in terminal.required_applied_reductions
            ],
        }
        for terminal_ref, terminal in enumerate(core.terminals)
    ]
    claim_reduction = {
        0: core_atom,
        1: claim_rows,
        2: reduction_rows,
        3: disposition_rows,
        4: requirement_rows,
    }

    runtime = {
        0: [
            {
                0: foundation._ordinal("occurrence-ref-body-v0", occurrence_ref),
                1: [foundation._value_type_body(item) for item in output_types],
            }
            for occurrence_ref, output_types in enumerate(validation.outputs)
        ],
        1: [],
        2: [],
        3: [
            {
                0: foundation._ordinal("terminal-ref-body-v0", terminal_ref),
                1: foundation._ordinal(
                    "occurrence-ref-body-v0",
                    validation.terminal_positions[terminal_ref],
                ),
                2: foundation._v(terminal.verdict.value),
                3: [
                    foundation._value_type_body(
                        _value_type(core, validation.outputs, item)
                    )
                    for item in terminal.public_outputs
                ],
            }
            for terminal_ref, terminal in enumerate(core.terminals)
        ],
    }
    execution = {
        0: protocol_atom,
        1: core_atom,
        2: foundation._v(0),
        3: _law("core-admission-v0"),
        4: [],
        5: _law("execution-and-replay-v0"),
        6: runtime,
        7: foundation._v(0),
        8: _law("execution-and-replay-v0"),
        9: _law("run-view-issuance-v0"),
    }
    return {
        "PublicBindingView": public_binding,
        "StrategyDecisionView": strategy,
        "PublicCoinView": public_coin,
        "EffectView": effect,
        "ClaimReductionView": claim_reduction,
        "ExecutionView": execution,
    }


def _bool_literal(value: bool) -> object:
    return k1.Literal(k1.admit_value(k1.BOOL, value))


def identity_algorithm() -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol("F0V2B2C1B5B2BooleanIdentity"),
        (k1.BOOL,),
        k1.Variable(0, k1.BOOL),
    )


def conjunction_algorithm() -> object:
    return k1.CanonicalAlgorithm(
        k1.Symbol("F0V2B2C1B5B2BooleanConjunction"),
        (k1.BOOL, k1.BOOL),
        k1.Conditional(
            k1.Variable(0, k1.BOOL),
            k1.Variable(1, k1.BOOL),
            _bool_literal(False),
        ),
    )


def environment_for(
    core: object, module: object, algorithms: tuple[object, ...]
) -> object:
    """Build the exact candidate-profile closure for a freshly encoded Core."""

    profile = candidate_profile_artifact()
    algorithm_map = {item.identity: item for item in algorithms}
    algorithm_refs, contract_refs = _ordinary_references(core)
    if set(algorithm_map) != set(algorithm_refs):
        raise AssertionError("fixture algorithm closure differs from Core references")
    contract = k1.DEFAULT_EVALUATION_CONTRACT
    if set(contract_refs) != {contract.identity}:
        raise AssertionError("fixture contract closure differs from Core references")
    module_ids = {reference.module for reference in _module_references(core)}
    if module_ids != {module.identity}:
        raise AssertionError("fixture module closure differs from Core references")
    return base.Environment(
        profile.profile_id,
        MappingProxyType({profile.profile_id: profile.profile}),
        MappingProxyType({module.identity: module}),
        MappingProxyType(algorithm_map),
        MappingProxyType(
            {identifier: MappingProxyType({}) for identifier in algorithm_map}
        ),
        MappingProxyType({contract.identity: contract}),
    )


def candidate_for(
    core: object, module: object, algorithms: tuple[object, ...]
) -> tuple[object, object]:
    """Rebuild exact closure and candidate identity after a typed mutation."""

    environment = environment_for(core, module, algorithms)
    return environment, make_candidate(core, environment.profile_id)


def fixture() -> Fixture:
    """Return the branch-complete expanded-Terminal witness."""

    module = b3.protocol_module()
    module_id = module.identity
    claim_input = base.ModuleDeclarationRef(module_id, "pir.claim-contract", 0)
    claim_output = base.ModuleDeclarationRef(module_id, "pir.claim-contract", 1)
    reduction_a = base.ModuleDeclarationRef(module_id, "pir.reduction-contract", 0)
    reduction_b = base.ModuleDeclarationRef(module_id, "pir.reduction-contract", 1)
    identity = identity_algorithm()
    conjunction = conjunction_algorithm()
    contract = k1.DEFAULT_EVALUATION_CONTRACT.identity
    public_inputs = tuple(base.InputDecl(k1.BOOL) for _ in range(3))
    bindings = (
        base.PublicBindingDecl(0, base.BindingClass.STATEMENT, base.PublicInputRef(0)),
        base.PublicBindingDecl(
            0, base.BindingClass.SESSION_CONTEXT, base.PublicInputRef(1)
        ),
        base.PublicBindingDecl(
            0, base.BindingClass.SESSION_CONTEXT, base.PublicInputRef(2)
        ),
    )
    claims = (
        b3.ClaimDecl(
            claim_input,
            0,
            base.ClaimUsage.LINEAR,
            b3.InitialClaimSource(0),
        ),
        b3.ClaimDecl(
            claim_output,
            0,
            base.ClaimUsage.REUSABLE,
            b3.ReductionOutputClaimSource(0, 0),
        ),
        b3.ClaimDecl(
            claim_output,
            0,
            base.ClaimUsage.REUSABLE,
            b3.ReductionOutputClaimSource(1, 0),
        ),
    )
    reductions = (
        b3.ReductionDecl(reduction_a, 0, (0,), (), (), (), (claim_output,)),
        b3.ReductionDecl(reduction_b, 0, (0,), (), (), (), (claim_output,)),
    )
    terminals = (
        TerminalDecl(
            base.TerminalVerdict.ACCEPT,
            (base.PublicInputRef(1),),
            (0,),
            (0,),
            (1,),
        ),
        TerminalDecl(
            base.TerminalVerdict.ABORT,
            (base.PublicInputRef(2),),
            (),
            (1,),
            (2,),
        ),
        TerminalDecl(
            base.TerminalVerdict.REJECT,
            (base.PublicInputRef(0),),
            (),
            (1,),
            (2,),
        ),
    )
    accept_guard = base.EvaluateGuard(
        conjunction.identity,
        contract,
        (base.OccurrenceOutputRef(0, 0), base.PublicInputRef(1)),
    )
    abort_guard = base.EvaluateGuard(
        identity.identity,
        contract,
        (base.PublicInputRef(2),),
    )
    occurrences = (
        base.OccurrenceDecl(0, base.AlwaysGuard(), base.CheckEffect(0)),
        base.OccurrenceDecl(0, accept_guard, b3.ApplyReductionEffect(0)),
        base.OccurrenceDecl(0, accept_guard, base.TerminalEffect(0)),
        base.OccurrenceDecl(0, base.AlwaysGuard(), b3.ApplyReductionEffect(1)),
        base.OccurrenceDecl(0, abort_guard, base.TerminalEffect(1)),
        base.OccurrenceDecl(0, base.AlwaysGuard(), base.TerminalEffect(2)),
    )
    provisional = base.InteractiveCore(
        (),
        public_inputs,
        (),
        (),
        (),
        (base.ScopeDecl(None, None),),
        bindings,
        (),
        (),
        (base.CheckDecl(identity.identity, contract, (base.PublicInputRef(0),)),),
        claims,
        reductions,
        terminals,
        occurrences,
    )
    used_modules = tuple(
        sorted(
            {reference.module for reference in _module_references(provisional)},
            key=lambda item: item.internal_reference(),
        )
    )
    core = replace(provisional, used_modules=used_modules)
    algorithms = (identity, conjunction)
    environment, candidate = candidate_for(core, module, algorithms)
    protocol_candidate = b2c0.make_protocol_candidate(
        candidate.asserted_id, environment.profile_id
    )
    return Fixture(
        environment,
        core,
        candidate,
        protocol_candidate,
        module,
        algorithms,
    )
