#!/usr/bin/env python3
"""Run the F0-V2B2C1B5B1 Terminal owner-contract research gate."""

from __future__ import annotations

import argparse
from copy import deepcopy
from dataclasses import dataclass
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
MODEL = HERE / "model.py"
INDEPENDENT = HERE / "independent.py"
EXPECTED = HERE / "expected-findings.json"
PREDECESSOR_EXPECTED = (
    ROOT
    / "evaluation/formal-source-terminal-path-algebra-f0v2b2c1b5a/expected-findings.json"
)
FOUNDATION_SOURCE = ROOT / "docs-next/foundation/executable-foundations.md"
TARGET_SOURCE = ROOT / "docs-next/pir/interactive-core.md"
AGGREGATE = "F0V2B2C1B5B1-A-TERMINAL-CONTRACT-SELECTION"


@dataclass(frozen=True)
class Finding:
    name: str
    outcome: str
    code: str

    def value(self) -> list[str]:
        return [self.name, self.outcome, self.code]


def _load(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:  # pragma: no cover - host failure
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def _require(condition: bool, detail: str) -> None:
    if not condition:
        raise AssertionError(detail)


def _finding(name: str, outcome: str, code: str) -> Finding:
    return Finding(name, outcome, code)


def literal(value: bool) -> dict[str, Any]:
    return {"tag": "Literal", "value": value}


def variable(index: int) -> dict[str, Any]:
    return {"tag": "Variable", "index": index}


def conditional(
    condition: dict[str, Any],
    when_true: dict[str, Any],
    when_false: dict[str, Any],
) -> dict[str, Any]:
    return {
        "tag": "Conditional",
        "condition": condition,
        "when_true": when_true,
        "when_false": when_false,
    }


def let(bound: dict[str, Any], body: dict[str, Any]) -> dict[str, Any]:
    return {"tag": "Let", "bound": bound, "body": body}


def primitive(name: str, *arguments: dict[str, Any]) -> dict[str, Any]:
    return {"tag": "PrimitiveCall", "primitive": name, "arguments": list(arguments)}


def negate(item: dict[str, Any]) -> dict[str, Any]:
    return conditional(item, literal(False), literal(True))


def conjunction(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    return conditional(left, right, literal(False))


def disjunction(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    return conditional(left, literal(True), right)


def algorithm(
    term: dict[str, Any], inputs: int, kind: str = "b5b1.structural-bool"
) -> dict[str, Any]:
    return {"algorithm_kind": kind, "ordered_inputs": inputs, "term": term}


def input_ref(kind: str, reference: int) -> dict[str, Any]:
    return {"kind": kind, "ref": reference}


def guard(
    term: dict[str, Any],
    inputs: list[dict[str, Any]],
    kind: str = "b5b1.structural-bool",
) -> dict[str, Any]:
    return {
        "algorithm": algorithm(term, len(inputs), kind),
        "evaluation_contract": "foundation.portable-evaluation-v0",
        "inputs": inputs,
    }


def _source(
    kind: str, reduction: int | None = None, output: int | None = None
) -> dict[str, Any]:
    return {"kind": kind, "reduction": reduction, "output": output}


def _effect(kind: str, reference: int) -> dict[str, Any]:
    return {"kind": kind, "ref": reference}


def _occurrence(guard_value: object, kind: str, reference: int) -> dict[str, Any]:
    return {"guard": guard_value, "effect": _effect(kind, reference)}


def safe_program() -> dict[str, Any]:
    """Return the branch-complete selected candidate carrier."""

    accept_guard = guard(
        conjunction(variable(0), variable(1)),
        [input_ref("CheckOutput", 0), input_ref("PublicBoolean", 0)],
    )
    abort_guard = guard(variable(0), [input_ref("PublicBoolean", 1)])
    return {
        "claims": [
            {"usage": "Linear", "source": _source("Initial")},
            {"usage": "Reusable", "source": _source("ReductionOutput", 0, 0)},
            {"usage": "Reusable", "source": _source("ReductionOutput", 1, 0)},
        ],
        "reductions": [
            {"inputs": [0], "outputs": [1]},
            {"inputs": [0], "outputs": [2]},
        ],
        "checks": [{"label": "bounded-check-0"}],
        "terminals": [
            {
                "verdict": "Accept",
                "public_outputs": ["accept-output"],
                "required_true_checks": [0],
                "required_applied_reductions": [0],
                "terminal_claims": [1],
            },
            {
                "verdict": "Abort",
                "public_outputs": ["abort-code"],
                "required_true_checks": [],
                "required_applied_reductions": [1],
                "terminal_claims": [2],
            },
            {
                "verdict": "Reject",
                "public_outputs": ["reject-code"],
                "required_true_checks": [],
                "required_applied_reductions": [1],
                "terminal_claims": [2],
            },
        ],
        "occurrences": [
            _occurrence(None, "Check", 0),
            _occurrence(deepcopy(accept_guard), "Reduction", 0),
            _occurrence(deepcopy(accept_guard), "Terminal", 0),
            _occurrence(None, "Reduction", 1),
            _occurrence(abort_guard, "Terminal", 1),
            _occurrence(None, "Terminal", 2),
        ],
    }


def _candidate(model: ModuleType, program: object) -> tuple[str, str, object | None]:
    try:
        result = model.analyze(program)
        return result.outcome, result.code, result
    except model.ContractFailure as error:
        return error.outcome, error.code, None


def _expect(
    operation: Callable[[], tuple[str, str, object | None]],
    outcome: str,
    code: str,
    label: str,
) -> object | None:
    observed_outcome, observed_code, result = operation()
    _require(
        observed_outcome == outcome,
        f"{label}: expected {outcome}, got {observed_outcome}",
    )
    _require(observed_code == code, f"{label}: expected {code}, got {observed_code}")
    return result


def _term_corpus() -> list[tuple[str, dict[str, Any], int]]:
    terms: list[tuple[str, dict[str, Any], int]] = [
        ("false", literal(False), 3),
        ("true", literal(True), 3),
        ("x0", variable(0), 3),
        ("x1", variable(1), 3),
        ("x2", variable(2), 3),
    ]
    for index in range(3):
        terms.append((f"not-x{index}", negate(variable(index)), 3))
    for left in range(3):
        for right in range(3):
            terms.append(
                (f"and-{left}-{right}", conjunction(variable(left), variable(right)), 3)
            )
            terms.append(
                (f"or-{left}-{right}", disjunction(variable(left), variable(right)), 3)
            )
            terms.append(
                (
                    f"implication-{left}-{right}",
                    disjunction(negate(variable(left)), variable(right)),
                    3,
                )
            )
    terms.extend(
        [
            ("if-same", conditional(variable(0), variable(1), variable(1)), 3),
            (
                "factored-x0",
                disjunction(
                    conjunction(variable(0), variable(1)),
                    conjunction(variable(0), negate(variable(1))),
                ),
                3,
            ),
            ("let-identity", let(variable(2), variable(0)), 3),
            (
                "let-conjunction",
                let(
                    variable(0),
                    conditional(variable(0), variable(2), literal(False)),
                ),
                3,
            ),
            (
                "opaque-xor",
                primitive("foundation.bool-xor-v0", variable(0), variable(1)),
                3,
            ),
        ]
    )
    return terms


def _must_facts_sound(candidate: dict[str, Any], exact: dict[str, Any]) -> bool:
    for key in ("when_true", "when_false"):
        candidate_outcome = candidate[key]
        exact_outcome = exact[key]
        if not candidate_outcome["possible"] and exact_outcome["possible"]:
            return False
        if not set(map(tuple, candidate_outcome["literals"])) <= set(
            map(tuple, exact_outcome["literals"])
        ):
            return False
    return True


def _mutate(name: str) -> dict[str, Any]:
    program = deepcopy(safe_program())
    if name == "required-check-guard-omits-result":
        replacement = guard(variable(0), [input_ref("PublicBoolean", 0)])
        program["occurrences"][1]["guard"] = deepcopy(replacement)
        program["occurrences"][2]["guard"] = deepcopy(replacement)
    elif name == "required-check-or-guard":
        replacement = guard(
            disjunction(variable(0), variable(1)),
            [input_ref("CheckOutput", 0), input_ref("PublicBoolean", 0)],
        )
        program["occurrences"][1]["guard"] = deepcopy(replacement)
        program["occurrences"][2]["guard"] = deepcopy(replacement)
    elif name == "required-check-negated":
        replacement = guard(negate(variable(0)), [input_ref("CheckOutput", 0)])
        program["occurrences"][1]["guard"] = deepcopy(replacement)
        program["occurrences"][2]["guard"] = deepcopy(replacement)
    elif name == "required-check-reference":
        program["terminals"][0]["required_true_checks"] = [9]
    elif name == "required-check-always-terminal":
        program["occurrences"][1]["guard"] = None
        program["occurrences"][2]["guard"] = None
    elif name == "guard-check-reference":
        for position in (1, 2):
            program["occurrences"][position]["guard"]["inputs"][0]["ref"] = 9
    elif name == "guard-check-after-use":
        check = program["occurrences"].pop(0)
        program["occurrences"].insert(2, check)
    elif name == "guard-check-not-guaranteed":
        program["occurrences"][0]["guard"] = guard(
            variable(0), [input_ref("PublicBoolean", 1)]
        )
    elif name == "required-reduction-reference":
        program["terminals"][0]["required_applied_reductions"] = [9]
    elif name == "required-reduction-after-terminal":
        reduction = program["occurrences"].pop(1)
        program["occurrences"].insert(2, reduction)
    elif name == "required-reduction-not-guaranteed":
        program["claims"][0]["usage"] = "Reusable"
        mismatch = guard(variable(0), [input_ref("PublicBoolean", 1)])
        program["occurrences"][1]["guard"] = mismatch
        program["terminals"][0]["terminal_claims"] = [0, 1]
        program["terminals"][1]["terminal_claims"] = [0, 2]
        program["terminals"][2]["terminal_claims"] = [0, 2]
    elif name == "required-check-duplicate":
        program["terminals"][0]["required_true_checks"] = [0, 0]
    elif name == "required-check-unsorted":
        program["terminals"][0]["required_true_checks"] = [1, 0]
    elif name == "required-reduction-duplicate":
        program["terminals"][0]["required_applied_reductions"] = [0, 0]
    elif name == "required-reduction-unsorted":
        program["terminals"][0]["required_applied_reductions"] = [1, 0]
    elif name == "terminal-claim-duplicate":
        program["terminals"][0]["terminal_claims"] = [1, 1]
    elif name == "terminal-claim-unsorted":
        program["terminals"][0]["terminal_claims"] = [2, 1]
    elif name == "terminal-claim-omitted":
        program["terminals"][0]["terminal_claims"] = []
    elif name == "terminal-claim-reference":
        program["terminals"][0]["terminal_claims"] = [9]
    elif name == "authored-disposition-reintroduced":
        terminal = program["terminals"][0]
        terminal["claim_dispositions"] = [[1, "Consume"]]
    elif name == "final-fallback-guarded":
        program["occurrences"][-1]["guard"] = guard(
            variable(0), [input_ref("PublicBoolean", 1)]
        )
    elif name == "linear-consumer-overlap":
        alternative = program["occurrences"].pop(3)
        program["occurrences"].insert(2, alternative)
    elif name == "guard-abi":
        program["occurrences"][2]["guard"]["algorithm"]["ordered_inputs"] = 1
    elif name == "malformed-term":
        program["occurrences"][2]["guard"]["algorithm"]["term"]["tag"] = (
            "BooleanTheorem"
        )
    elif name == "unsupported-effect":
        program["occurrences"][0]["effect"]["kind"] = "FailureTransition"
    else:  # pragma: no cover - mutation table is closed
        raise KeyError(name)
    return program


MUTATIONS: tuple[tuple[str, str, str], ...] = (
    ("required-check-guard-omits-result", "Refused", "F0V2B2C1B5B1-R-CHECK-ENTAILMENT"),
    ("required-check-or-guard", "Refused", "F0V2B2C1B5B1-R-CHECK-ENTAILMENT"),
    ("required-check-negated", "Refused", "F0V2B2C1B5B1-R-CHECK-ENTAILMENT"),
    ("required-check-reference", "Refused", "F0V2B2C1B5B1-R-CHECK-REFERENCE"),
    ("required-check-always-terminal", "Refused", "F0V2B2C1B5B1-R-CHECK-ENTAILMENT"),
    ("guard-check-reference", "Refused", "F0V2B2C1B5B1-R-GUARD-INPUT"),
    ("guard-check-after-use", "Refused", "F0V2B2C1B5B1-R-GUARD-INPUT"),
    ("guard-check-not-guaranteed", "Refused", "F0V2B2C1B5B1-R-GUARD-INPUT"),
    ("required-reduction-reference", "Refused", "F0V2B2C1B5B1-R-REQUIRED-REDUCTION"),
    (
        "required-reduction-after-terminal",
        "Refused",
        "F0V2B2C1B5B1-R-REQUIRED-REDUCTION",
    ),
    (
        "required-reduction-not-guaranteed",
        "Refused",
        "F0V2B2C1B5B1-R-REQUIRED-REDUCTION",
    ),
    ("required-check-duplicate", "Refused", "F0V2B2C1B5B1-R-CANONICAL-SET"),
    ("required-check-unsorted", "Refused", "F0V2B2C1B5B1-R-CANONICAL-SET"),
    ("required-reduction-duplicate", "Refused", "F0V2B2C1B5B1-R-CANONICAL-SET"),
    ("required-reduction-unsorted", "Refused", "F0V2B2C1B5B1-R-CANONICAL-SET"),
    ("terminal-claim-duplicate", "Refused", "F0V2B2C1B5B1-R-CANONICAL-SET"),
    ("terminal-claim-unsorted", "Refused", "F0V2B2C1B5B1-R-CANONICAL-SET"),
    ("terminal-claim-omitted", "Refused", "F0V2B2C1B5B1-R-TERMINAL-CLOSURE"),
    ("terminal-claim-reference", "Refused", "F0V2B2C1B5B1-R-TERMINAL-CLAIM"),
    ("authored-disposition-reintroduced", "Malformed", "F0V2B2C1B5B1-M-SHAPE"),
    ("final-fallback-guarded", "Refused", "F0V2B2C1B5B1-R-FINAL-FALLBACK"),
    ("linear-consumer-overlap", "Refused", "F0V2B2C1B5B1-R-LINEAR-PATH-OVERLAP"),
    ("guard-abi", "Refused", "F0V2B2C1B5B1-R-GUARD-ABI"),
    ("malformed-term", "Malformed", "F0V2B2C1B5B1-M-TERM"),
    ("unsupported-effect", "Unsupported", "F0V2B2C1B5B1-U-EFFECT"),
)


def evaluate() -> tuple[list[Finding], dict[str, Any]]:
    model = _load("_zkc_f0v2b2c1b5b1_model", MODEL)
    independent = _load("_zkc_f0v2b2c1b5b1_independent", INDEPENDENT)
    findings: list[Finding] = []

    predecessor = json.loads(PREDECESSOR_EXPECTED.read_text(encoding="utf-8"))
    _require(
        predecessor["aggregate"] == "F0V2B2C1B5A-C-TERMINAL-CONTRACT-INCOMPLETE",
        "B5A predecessor aggregate drifted",
    )
    findings.append(
        _finding("predecessor-pin", "Affirmative", "F0V2B2C1B5B1-A-PREDECESSOR-PIN")
    )

    foundation_source = FOUNDATION_SOURCE.read_text(encoding="utf-8")
    target_source = TARGET_SOURCE.read_text(encoding="utf-8")
    terminal_start = target_source.index("TerminalDecl = {")
    terminal_end = target_source.index("At an active terminal", terminal_start)
    terminal_source = target_source[terminal_start:terminal_end]
    _require(
        "Foundation does not define a universal ZK value algebra, protocol evaluator,"
        in foundation_source
        and "judgment engine, result type, or resource policy" in foundation_source,
        "Foundation owner boundary drifted",
    )
    _require(
        "ClaimDisposition = Consume | Discharge" in target_source
        and "required_applied_reductions" not in terminal_source,
        "the B5A Terminal source gap no longer matches this successor",
    )
    findings.append(
        _finding("owner-source-boundary", "Affirmative", "F0V2B2C1B5B1-A-OWNER-SOURCE")
    )
    findings.append(
        _finding(
            "target-gap-source-pin", "Affirmative", "F0V2B2C1B5B1-A-TARGET-GAP-PIN"
        )
    )

    candidate_source = MODEL.read_text(encoding="utf-8")
    oracle_source = INDEPENDENT.read_text(encoding="utf-8")
    _require(
        "itertools" not in candidate_source and "product(" not in candidate_source,
        "candidate enumerates assignments",
    )
    _require(
        "import model" not in oracle_source and "from model" not in oracle_source,
        "oracle imports candidate",
    )
    findings.append(
        _finding(
            "candidate-oracle-separation",
            "Affirmative",
            "F0V2B2C1B5B1-A-ORACLE-SEPARATION",
        )
    )

    corpus = _term_corpus()
    exact_matches = 0
    term_assignments = 0
    for name, term, input_count in corpus:
        candidate, _nodes = model.analyze_boolean_algorithm(
            algorithm(term, input_count, name)
        )
        exact = independent.exact_boolean_facts(algorithm(term, input_count, name))
        candidate_value = candidate.value()
        term_assignments += exact.pop("assignments")
        _require(
            _must_facts_sound(candidate_value, exact),
            f"unsound must-fact result for {name}",
        )
        if candidate_value == exact:
            exact_matches += 1
    findings.append(
        _finding(
            "must-fact-soundness", "Affirmative", "F0V2B2C1B5B1-A-MUST-FACT-SOUNDNESS"
        )
    )
    findings.append(
        _finding(
            "structural-boolean-precision",
            "Affirmative",
            "F0V2B2C1B5B1-A-STRUCTURAL-PRECISION",
        )
    )

    program = safe_program()
    result = _expect(
        lambda: _candidate(model, program),
        "Affirmative",
        "F0V2B2C1B5B1-A-TERMINAL-OWNER-CONTRACTS",
        "selected Terminal carrier",
    )
    assert result is not None
    oracle = independent.evaluate_all(program)
    _require(oracle["valid"], f"oracle rejected selected carrier: {oracle}")
    _require(
        oracle["assignments"] == 8,
        "selected carrier did not cover three Boolean sources",
    )
    _require(
        oracle["terminal_counts"] == {"Abort": 3, "Accept": 2, "Reject": 3},
        "first-active outcome partition differs",
    )
    findings.append(
        _finding(
            "branch-complete-selected-carrier",
            "Affirmative",
            "F0V2B2C1B5B1-A-BRANCH-CARRIER",
        )
    )
    _require(result.check_entailments == ((0, 0, 0),), "required Check witness differs")
    findings.append(
        _finding(
            "required-check-entailment",
            "Affirmative",
            "F0V2B2C1B5B1-A-CHECK-ENTAILMENT",
        )
    )
    _require(
        result.reduction_requirements == ((0, 0), (1, 1), (2, 1)),
        "required Reduction closure differs",
    )
    findings.append(
        _finding(
            "required-reduction-ownership",
            "Affirmative",
            "F0V2B2C1B5B1-A-REQUIRED-REDUCTION",
        )
    )
    _require(
        result.terminal_dispositions
        == (
            ((1, "Consume"),),
            ((2, "Discharge"),),
            ((2, "Discharge"),),
        ),
        "verdict-derived Claim dispositions differ",
    )
    findings.append(
        _finding(
            "verdict-derived-claim-disposition",
            "Affirmative",
            "F0V2B2C1B5B1-A-DERIVED-DISPOSITION",
        )
    )
    findings.append(
        _finding(
            "first-active-semantics-preserved",
            "Affirmative",
            "F0V2B2C1B5B1-A-FIRST-ACTIVE",
        )
    )
    findings.append(
        _finding(
            "check-false-authored-fallback",
            "Affirmative",
            "F0V2B2C1B5B1-A-CHECK-FALSE-FALLBACK",
        )
    )

    let_program = deepcopy(program)
    let_guard = guard(
        let(conjunction(variable(0), variable(1)), variable(0)),
        [input_ref("CheckOutput", 0), input_ref("PublicBoolean", 0)],
    )
    let_program["occurrences"][1]["guard"] = deepcopy(let_guard)
    let_program["occurrences"][2]["guard"] = deepcopy(let_guard)
    _expect(
        lambda: _candidate(model, let_program),
        "Affirmative",
        "F0V2B2C1B5B1-A-TERMINAL-OWNER-CONTRACTS",
        "Let-bound required Check",
    )
    _require(
        independent.evaluate_all(let_program)["valid"],
        "oracle rejected Let-bound implication",
    )
    findings.append(
        _finding(
            "let-bound-check-entailment", "Affirmative", "F0V2B2C1B5B1-A-LET-ENTAILMENT"
        )
    )

    factored_program = deepcopy(program)
    factored_guard = guard(
        disjunction(
            conjunction(variable(0), variable(1)),
            conjunction(variable(0), negate(variable(1))),
        ),
        [input_ref("CheckOutput", 0), input_ref("PublicBoolean", 0)],
    )
    factored_program["occurrences"][1]["guard"] = deepcopy(factored_guard)
    factored_program["occurrences"][2]["guard"] = deepcopy(factored_guard)
    _expect(
        lambda: _candidate(model, factored_program),
        "Affirmative",
        "F0V2B2C1B5B1-A-TERMINAL-OWNER-CONTRACTS",
        "branch-joined required Check",
    )
    _require(
        independent.evaluate_all(factored_program)["valid"],
        "oracle rejected branch-joined implication",
    )
    findings.append(
        _finding(
            "branch-join-check-entailment",
            "Affirmative",
            "F0V2B2C1B5B1-A-BRANCH-JOIN-ENTAILMENT",
        )
    )

    weakened = deepcopy(program)
    weakened["terminals"][0]["required_applied_reductions"] = []
    _expect(
        lambda: _candidate(model, weakened),
        "Affirmative",
        "F0V2B2C1B5B1-A-TERMINAL-OWNER-CONTRACTS",
        "authored required-Reduction policy change",
    )
    _require(
        independent.evaluate_all(weakened)["valid"],
        "oracle rejected weaker authored policy",
    )
    owner_hashes = {
        hashlib.sha256(
            json.dumps(item, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
        for item in (program["terminals"][0], weakened["terminals"][0])
    }
    _require(
        len(owner_hashes) == 2, "required Reduction policy did not change owner bytes"
    )
    findings.append(
        _finding(
            "required-reduction-owner-sensitivity",
            "Affirmative",
            "F0V2B2C1B5B1-A-REDUCTION-OWNER-SENSITIVITY",
        )
    )

    old_consume = {
        "verdict": "Accept",
        "required_true_checks": [0],
        "claim_dispositions": [[1, "Consume"]],
    }
    old_discharge = deepcopy(old_consume)
    old_discharge["claim_dispositions"] = [[1, "Discharge"]]
    old_hashes = {
        hashlib.sha256(
            json.dumps(item, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
        for item in (old_consume, old_discharge)
    }
    _require(
        len(old_hashes) == 2, "unconstrained disposition tags did not split identity"
    )
    findings.append(
        _finding(
            "unconstrained-disposition-identity-split",
            "Refused",
            "F0V2B2C1B5B1-R-DISPOSITION-ALIAS",
        )
    )

    hidden = independent.hidden_gating_counterexample()
    _require(
        hidden["violation"] == "linear-claim-consumed-twice",
        "hidden-gating counterexample drifted",
    )
    findings.append(
        _finding(
            "implicit-terminal-gating", "Refused", "F0V2B2C1B5B1-R-IMPLICIT-GATING"
        )
    )
    findings.append(
        _finding(
            "check-false-failure-transition",
            "Refused",
            "F0V2B2C1B5B1-R-FAILURE-TRANSITION",
        )
    )
    findings.append(
        _finding(
            "remove-required-checks",
            "Refused",
            "F0V2B2C1B5B1-R-WEAKENED-CHECK-CONTRACT",
        )
    )
    findings.append(
        _finding(
            "external-theorem-as-admission-authority",
            "Refused",
            "F0V2B2C1B5B1-R-EXTERNAL-AUTHORITY",
        )
    )

    mutation_agreement = 0
    for name, outcome, code in MUTATIONS:
        mutated = _mutate(name)
        _expect(lambda value=mutated: _candidate(model, value), outcome, code, name)
        oracle_result = independent.evaluate_all(mutated)
        _require(not oracle_result["valid"], f"oracle accepted mutation {name}")
        findings.append(_finding(name, outcome, code))
        mutation_agreement += 1
    findings.append(
        _finding(
            "mutation-oracle-agreement",
            "Affirmative",
            "F0V2B2C1B5B1-A-MUTATION-AGREEMENT",
        )
    )

    opaque = deepcopy(program)
    opaque_guard = guard(
        primitive("foundation.bool-and-v0", variable(0), variable(1)),
        [input_ref("CheckOutput", 0), input_ref("PublicBoolean", 0)],
    )
    opaque["occurrences"][1]["guard"] = deepcopy(opaque_guard)
    opaque["occurrences"][2]["guard"] = deepcopy(opaque_guard)
    _expect(
        lambda: _candidate(model, opaque),
        "Refused",
        "F0V2B2C1B5B1-R-CHECK-ENTAILMENT",
        "opaque primitive implication",
    )
    _require(
        independent.evaluate_all(opaque)["valid"],
        "oracle rejected extension-only opaque conjunction",
    )
    findings.append(
        _finding(
            "primitive-specific-implication-is-not-imported",
            "Refused",
            "F0V2B2C1B5B1-R-OPAQUE-PRIMITIVE",
        )
    )

    _require(
        result.operations < 256,
        "selected candidate crossed the compact operation budget",
    )
    findings.append(
        _finding("compact-static-work", "Affirmative", "F0V2B2C1B5B1-A-COMPACT-WORK")
    )
    findings.append(
        _finding("pir-owned-terminal-use", "Affirmative", "F0V2B2C1B5B1-A-PIR-OWNER")
    )
    findings.append(
        _finding(
            "foundation-denotation-unchanged",
            "Affirmative",
            "F0V2B2C1B5B1-A-FOUNDATION-BOUNDARY",
        )
    )
    findings.append(
        _finding(
            "exact-six-view-projection",
            "CannotAnswer",
            "F0V2B2C1B5B1-C-EXACT-PROJECTION",
        )
    )
    findings.append(
        _finding(
            "primitive-implication-satellite",
            "CannotAnswer",
            "F0V2B2C1B5B1-C-IMPLICATION-SATELLITE",
        )
    )
    findings.append(
        _finding(
            "target-publication", "CannotAnswer", "F0V2B2C1B5B1-C-TARGET-PUBLICATION"
        )
    )
    findings.append(
        _finding(
            "live-implementation-correspondence",
            "CannotAnswer",
            "F0V2B2C1B5B1-C-LIVE-CORRESPONDENCE",
        )
    )
    findings.append(
        _finding("formal-proof", "CannotAnswer", "F0V2B2C1B5B1-C-FORMAL-PROOF")
    )
    findings.append(
        _finding("cryptographic-security", "CannotAnswer", "F0V2B2C1B5B1-C-SECURITY")
    )
    findings.append(_finding("q1-correspondence", "CannotAnswer", "F0V2B2C1B5B1-C-Q1"))
    findings.append(_finding("terminal-contract-selection", "Affirmative", AGGREGATE))

    payload = [finding.value() for finding in findings]
    checksum = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()
    metrics = {
        "findings": len(findings),
        "findings_sha256": checksum,
        "term_corpus": len(corpus),
        "term_assignments": term_assignments,
        "term_exact_matches": exact_matches,
        "candidate_operations": result.operations,
        "runtime_assignments": oracle["assignments"],
        "terminal_counts": oracle["terminal_counts"],
        "mutations": mutation_agreement,
        "hidden_gating_counterexample": hidden,
    }
    return findings, metrics


def _load_expected() -> dict[str, Any]:
    value = json.loads(EXPECTED.read_text(encoding="utf-8"))
    _require(type(value) is dict, "expected findings root differs")
    return value


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    findings, metrics = evaluate()
    observed = {
        "aggregate": AGGREGATE,
        "findings_sha256": metrics["findings_sha256"],
        "finding_codes": [finding.value() for finding in findings],
    }
    if args.check:
        expected = _load_expected()
        if observed != expected:
            print(
                json.dumps(
                    {"expected": expected, "observed": observed},
                    indent=2,
                    sort_keys=True,
                )
            )
            return 1
    counts: dict[str, int] = {}
    for finding in findings:
        counts[finding.outcome] = counts.get(finding.outcome, 0) + 1
    output: dict[str, Any] = {
        "aggregate": AGGREGATE,
        "outcomes": dict(sorted(counts.items())),
        "metrics": metrics,
    }
    if args.json:
        output["finding_codes"] = observed["finding_codes"]
    print(json.dumps(output, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
