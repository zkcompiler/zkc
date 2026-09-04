#!/usr/bin/env python3
"""Produce a live, manually curated invariant-boundary coverage snapshot.

For each instrument this script collects affirmative outcomes and every
non-affirmative ``(outcome, boundary, code)`` triple its probe function reaches.
It then compares the pooled non-affirmative boundaries with an authored mapping
from ledger rows to expected boundaries.  The result is useful for finding
unexercised pressure and prioritizing review.

It is not an R2 closure checker.  In particular, it does not establish that a
driver is a well-formed negative mutation, associate a particular positive
inhabitant with each invariant, prove that the authored boundary mapping is
correct, or distinguish semantic refusals from missing dependencies, resource
limits, checker failures, and intentionally unexercised outcomes.  The FRI and
P01 inputs are read from stored case oracles; the four cross-cutting probes are
executed live.  Results are therefore mixed-strength diagnostics.

The labels are ``boundary-covered``, ``boundary-partial``, and
``boundary-uncovered``.  Even ``boundary-covered`` means only that every
manually listed boundary was observed and no already-authored gap remains.  A
human closure decision still belongs to the case or invariant owner.

Run from the repository root:

    python3 evaluation/coverage.py
    python3 evaluation/coverage.py --json
"""

from __future__ import annotations

import argparse
import importlib
import json
from pathlib import Path
import sys
from typing import Any, Callable, Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
EVALUATION = REPO_ROOT / "evaluation"


# --- the ledger ---------------------------------------------------------------
#
# Each entry names boundaries whose observation is relevant to the invariant.
# The mapping is authored, not derived. A renamed boundary reports as uncovered
# rather than silently matching a stale name.

LEDGER: dict[str, dict[str, Any]] = {
    "F-01": {
        "title": "regime closure",
        "boundaries": {"algebra-profile"},
        "pressure": (
            "Two independent implementations must derive the same identity/support "
            "result and reject an unsupported or ambiguously interpreted regime."
        ),
        "gap": (
            "one implementation derives the identity and support result, not two: "
            "the runner's `verify_report` re-derives by calling `build_report` "
            "and compares against a stored expectation file, which is a frozen "
            "oracle rather than a second implementation. The subject is a finite- "
            "field algebra profile rather than a semantic regime; the profile "
            "does carry an exact change law (a changed field moves its identity), "
            "but the witnesses' own regime object is judged only by a boolean "
            "support predicate whose two refusal paths are unreached. Of the two "
            "rejection kinds the pressure names, only unsupported is exercised — "
            "and its refusal (P01-ALG-007, a non-pinned codec) lives in the unit "
            "tests, so the negatives measured at this boundary are the composite- "
            "modulus and challenge-size well-formedness refusals. No witness "
            "rejects an ambiguously interpreted regime, and no first-class "
            "acquired lane is exercised."
        ),
    },
    "F-02": {
        "title": "canonical boundary-value closure",
        "boundaries": {"framing"},
        "pressure": (
            "A noncanonical encoding, wrong domain, or ambiguous equality must fail "
            "before the affected boundary."
        ),
        "gap": (
            "the framing boundary pins each occurrence's codec to the one its "
            "declared sort and cardinality require, which delivers the wrong- "
            "domain half; no noncanonical byte string is ever decoded and "
            "refused, and the only surface that would "
            "(r2-p01-schnorr/p01model/interface.py, codes P01-PROOF-004/005/006) "
            "has no callers; the ambiguous-equality half is exercised only at "
            "relations:statement-bridge:relation-qualification, which this entry "
            "does not claim and the frozen results do not carry"
        ),
    },
    "F-03": {
        "title": "algorithm closure",
        "boundaries": {"algorithm-closure", "algorithm-support"},
        "pressure": (
            "Round-trip a real codec/sampler/bridge; reject wrong arity, domain, "
            "state, or result."
        ),
        "gap": (
            "both claimed boundaries are name checks on the construction record — "
            "that a sampler algorithm is cited, and that the cited name is one "
            "the witness supports; neither encodes a value or steps a sampler, so "
            "no round-trip is exercised and none of the wrong arity, domain, "
            "state, or result rejections lands here. A real deterministic sampler "
            "does run, with a named exhaustion failure, but at an unclaimed "
            "boundary whose code never fires, and the codec has no decode to "
            "round-trip against. The quoted pressure also drops the row's shared- "
            "envelope and domain-ownership clause."
        ),
    },
    "F-05": {
        "title": "bounded identity work",
        "boundaries": {"closed-core", "guard:representation", "guard:work"},
        "pressure": (
            "Measure stored bytes, peak derived structure, memory, and work on real "
            "and adversarial guards. No divergent semantic verdict."
        ),
        "gap": (
            "work is measured and separate from size (n^2 against 2^n "
            "expansions), and the 'no divergent semantic verdict' clause is "
            "delivered — both orders are proved by exhaustion to denote the same "
            "function, so the refusal is about representation, not meaning. Two "
            "further boundaries deliver the admission-derived-work clause and "
            "should be claimed here: `execution-resource` (R2-REQ-006) and "
            "`execution-qualification:resource` (R2-QUAL-009), which bound "
            "aggregate worst-case work before execution or replay begins. Still "
            "missing: stored bytes, memory, and peak derived structure — the "
            "diagram cost reports the final reachable node count (18 at n=8 "
            "interleaved), not the peak unique table (80), and nothing bounds the "
            "peak; and the identity-preimage byte/node/depth bounds declared in "
            "each witness's terms.py have no test that drives them. The guards "
            "remain the textbook separating family rather than a corpus of real "
            "ones, and of the many codes sharing the `closed-core` boundary only "
            "R2-LOGUP-001, the declared claim bound, bears on this row."
        ),
    },
    "F-06": {
        "title": "identity-field justification",
        # This entry previously claimed closure on `logup:derived-anchors`, which
        # tests that an authored anchor may not diverge from derived material.
        # That is a derived-stays-derived property and now sits under X-02.  No
        # witness permutes an identity-bearing collection, which is what this
        # invariant's pressure actually asks for.
        "boundaries": set(),
        "pressure": (
            "Remove or justify one semantically inert permutation/field; demonstrate "
            "the consumer or attack boundary for every retained one."
        ),
    },
    "P-01": {
        "title": "complete instance binding",
        "boundaries": {"transcript-prefix:fold1", "logup:transcript-prefix"},
        "pressure": (
            "Omit, substitute, reorder where order is semantic, delay, or use the "
            "wrong codec for one Statement occurrence; duplicate only where the "
            "selected profile forbids it."
        ),
        "gap": (
            "omission, delay, and duplication before the fold challenge are "
            "driven at the claimed boundaries, by two independent routes; "
            "substitution is not — the FRI witness publishes it as NotExercised "
            "at `scope:substituted-statement-influence` and its wrong-statement- "
            "value mutation refuses to build — a reorder inside the prefix is not "
            "driven either, since R2-FS-006 is defined and never reached, and the "
            "wrong-codec mutation fires at `framing`, a boundary this entry does "
            "not claim. The Schnorr witness asserts substitution, reorder, wrong "
            "codec, and duplication on its challenge prefix, but does not publish "
            "those cases to its frozen corpus, so nothing here measures them."
        ),
    },
    "P-03": {
        "title": "exact prefix closure",
        "boundaries": {"transcript-prefix:pow", "logup:transcript-prefix"},
        "pressure": (
            "Reproduce the semantic boundaries behind E211, E212, and E214 without "
            "importing their current representation by fiat."
        ),
    },
    "P-05": {
        "title": "public-coin eligibility",
        "boundaries": {"public-coin-eligibility"},
        "pressure": (
            "Introduce a verifier-private invocation value, private sample, hidden "
            "state dependency, or unlinked stochastic verifier move and require "
            "admission to reject it."
        ),
        "gap": (
            "a challenge declared VerifierPrivate is introduced and rejected; the "
            "pressure's other three introductions are not — CoinSource has the "
            "single member UniformFinite so no private sample is expressible, no "
            "mutation gives a verifier action a predicate or residual, and the "
            "influence-set laws that would catch an unlinked verifier coin "
            "(R2-FS-009, R2-FS-010) have no driver in any test or published case "
            "and sit at transcript-prefix boundaries claimed by P-01 and P-03"
        ),
    },
    "P-07": {
        "title": "unambiguous challenge derivation",
        "boundaries": {"squeeze-sample-admission"},
        "pressure": (
            "Ambiguous/reused occurrence namespace, wrong state transition, and "
            "grinding/rejection failure mutations, including the semantic boundary "
            "behind E216."
        ),
        "gap": (
            "namespace reuse is genuinely mutated and refused at the E216 "
            "boundary, but the pressure's other demands are not delivered here: "
            "no mutation drives a wrong state transition against the "
            "squeeze/sample relation — the relation's own named failure "
            "(R2-EXEC-012, sampler retry bound exhausted) has no driver, and the "
            "nearest negative, R2-QUAL-003 'record differs from exact "
            "reexecution', is whole-record replay equality on another boundary "
            "and is absent from the frozen case set; the grinding/rejection- "
            "failure mutation that does exist is refused at `analysis- "
            "applicability:grinding-failure`, which this entry does not claim; "
            "the claimed boundary's second code R2-NS-002, for a malformed or "
            "ambiguous namespace, is never driven; and uniqueness is checked "
            "within one Core over authored literal namespaces, so composition- "
            "safety and the ABI's freedom from a globally unique authored string "
            "hold by construction rather than under pressure"
        ),
    },
    "P-08": {
        "title": "causal prover generation",
        "boundaries": {"strategy-causality:message:g1"},
        "pressure": (
            "A commitment depending on a future challenge is not strategy-generated "
            "even if a whole serialized trace replays."
        ),
        "gap": (
            "the future-read negative does hold the wire byte-identical, but "
            "nothing asserts that half: it is refused before any transcript check "
            "runs and no replaying trace is ever exhibited for it, and because "
            "the mutant also differs from the canonical strategy realization the "
            "exact-match rule would refuse it even with the causality predicate "
            "removed, so causality is never the sole discriminator; the rule "
            "reads declared reads, not realized dependence, and the executable "
            "form of that check in the Schnorr witness has no caller"
        ),
    },
    "P-10": {
        "title": "typed claim routing",
        "boundaries": {"typed-routing", "logup:claims", "logup:claim-linearity"},
        "pressure": (
            "Wrong claim contract, parameter order/domain, reduction output, or "
            "check input rejects."
        ),
        "gap": (
            "the claim graph's referential integrity and its single-consumer rule "
            "are measured; the typing is not. `Claim.contract`, "
            "`Reduction.contract`, and `Reduction.deps` are inert data no rule "
            "reads, so a core whose inclusion and identity contracts are swapped, "
            "whose reduction names a foreign contract, whose side input names a "
            "challenge nothing samples, or whose challenge declares a different "
            "domain and space all still admit affirmative. The reduction-output "
            "rule R2-LOGUP-011 on this boundary has no caller; no witness has a check "
            "operand to mutate; and `typed-routing`/R2-ROUTE-001 is an equality "
            "against a hardcoded route order that the closed-core schedule law "
            "already enforces, carrying no type content."
        ),
    },
    "P-11": {
        "title": "view adequacy",
        "boundaries": set(),
        "pressure": (
            "Remove one required fact, add a forbidden authoritative mirror, or "
            "request an unknown question."
        ),
    },
    "R-03": {
        "title": "explicit grounding equations",
        "boundaries": {"commitment:opening", "commitment:domain-separation"},
        "pressure": (
            "One affirmative real object plus wrong commitment, material, selector, "
            "position, and equation mutations."
        ),
        "gap": (
            "the wrong-commitment, material, selector, and equation mutations are "
            "all asserted, but no position mutation exists: the single "
            "evaluation-order rule -- an opening must precede the check that "
            "consumes it -- never fires under the witness's own suite, and no "
            "mutation can make it fire. This probe also never drives the equation "
            "mutation itself; a forged answer that fails to reconstruct the "
            "commitment is reached only by the unit tests, so the measured "
            "negative set is narrower than the property claimed"
        ),
    },
    "R-04": {
        "title": "lossless bridge laws are explicit",
        "boundaries": {"bridge:lane"},
        "pressure": (
            "Round-trip a full equivalence in both directions, round-trip an "
            "embedding on its image, and reject a lossy mapping presented as either."
        ),
        "gap": (
            "the lane boundary checks declaration hygiene — which obligations "
            "each lane must and must not carry — but no bridge carries an "
            "executable map, so neither round trip is driven at it; the one "
            "bijection round trip (tests/test_bridges.py:139) runs on free "
            "lambdas, reaches no boundary, and checks only backward(forward(x)) "
            "== x despite its docstring claiming both inverse laws, so an "
            "injective non-surjective map passes it, and no embedding is ever "
            "inverted on its image because the image predicate is an opaque "
            "string that is never evaluated"
        ),
    },
    "R-05": {
        "title": "every retained lossy projection is separate and priced",
        "boundaries": {"analysis:projection-loss"},
        "pressure": (
            "Model the current 256-to-216-bit anchor case with a grounded reduction "
            "or deliberately eliminate it, for example by retaining a full digest."
        ),
        "gap": (
            "the shipped anchor case is modeled and its reduction shown "
            "ungrounded — a projection collision is constructible in constant "
            "time, so pricing returns CannotAnswer naming the premise nothing "
            "establishes — but neither branch of the pressure lands: no grounded "
            "reduction is built and no full-digest elimination is modeled, and "
            "the one affirmative pricing of the case is reached only by passing "
            "in an unvalidated premise string. The loss is a declared 40-bit "
            "constant checked for presence; no advantage or occurrence-scaled "
            "addend is ever computed. Occurrence exactness has no reachable "
            "negative: pricing ignores the bridge's declared count, and the "
            "fixture-side wrong-count refusal is unreachable behind "
            "requalification"
        ),
    },
    "R-06": {
        "title": "relation-facing witness surface",
        # These boundaries refuse an operand naming a foreign parent, which is
        # referential binding between admission layers. This invariant is about a
        # Witness/Context/ProtocolValue surface distinction, and no witness models
        # that vocabulary at all.
        "boundaries": set(),
        "pressure": (
            "A protocol-private nonwitness input must not force a Relations witness "
            "port; an exported derived witness must be expressible."
        ),
        "gap": (
            "neither claimed boundary asserts a witness surface: "
            "relations:instance-admission:relation and relations:witness- "
            "admission:instance refuse an operand that names a foreign parent, "
            "which is referential binding between admission layers, not a "
            "Witness/Context/ProtocolValue distinction. Of the pressure's two "
            "halves, the nonwitness half is only positively exhibited — "
            "relation_honest_prover_candidate projects the single RelationWitness "
            "local input and leaves the PrivateRandomness nonce off the relation "
            "surface, checked once as an affirmative on relations:honest-prover- "
            "correspondence — with no case driving a protocol-private nonwitness "
            "input into a witness port and no Result-bearing guard behind it, and "
            "the exported-derived-witness half exists only in "
            "check_qualified_private_witness_grounding, which has no callers, no "
            "test, and publishes no case"
        ),
    },
    "R-07": {
        "title": "result correspondence has a direction",
        "boundaries": {
            "relations:satisfaction",
            "relations:honest-prover-correspondence:exact-law",
        },
        "pressure": (
            "A structural binding cannot be consumed as behavioral equivalence."
        ),
        "gap": (
            "structural correspondence and satisfaction are exercised as separate "
            "judgments that can disagree; Protocol acceptance, soundness direction, "
            "completeness direction, and full equivalence are not"
        ),
    },
    "R-08": {
        "title": "binding questions retain meaningful negatives",
        "boundaries": {"logup:material-identity", "apply.parameters.lookups"},
        "pressure": (
            "For every affirmative result, exhibit a well-formed admitted operand "
            "that can produce its declared Negative, or derive the fact internally "
            "instead."
        ),
        "gap": (
            "both claimed boundaries are refusals inside `admit_core`, so neither "
            "operand was ever admitted; the layered case the pressure names — an "
            "admitted operand failing a later question — is exercised only in the "
            "uncited Schnorr chain (`relations:satisfaction`, "
            "`relations:instance-admission:relation`, `relations:witness- "
            "admission:instance`, `relations:honest-prover-correspondence:exact- "
            "law`), which this entry should claim; and logup's second "
            "affirmative, `correspondence`, publishes two negatives no test or "
            "probe drives, one of which restates admission's role check under a "
            "weaker name"
        ),
    },
    "X-02": {
        "title": "derived evidence remains derived",
        "boundaries": {"logup:derived-anchors"},
        "pressure": (
            "Two independent routes reproduce or validate the same derived object; "
            "mutation is detected without turning the cache or certificate into the "
            "semantic owner."
        ),
        "gap": (
            "the claimed boundary is on-property but single-sourced: the column "
            "anchor and the reduction anchor are both reads of the one literal "
            "ANCHORS map (logup_model/logup.py:302-310 into 387 and 407), so nothing "
            "is recomputed and the law cannot separate derived evidence from two "
            "identical authored copies. A second route does exist and is not "
            "claimed here — load_fixture hash-pins the shipped .mlir fixtures and "
            "correspondence checks the independently declared scenario against "
            "facts read out of them (logup.py:331-358, 606-620) — but it "
            "validates roles and challenge space rather than anchors, probe_logup "
            "never drives it, and its negatives R2-LOGUP-020 and R2-LOGUP-021 have no "
            "caller anywhere, so logup:correspondence can never enter the "
            "measured negative set. The cache-is-not-the-owner clause is untested "
            "at any claimed boundary."
        ),
    },
    # The two entries below are local observations named by the witnesses, not
    # numbered ledger rows.  They carry no pressure clause to quote.
    "X-TERM": {
        "title": "terminal closure (local: no live claim survives)",
        "boundaries": {"logup:terminal-closure"},
        "pressure": None,
    },
    "X-SEAT": {
        "title": "origin and seat agree (local)",
        "boundaries": {"logup:origin-seat", "logup:round-structure"},
        "pressure": None,
    },
}


# --- witness probes -----------------------------------------------------------


def _load(package_root: Path, dotted: str) -> Any:
    """Import a witness module as part of its own package.

    Loading the file directly would break its relative imports, so the witness
    root goes on the path and the module is imported by name.
    """

    if str(package_root) not in sys.path:
        sys.path.insert(0, str(package_root))
    for stale in [name for name in sys.modules if name.split(".")[0] == dotted.split(".")[0]]:
        del sys.modules[stale]
    return importlib.import_module(dotted)


def _record(sink: dict[str, set], result: Any) -> None:
    outcome = getattr(result, "outcome", None)
    if outcome is None:
        return
    triple = (outcome.value, getattr(result, "boundary", ""), getattr(result, "code", ""))
    if outcome.value == "Affirmative":
        sink["positives"].add(triple)
    else:
        sink["negatives"].add(triple)
    sink["codes"].add(triple[2])


def probe_commitment() -> dict[str, set]:
    root = EVALUATION / "r2-probe-commitment"
    sys.path.insert(0, str(root))
    core = _load(root, "commitment_model.core")
    constructions = importlib.import_module("commitment_model.commitment").CONSTRUCTIONS
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    construction = constructions["r2.commit.binary-merkle.v1"]
    small = type(construction)(
        name=construction.name, element_sort=construction.element_sort, arity_log2=3,
        query_sort=construction.query_sort, domain_separation=construction.domain_separation,
        binding_game=construction.binding_game,
    )
    built = core.build_core(small)
    _record(sink, core.admit_core(built))
    leaves = core.honest_leaves(small)
    for mutation in core.Mutation:
        try:
            _record(sink, core.run_opening(built, leaves, 0, mutation))
        except Exception:
            pass
        try:
            _record(sink, core.admit_core(core.mutate_core(built, mutation)))
        except Exception:
            pass
    sys.path.remove(str(root))
    return sink


def probe_logup() -> dict[str, set]:
    root = EVALUATION / "r2-probe-logup"
    sys.path.insert(0, str(root))
    logup = _load(root, "logup_model.logup")
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    for variant in logup.Variant:
        built = logup.build_core(variant)
        _record(sink, logup.admit_core(built))
        for mutation in logup.Mutation:
            try:
                _record(sink, logup.admit_core(logup.mutate(built, mutation)))
            except Exception:
                pass
    sys.path.remove(str(root))
    return sink


def probe_value_bridges() -> dict[str, set]:
    root = EVALUATION / "r2-probe-value-bridges"
    bridges = _load(root, "value_bridge_model.bridges")
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    Bridge, Lane = bridges.Bridge, bridges.Lane
    variants = [
        Bridge("b", Lane.BIJECTION, "s", "t"),
        Bridge("b", Lane.BIJECTION, "s", "t", image_predicate="i"),
        Bridge("b", Lane.BIJECTION, "s", "t", loss_bits=40, collision_relation="c"),
        Bridge("e", Lane.EMBEDDING, "s", "t", image_predicate="i"),
        Bridge("e", Lane.EMBEDDING, "s", "t"),
        Bridge("e", Lane.EMBEDDING, "s", "t", image_predicate="i", loss_bits=40),
        Bridge("p", Lane.PROJECTION, "s", "t", collision_relation="c", loss_bits=40, occurrence_count=1),
        Bridge("p", Lane.PROJECTION, "s", "t", collision_relation="c", loss_bits=40, occurrence_count=1, image_predicate="i"),
        Bridge("p", Lane.PROJECTION, "s", "t", loss_bits=40, occurrence_count=1),
        Bridge("p", Lane.PROJECTION, "s", "t", collision_relation="c", occurrence_count=1),
        Bridge("p", Lane.PROJECTION, "s", "t", collision_relation="c", loss_bits=40),
        "not-a-bridge",
    ]
    for bridge in variants:
        _record(sink, bridges.admit_bridge(bridge))
    for count, rule in ((1, None), (3, "anchors-are-sealed-digests"), (0, None)):
        _record(sink, bridges.price_projection(bridges.ANCHOR_PROJECTION, count, rule))
    _record(sink, bridges.price_projection(variants[3], 1, None))
    return sink


def probe_guard_cost() -> dict[str, set]:
    root = EVALUATION / "r2-probe-guard-cost"
    guards = _load(root, "guard_model.guards")
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    default = guards.GuardProfile("r2.probe.guard.default")
    thrifty = guards.GuardProfile("r2.probe.guard.thrifty", max_nodes=4096, max_work=100)
    _record(sink, guards.admit_guard(default, guards.pairing_formula(4), guards.interleaved_order(4)))
    # The declared default bound, not an ad-hoc narrow one: an envelope that only
    # ever refuses under a profile invented for the test declares nothing.
    _record(sink, guards.admit_guard(default, guards.pairing_formula(8), guards.separated_order(8)))
    # Work and size are bounded separately, so they refuse at separate boundaries.
    _record(sink, guards.admit_guard(thrifty, guards.pairing_formula(8), guards.separated_order(8)))
    _record(sink, guards.admit_guard(default, guards.BooleanAtom("absent"), ("bool:present",)))
    return sink


def probe_fri() -> dict[str, set]:
    """The FRI witness already publishes its measured outcomes."""

    frozen = json.loads(
        (EVALUATION / "r2-protocol-model" / "cases" / "expected-results.json").read_text()
    )
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    for case in frozen["cases"].values():
        triple = (case["outcome"], case["boundary"], case["code"])
        if case["outcome"] == "Affirmative":
            sink["positives"].add(triple)
        else:
            sink["negatives"].add(triple)
        sink["codes"].add(case["code"])
    return sink


def probe_p01() -> dict[str, set]:
    """Schnorr publishes its evidence through a frozen oracle."""

    frozen = json.loads(
        (EVALUATION / "r2-p01-schnorr" / "cases" / "expected-results.json").read_text()
    )
    sink: dict[str, set] = {"positives": set(), "negatives": set(), "codes": set()}
    for case in frozen["cases"].values():
        triple = (case["outcome"], case["boundary"], case["code"])
        if case["outcome"] == "Affirmative":
            sink["positives"].add(triple)
        else:
            sink["negatives"].add(triple)
        sink["codes"].add(case["code"])
    return sink


PROBES: dict[str, Callable[[], dict[str, set]]] = {
    "fri": probe_fri,
    "schnorr": probe_p01,
    "commitment": probe_commitment,
    "logup": probe_logup,
    "value-bridges": probe_value_bridges,
    "guard-cost": probe_guard_cost,
}


# --- reporting ----------------------------------------------------------------


def measure() -> dict[str, Any]:
    per_witness: dict[str, dict[str, Any]] = {}
    boundaries: set[str] = set()
    for name, probe in PROBES.items():
        sink = probe()
        per_witness[name] = {
            "positives": sorted(sink["positives"]),
            "negatives": sorted(sink["negatives"]),
            "codes": sorted(sink["codes"]),
        }
        boundaries |= {triple[1] for triple in sink["negatives"]}
    verdicts: dict[str, Any] = {}
    for ident, entry in sorted(LEDGER.items()):
        want: set[str] = entry["boundaries"]
        met = want & boundaries
        if not want:
            state = "boundary-uncovered"
        elif met == want:
            state = "boundary-covered"
        elif met:
            state = "boundary-partial"
        else:
            state = "boundary-uncovered"
        # Reaching every claimed boundary is necessary, not sufficient: the
        # boundary must also be the one the invariant's pressure asks for.  That
        # pairing cannot be measured from a run, so an entry states the gap it
        # knows about and is held to boundary-partial until the gap is resolved.
        gap = entry.get("gap")
        if gap and state == "boundary-covered":
            state = "boundary-partial"
        verdicts[ident] = {
            "title": entry["title"],
            "state": state,
            "required": sorted(want),
            "met": sorted(met),
            "gap": gap,
        }
    return {"witnesses": per_witness, "invariants": verdicts, "boundaries": sorted(boundaries)}


def render(report: dict[str, Any]) -> str:
    lines = ["witness            positives  negatives  codes"]
    for name, data in report["witnesses"].items():
        lines.append(
            f"  {name:<16} {len(data['positives']):>9}  {len(data['negatives']):>9}  {len(data['codes']):>5}"
        )
    lines.append("")
    lines.append("invariant  coverage-state        title")
    tally: dict[str, int] = {
        "boundary-covered": 0,
        "boundary-partial": 0,
        "boundary-uncovered": 0,
    }
    for ident, verdict in report["invariants"].items():
        tally[verdict["state"]] += 1
        missing = set(verdict["required"]) - set(verdict["met"])
        suffix = f"   missing: {', '.join(sorted(missing))}" if missing else ""
        lines.append(
            f"  {ident:<8} {verdict['state']:<20} {verdict['title']}{suffix}"
        )
        if verdict.get("gap"):
            lines.append(f"  {'':<8} {'':<20} pressure gap: {verdict['gap']}")
    lines.append("")
    lines.append(
        f"boundary-covered {tally['boundary-covered']}  "
        f"boundary-partial {tally['boundary-partial']}  "
        f"boundary-uncovered {tally['boundary-uncovered']}"
        f"   (of {len(report['invariants'])} tracked)"
    )
    return "\n".join(lines)


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    report = measure()
    print(json.dumps(report, indent=2, sort_keys=True) if args.json else render(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
