# F2-P0 Schnorr Relations--Plan coupling audit

This package asks one question at cutoff
`de49641aba0086b1e3f7eff48f5276ffd8af2845`:

> Can the current `docs-next/relations` and
> `docs-next/pir/interfaces-and-plans.md` contracts alone select and exactly
> couple a finite relation definition, semantic model, instance, and Plan
> strategy roles to the F1-R1B Schnorr target?

The frozen answer is
`CannotAnswer/F2P0-C-EXACT-COUPLING-UNDERDETERMINED`.

The contracts are expressive enough for an acyclic **conditional attachment
shape** once separately authored and admitted Relations and Plan operands are
supplied. They do not derive or select those operands from the current Core,
its verifier equation, or its two Prover decision sites. The current F1-R1B
subject therefore still has no coordinate for any of F2-O0's five property
premises.

Run the offline, standard-library-only gate from the repository root:

```sh
python3 -B evaluation/formal-schnorr-relations-plan-f2p0/run.py --check
```

It freezes 30 findings: 12 affirmative bounded observations, five refused
inferences, and 13 `CannotAnswer` boundaries.

The contract ledger is re-pinned to the current Interface/Plan bytes. The
new owner-compiler block shifts the cited Plan ranges but does not alter their
text, the two reconstructed candidate completions, or any frozen outcome.

## Exact conditional shape

The forward route supported by the contracts is:

```text
RelationDefinition -> RelationInterface -> RelationSemanticModel
                                    \-----> RelationInstance (per invocation)

Protocol -> ProtocolRelationBinding -------------------> RelationInterface

ProverPlan -> PlanRealizes -> PlanStrategyStep
     |
     +-> PlanWitnessSurface -> PlanWitnessBinding -----> RelationInterface
```

`ProtocolRelationBinding` and `PlanWitnessBinding` are deliberately
independent. The first never reads a Plan; the second reads a source-ID-free
`PlanWitnessSurface`, not a `ProverPlanId` or private source map. A checked
aggregate may retain both, but neither binding creates a combined owner or an
honesty proposition.

That shape does not provide the operands. An exact definition needs a selected
definition language and payload. A model needs a selected evaluator and a
separate definition/model correspondence. An instance needs exact public
values for one invocation. A Plan needs selected private-material,
randomness, state, and recipe declarations and a `PlanRealizes` result. None is
present in F1-R1B.

## Five-premise matrix

| F2-O0 premise | Current F1 role site | Coordinate after separately authored bundle | What still is not established |
|---|---|---|---|
| relation predicate | Statement binding 0 names only the public side | `RelationSemanticModel.evaluator` and occurrence-local `CheckedRelationSatisfaction` | a total provider `Stmt -> Wit -> Bool`, termination basis, and acceptance correspondence |
| witness type | none | `RelationInterface.private_witness[i].value_type`, joined to a Plan occurrence by `PlanWitnessBinding.witness_edges[i]` | representation translation if the provider does not reuse the exact type |
| Prover private state | none | `ProverPlan.persistent_state[i]` and adapter `PlanExecutionState` | a checked projection of the richer adapter-private state into one provider `PrvState` |
| honest commit | decision 0 only | `ProverPlan.decision_recipes[0]` and `PlanStrategyStep` at decision 0 | relation-relative honesty/correctness and provider-field correspondence |
| honest respond | decision 2 only | `ProverPlan.decision_recipes[2]` and `PlanStrategyStep` at decision 2 | relation-relative honesty/correctness and provider-field correspondence |

Thus all five have a **contract-defined destination family**, and commit and
respond already have exact **role sites**. Zero of five has a current premise
coordinate in the admitted F1 target. Even after authoring a bundle,
`PlanRealizes` proves structural coverage, typed dataflow, read confinement,
and state closure only; it does not prove witness satisfaction, algorithmic
correctness, completeness, or any cryptographic property.

The relation evaluator is also an exact deterministic **partial** decision
procedure. The Relations contract explicitly requires a separate termination
basis before treating every admitted model as a total Boolean predicate.

## Two independent reconstruction paths

[`model.py`](model.py) follows the forward typed route. It admits the exact
F1-R1B Core and Fresh Protocol, reads the typed Statement and decision sites,
checks two K1 evaluator samples, reconstructs the finite verifier table, and
validates every cited contract range and predecessor digest.

[`independent.py`](independent.py) follows a reverse falsification route. It
uses the B1 clean-room owner-view compiler, decodes the Statement and decision
coordinates from canonical bodies, interprets all 81 verifier-term inputs with
F1-R1B's separately written term interpreter, and reconstructs two incompatible
finite completions. The two files do not import one another.

[`run.py`](run.py) requires byte-for-byte equality of their canonical subject,
contract route, premise matrix, and countermodel report, then compares the
result with [`expected-findings.json`](expected-findings.json).

## Finite non-selection witnesses

The exact target check is `z = a + c*y (mod 3)`. Two incompatible completions
make every enumerated honest run accept:

| Completion | Relation and witness | Private state | commit | respond | Honest runs |
|---|---|---|---|---|---:|
| knowledge-shaped | `x : Z3`, `rel(y,x) iff y=x` | nonce `r : Z3` | `a := r` | `z := r+c*x` | 27/27 |
| statement-only | `unit : Unit`, relation always true | `Unit` | `a := 0` | `z := c*y` | 9/9 |

Adding one to each response makes all 36 controls reject. These completions are
not proposed semantics and are not admitted Relations or Plan objects. Their
only purpose is to falsify unique reconstruction: the same verifier target and
generic contracts permit different relation predicates, witness carriers,
private states, commit algorithms, and response algorithms.

## Contract clauses pinned by the gate

Exact ranges and full-file digests are in
[`contract-ledger.json`](contract-ledger.json). The decisive clauses are:

- relation Definition, Interface, Instance, Model, and satisfaction:
  `relation-model.md` lines 562--584, 672--716, 759--810, 847--937, and
  1007--1070;
- independent Protocol and Plan attachment paths: `relations/README.md`
  lines 74--86;
- `ProtocolRelationBinding`: `relation-model.md` lines 1607--1688;
- `PlanWitnessBinding`: `relation-model.md` lines 1917--1962;
- Plan subject, recipes, `PlanRealizes`, and its non-claims:
  `interfaces-and-plans.md` lines 687--753, 853--1029, and 1184--1189;
- adapter state and exact recipe execution: `interfaces-and-plans.md`
  lines 1267--1378; and
- source-ID-free `PlanWitnessSurface`: `interfaces-and-plans.md`
  lines 1623--1688.

## Non-claims and disposition

This package does not author or admit a relation, model, instance, Plan,
binding, satisfaction result, provider translation, completeness proposition,
or security theorem. It does not select either finite completion, change an
owner page, alter PIR semantics, or claim that verifier acceptance is relation
satisfaction.

No owner-page change is recommended by this audit. The contracts already make
the separation and non-claims explicit. A follow-on may author exact candidate
operands and ask a separately owned correspondence/applicability proposition;
that is new subject evidence, not a reason to fill an existing contract's
deliberate gap by inference.
