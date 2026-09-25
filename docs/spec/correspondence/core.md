# Core specification and Formal correspondence

[Execution](../core/execution.md) and
[Observations](../core/observations.md) own the definitions; the
[effect-tree rationale](../../rationale/effect-tree-bodies.md) explains the
alternatives. This map records exact support and limits;
it does not supply semantics by listing a declaration name.

## How to read the map

**D** means correspondence with a mathematical definition.
**T** means a kernel-checked proposition with the stated hypotheses.
**O** means a policy, source obligation or implementation correspondence that
the generic definitions do not automatically establish. Mixed entries identify
the mathematical part and its application boundary separately.

All variables in the statements are universally quantified at their declared
types unless an existential is written. Deterministic handler functions are
total mathematical functions. Return types agree in `Related`; state and event
types may differ. A proof of a proposition is distinct from checking that an
actual frontend, native operation or cryptographic provider supplies its premises.

| Clause | Kind and exact declarations | Hypotheses and scope retained |
|---|---|---|
| [CORE-01](../core/execution.md#signatures), [bodies](../core/execution.md#bodies) | D: `PIR.Signature`, `PIR.Proc` | Dependent reply type; inductive body. O: capture/source admissibility and portable syntax are separate. `Proc` does not enforce a public bound or physical participant locality. |
| [CORE-02](../core/execution.md#outcomes), [complete results](../core/execution.md#complete-results) | D: `PIR.Stop`, `PIR.Outcome`, `PIR.Execution`, `PIR.Handler` | Five distinct stop constructors and a complete result. O: cause descriptions, diagnostic detail, admission and verifier meanings are supplied by the applicable contracts; the enum does not check them. |
| [CORE-03](../core/execution.md#sequencing) | D: `PIR.Execution.follow` | On stop retain state/events/reason and skip the continuation; on return use actual state and append events. No ambient effects or outer-monad failure are covered by this deterministic definition. |
| [CORE-04](../core/execution.md#deterministic-interpretation) | D: `PIR.Proc.run` | Done/halt/call equations. O: a native implementation must relate its actual transitions and failure effects to this handler; no automatic rollback or termination proof. |
| [CORE-05](../core/execution.md#body-composition) | D: `PIR.Proc.bind`; T: `PIR.follow_assoc`, `PIR.run_bind`, `PIR.replacement_then` | Complete execution equality at the selected initial state; identical handler and suffix. Associativity retains event order and does not establish commutation. |
| [CORE-06](../core/execution.md#call-boundary) | D: `PIR.Proc.run` fixes the continuation boundary | O: mathematical totality and atomic controller scope; a finer native execution needs its own correspondence. No theorem here proves scheduling, native termination, reentrancy or concurrency properties. |
| [CORE-07](../core/execution.md#uniform-call-bounds) | D: `PIR.Within`; T: `PIR.ExecutionPath.calls_bounded` | Bound over every interface-typed reply; actual run may stop. The bound counts instrumented calls, not emitted events or internal costs. O: frontend admission must establish the bound for its actual body and public instance. |
| [CORE-08](../core/observations.md#event-projections) | D: `PIR.observeEvents`; T: `PIR.observe_append` | Fixed per-event projections into lists; concatenation preserved. O: selecting and binding the observer to a claim is not enforced by the function's type. |
| [CORE-09](../core/observations.md#execution-relation) | D: `PIR.Related` | Exact shared-type outcomes, relation on actual final states including stops, equality of the selected traces. O: soundness of a representation or privacy interpretation is not automatic. |
| [CORE-10](../core/observations.md#sequential-composition), [handler replacement](../core/observations.md#handler-replacement), [transitive composition](../core/observations.md#transitive-composition) | D: `PIR.HandlerRelated`; T: `PIR.related_follow`, `PIR.run_related`, `PIR.related_trans` | Per-operation laws for every related input state; initial relation; same reply-adaptive body. Sequential continuations cover every common reply and related state. Transitivity uses one middle execution/observer and existential intermediate state. |
| [CORE-11](../core/observations.md#final-state-observations), [context scope](../core/observations.md#context-scope) | T: `PIR.related_observer` | State projection compatibility for every related pair plus `Related`. O: cross-world disclosure, target contexts and security claims need their own experiments/relations and actual interfaces. |
| [CORE-12](../core/execution.md#outer-effects) | D: `PIR.MonadHandler`, `PIR.Execution.followM`, `PIR.Proc.runM` | `Monad M`; an outer effect need not produce a complete execution. O: an inspectable outer failure requires an explicit adapter. |
| [CORE-13](../core/execution.md#outer-effects) | T: `PIR.runM_bind`, `PIR.runM_pure`, `PIR.runM_lift` | First two use `LawfulMonad`; lifting uses `MonadLiftT` and `LawfulMonadLiftT` preserving bind/pure, with the source/target monads. O: normalization, joint laws, security and preservation of stopped mass are properties of the selected probability interpretation, not monad-class consequences. |
| [CORE-14](../core/execution.md#actual-call-records) | D: `PIR.ExecutionPath.handler`; T: `PIR.ExecutionPath.erasure`, `PIR.ExecutionPath.calls_permitted`, `PIR.ExecutionPath.calls_bounded` | Erasure needs no admission premise. Permission needs `Conforms P p phase`. The count bound independently needs `Within n p`; neither conformance nor honest replies are needed for that theorem. A stopped invocation records its input phase, not a fabricated reply transition. |
| [CORE-15](../core/execution.md#persistent-history) | T: `PIR.ExecutionPath.run_recorded` | For every operation and state, `log` of the actual handler post-state equals old `log` followed by actual emitted events. This premise includes stopped results. No history is reconstructed without it. |

## Declaration owners and consumer boundary

- [Execution](../../../formal/Zkc/Semantics/Execution.lean): signature, body,
  outcomes, deterministic sequencing and equal-result relations.
- [Interaction](../../../formal/Zkc/Semantics/Interaction.lean): the `Within`
  definition. Its phase/role/source contracts belong to the language chapters.
- [MonadExecution](../../../formal/Zkc/Semantics/MonadExecution.lean): monadic
  execution and laws. Its distributional-state expansion is an application
  outside the core.
- [ExecutionPath](../../../formal/Zkc/Semantics/ExecutionPath.lean): call records,
  erasure, actual permission, actual count and persistent history.
- [Source](../../guides/source-and-inputs.md), [probability](../../guides/security-properties.md#probability-initialization-and-persistent-providers),
  [properties](../../guides/security-properties.md) and [realization](../../guides/realization.md)
  explain the admission and application contracts that the other chapters of
  the [specification](../README.md) define.

The core does not restate `Contract`/`Satisfies`, phase formation, bounded
repetition, heterogeneous realization or disclosure. The foundation build
includes some of those dependencies; building them does not enlarge the core's
normative scope.

## Controls and what they refute

The [core controls](../../../formal/Tests/SpecCore.lean) establish:

| Control | Unsupported inference it rules out |
|---|---|
| `Tests.SpecCore.equal_visible_prefix_does_not_justify_suffix` | Same returned value and event list imply a same-suffix replacement, regardless of residual state |
| `Tests.SpecCore.related_does_not_license_arbitrary_state_view` | An arbitrary residual relation licenses publishing final states verbatim |
| `Tests.SpecCore.erased_trace_agreement_does_not_imply_public_agreement` | Equality after event erasure establishes equality under the public observer |
| `Tests.SpecCore.stopping_invocation_counts_once` | A terminal call disappears from the count, its event count equals call count, its phase advances, or its suffix runs |
| `Tests.SpecCore.public_bound_applies_to_stopping_invocation` | An all-reply bound is usable only on successful executions |

The last two quantify over every `Stop` reason. The count application consumes
the generic theorem rather than proving the example by arithmetic alone.
The first three are counterexamples to weaker hypotheses, not examples of
a flawed existing `Related` theorem.

[Existing execution controls](../../../formal/Tests/Execution.lean) cover returned
errors versus terminal stops, state/prefix retention, weak postconditions,
acceptance followed by abort and the nonuniform well-founded tree.
[OuterEffects](../../../formal/Tests/OuterEffects.lean) distinguishes lost outer
reports from retained inner stops and is imported by the foundation
controls. [Simulation controls](../../../formal/Tests/Simulation.lean) retain
stopped-state, missing-event, wrong-stop and final-state-dependent handle
counterexamples. Those representation laws are supporting checks, not an
adoption of the entire native relation.

## Reproduction

From the repository root, use a fresh output path:

```sh
python3 formal/checks/check_foundation.py --output /tmp/zkc-foundation-recheck
python3 formal/checks/check_library.py
python3 formal/checks/audit_imports.py
python3 tests/check_docs.py --output /tmp/zkc-docs-recheck.json
```

The foundation command copies its exact local import closure into a fresh
package and builds without prior objects or external package imports. Its
header-parser step uses the configured root Lake environment; the root package
still has its declared Mathlib dependency. Therefore this is an independent
foundation build, not a claim that an unprovisioned root checkout installs
without package resolution.

The foundation audit checks stored declarations and proof dependencies against
the allowed axioms `propext`, `Classical.choice` and `Quot.sound`; a placeholder
or unexpected owned axiom fails. Source hashes are checked against the copied
inputs again after the build. Import/library checks cover architectural
boundaries; the documentation checker covers inline links,
heading fragments and whitespace. Neither a link check nor declaration-name
resolution establishes prose-to-Formal semantic equivalence.

## Profiles

Common core definitions remain in place. Moved protocol constructions use the same
interpretation/admission laws; a profile directory is not an additional semantic layer.

## Outer finite-step controllers

[Iteration](../core/iteration.md) corresponds to
[`PIR.Iteration`](../../../formal/Zkc/Semantics/Iteration.lean).
`approximate_add` and `evaluate_add` establish prefix composition;
`evaluateM_add` lifts it through the selected lawful monad and
`evaluateM_pure` recovers deterministic execution;
`finished_stable` and `finished_unique` establish terminal stability;
`Diverges` and `Terminates` classify the deterministic total-handler reference.
`interpret_approximate`, `approximate_admission`, `within_approximate` and
`evaluate_related` transport their explicit per-body premises.
`close_state` and `close_events` retain effects at a deployment cap.
The Rust controller has differential evidence, not a native refinement proof.

`approximate_blocks` preserves the finite process under a multiplied horizon.
`Boundary.within_bind_of_returns` and `within_approximate_of_invariant` use
certified return invariants instead of requiring bounds for unreachable seeds.
[`Zkc.Realization.Iteration`](../../../formal/Zkc/Realization/Iteration.lean)
uses `Execution.Relates` for state-dependent continuation/result representation;
`evaluate_relates` and `close_relates` keep exact tags, stops and observations.
`Tests.IterationBounds` and `Tests.IterationRepresentation` exercise these laws.
