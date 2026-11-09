# Authoring with Process contracts

The model clients are [AdaptiveChecks](../ProtocolProofExamples/AdaptiveChecks.lean) and
[SharedState](../ProtocolProofExamples/SharedState.lean). Their Process migrations supply the
examples below; final integration validation is tracked separately in
[IMPLEMENTATION.md](IMPLEMENTATION.md). They are mathematical model games, not translations of
a concrete zkc artifact. The first has arbitrary nested rounds and history-dependent strategies;
the second has a persistent shared challenge, observable state, an erased audit counter and
components containing several primitive operations.

Author `PIR.Process I A` from the shared `ZkcProgram` foundation. `PIR.Process.call operation .done`
is a single typed service call; `do` notation uses Process bind. A `.halt reason`, or a stopped
service reply, prevents subsequent calls. `System E I S L` fixes complete primitive kernels and
the initial law; `system.experiment client` returns `Execution S L A`, including reached state
and ordered events on every stop. No author-facing FreeM translation is needed.

## Fix the claim before selecting its proof

A request fixes the experiment, the admitted environments, the observation and the bound. The
soundness constructor computes acceptance in the request's negative promise region. Completeness
requires unconditional accepting mass at least `1 - error`. Neither proof method chooses those
facts. For example, the adaptive client's exact requests are `soundnessRequest count width`
and `completenessRequest count width`; both use `system.experiment (game count width)`.

The examples explicitly choose the environment interface. `AdaptiveChecks.Strategy` is a
function from prior challenge history to the next bit. It cannot read the current fresh
challenge before choosing that bit. This test quantifies over all such deterministic strategies;
it does not assert a separate resource-bounded cryptographic adversary theorem.

## Write or reuse the mathematical contract

`OperationSpec I S L` consumes a continuation potential of type
`Outcome (I.Reply operation) → (S × List L) → ENNReal`. The exact specification is
`opExpectation (system.accumulatedOperations environment)`. The fair-bit model averages the
two returned continuations at their reached state/log. `UpperBound.bind` and `LowerBound.bind`
combine contracts without assuming independence.

Bind also requires `hstop` for every stopped reason: upper bounds need
`reward (.stopped reason) ≤ post (.stopped reason)`, while lower bounds need the reverse.
Finite iteration carries the corresponding stopped-branch inequality at every round.
Measurable terminal rewards/events and countable operation replies with measurable singletons
remain explicit premises where the probability and transport theorems require them.

For arbitrary rounds, the author supplies an indexed invariant and a body contract. The
adaptive example uses a remaining-error potential of this shape:

```lean
fun round out _ => resultReward
  (fun next => reward next.2 (factor residual ^ (count - round) * value)) out
```

Here `resultReward` assigns the displayed reward to a returned accumulator and zero to a
stopped outcome. Its one-round mathematics is in `primitive_upper` and `primitive_lower`.
The round and batch proofs invoke the same `UpperBound.iterate` and `LowerBound.iterate`
rules with explicit `hstop`. A batch is a body for the next loop; no additional structural
traversal theorem is authored.

The shared-state example uses the indicator that the first guess matches the hidden bit as
its potential. Its integral is one half. The second check uses the same bit, so there is no
second independent factor of one half. The theorem `multiplying_check_probabilities_invalid`
proves that the proposed product bound is false.

## Install a representation once

If the actual and mathematical systems agree, reuse `Installation.reflexive`. For a state/log
representation, prove its measurable local joint-law meaning and whole initial-law pushforward,
then use `Installation.ofMap`. The map is from `S × List L` to `T × List M`; its target needs
the stated measurable equality instance. Both systems still use the same Signature and complete
reply meanings. There is no public `Connection` alias.

The shared-state client erases an audit counter but retains the hidden challenge, observable
check counter and event prefix. Its primitive full-record equation is:

```lean
(primitiveConcrete operation state).map
    (fun out => (⟨out.outcome, represent out.state, out.events⟩ :
      Execution ModelState Unit Reply)) =
  primitiveModel operation (represent state)
```

For installation, `representAccumulated` preserves the prefix as well as mapping state.
`Representation.contractOfMap` uses the corresponding equation on `accumulatedOperations` to
construct the joint coupling and graph relation. Initial coverage is an equality between the
pushforward of the entire actual `initialWithEvents` measure and the model measure; covering
one convenient initial state is insufficient.

The high-level `componentImplementation : OperationInterpretation Component Primitive`
performs two primitive calls per operation. Its handlers run that Process implementation under
the deterministic primitive handlers. `model_implementation` and `concrete_implementation`
use `System.run_eq_dirac` to relate these to the public probability kernels.
`component_inlining` then uses `Process.interpret` and `Process.run_interpret` to equate the
hierarchical and inlined complete executions. The representation and installation preserve
shared state through later calls. `resetting_counter_invalid` rejects a reset of the retained
observable counter. This model does not claim the broader service-wiring or decoder API.

## Assemble the fixed root

`UpperEvidence` and `LowerEvidence` contain `subject`, `installation`, `spec`, `local_bound`,
`model_event`, `measurable_event`, `terminal`, `potential`, `mathematics` and `budget`.
The terminal implication compares complete Execution records: actual bad implies model bad
for upper bounds; model acceptance implies actual acceptance for lower bounds. The budget
integrates the potential over the whole model `initialWithEvents` law. The final proof is, for example:

```lean
theorem shared_soundness : soundness.Holds := soundnessEvidence.establish

theorem shared_completeness : completeness.Holds := completenessEvidence.establish
```

The public root theorem reuses the existing backend closure to derive the probability claim.
No evidence field has the type
`soundness.Holds`, `completeness.Holds`, or a renamed copy of that final conclusion. An arbitrary
whole-game mathematical theorem can still be used as a proof method, but is never presented as
an automatically discharged local operation obligation.

## What is reusable, and what remains authored

| Input | Current treatment |
| --- | --- |
| Program and probability meaning | Canonical Process, one internal upstream kernel interpretation |
| From local joint laws to every adaptive client | Reused upstream theorem and generic event corollaries |
| Bind, branch, finite and nested iteration | Process rules with explicit stop obligations, reusing backend contracts |
| Identity representation | Common constructor |
| Meaningful representation or component implementation | Library/companion supplies the map and local meaning laws |
| Degree/root/proximity algebra or a new residual invariant | Mathematical library or companion |
| Initial coverage and requested observation implication | Explicit mathematical obligations, reusable when representations agree |
| Applying contracts and selecting invariants in these examples | Ordinary Lean theorem applications and simplification |
| Automatic construction, concrete IR binding, generated companions | Later construction/integration owners |

Structural theorem reuse is implemented. A proof-search tactic or source-to-proof generator is
not required to use this core and is not claimed as implemented. Such tooling must produce
these same checked judgments. It must not weaken the request, replace a missing meaning law
with a name match, or ask each new protocol author to write another structural visitor.

The shared-state soundness and honest-completeness clients intentionally have different permitted
interactions: the honest client reveals the private bit before checking; the adversarial client
only receives previous check replies. They validate contextual composition and state handling.
They are not presented as a proof of knowledge, or as Schnorr AND security.

## Selecting another property

[PropertyProfiles](../ProtocolProofExamples/PropertyProfiles.lean) supplies complete extraction
and simulation examples; [ClaimBoundaries](../ProtocolProofExamples/ClaimBoundaries.lean)
supplies promise-gap, abort, conditional-receipt and nonvacuity examples. See [CLAIMS.md](CLAIMS.md)
for the complete author-facing fields and quantifiers.

For extraction, fix the Process algorithm, service access, Event type, public target, witness
relation and success function first. Success requires a valid `.returned (some witness)` in
the complete record; `none`, invalid witnesses and all stops retain their mass as failure.
Prove `successRequest environment` for every admitted environment, using the
ordinary lower-bound methods or a direct probability argument, and prove `CallsBounded`.
`ExtractionRequest.establish` assembles these two facts. It is an interface-closing theorem,
not a proof of a forking lemma or an automatic extractor constructor.

For simulation, fix the real `Outcome View` experiment, one Process simulator with allowed
public input/services, its Event type, valid context/witness pairs, error and call budget.
`Observation.outcome` projects the simulator's full Execution without discarding stops.
Prove the real/simulated view comparison and the resource bound. `establish_exact` reuses an
exact-law equality when available. A statistical argument can instead prove the fixed two-sided
comparison directly. Restricted observers use
their own request; proving a restricted family does not imply all-event statistical privacy.

The final value is `Receipt (.soundness request)` or the corresponding property constructor.
An arbitrary lemma uses `Receipt (.custom proposition)` and stays custom even if its proposition
happens to equal a built-in meaning. If a mathematical premise is still open, use
`ConditionalReceipt claim Premise`; close it only after that premise is proved.
