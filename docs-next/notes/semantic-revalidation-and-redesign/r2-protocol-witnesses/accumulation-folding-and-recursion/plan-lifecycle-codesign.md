# ProverPlan Lifecycle Co-Design

> **Kind:** Temporary cross-case architecture decision record
> **State:** Semantic target selected and durably absorbed; complete owner-
> profile publication, holdout validation, and independent identity/profile
> freeze remain separate gates
> **Authority:** None. Durable PIR, Relations, and OIR pages own the promoted
> laws. This page preserves the selection-time reasoning, mutations, and
> promotion ledger without claiming implementation or normative authority.
> **Supersession note:** Catalog counts and profile-graph snapshots on this
> page predate the later recursive-composition coverage schema and independent
> Analysis composition branch. Durable Relations and Analysis pages own the
> current 24-kind and six-profile target; the lifecycle laws here remain only
> their selection-time context.

## 1. Decision

Select one narrow, owner-local addition to `ProverPlan`: an
`AcceptedTerminalRecipe` for bounded private derivation after the exact
`Accept` terminal is reached, with no Prover move, Core-visible effect, or
hidden cross-run state mutation.

The name deliberately says `AcceptedTerminal`, not merely
“completion.” A `CompletedProtocolRecord` may be an FS interpretation failure,
and a terminal run may end in `Reject` or `Abort`. None of those permits the
private continuation output selected here.

The selected target organization is:

```text
static Plan identity
  |- private ingress, randomness, and execution-local state
  |- ordinary recipes at public ProverDecisionPoint occurrences
  `- bounded recipes at exact Accept terminal occurrences
          |
          `- atomic private witness exports

runtime Plan session
  |- exact private ingress and randomness authorities
  |- exact Plan-owned strategy adapter for the generated Core run
  |- sealed decision-local values and final post-decision state
  `- accepted-terminal continuation authority
```

This is a `ConservativeExtension` of Plan. It does not add an accumulator root,
a setup-result root, a runtime child Core, an opaque callback, or a new Core
event.

The typed public-Plan-parameter candidate is explicitly **deferred**, not
selected. The current cases can all use either a Core `PublicParameter` or a
Plan `Constant`, so they do not satisfy the frozen promotion rule in
[`research-contract.md`](research-contract.md): reuse convenience and avoiding
a second profile rotation are not independent semantic requirements.

## 2. Why the cases force the selected decision

### 2.1 Final-coin private evolution

The source-level pattern occurs in three distinct selected constructions.

| Source | Last public dependency | Public output | Private output after it |
|---|---|---|---|
| Nova Construction 1 | verifier challenge `r` after cross-term commitment `T_bar` | folded committed relaxed-R1CS instance | folded `(E,r_E,W,r_W)`, including retained private `T,r_T` |
| HyperNova Construction 1 | final challenge `rho` after Sumcheck and `sigma,theta` publications | folded LCCCS instance | folded private LCCCS witness |
| CycleFold Construction 7 | primary fold challenge `rho`, then the companion publication and final companion-fold challenge `rho_star` | evolved primary LCCCS and companion CRR1CS instances | primary witness after `rho`; companion witness after `rho_star` |

In Nova and HyperNova, the last Challenge is verifier-observable, the resulting
public instance is verifier-computable, and no later Prover message exists. In
CycleFold the primary private LCCCS witness depends only on `rho` and can be
exported at the subsequent ordinary decision that publishes the companion fold
material. The companion CRR1CS witness additionally depends on `rho_star`,
after which Construction 7 has no Prover event. The terminal extension is
therefore required for Nova's fold witness, HyperNova's fold witness, and
CycleFold's companion witness; it does not falsely assign `rho_star` as a
dependency of CycleFold's primary witness.

ProtoStar is the decisive negative control, not a fourth positive case. Its
accumulation prover computes and explicitly publishes `acc'.x` after deriving
`alpha`; that genuine post-Challenge Prover Message supplies an ordinary
decision site. The same ordinary decision recipe can publish `acc'.x` and
export `acc'.w`. Adding a terminal recipe there would duplicate an already
legal lifecycle and would fail the minimality test.

The exact source reconstruction and byte locks are in
[`nova-hypernova-and-protostar.md`](nova-hypernova-and-protostar.md). The
relevant primary loci are Nova Construction 1 steps 1--4, HyperNova
Construction 1 steps 6--8, CycleFold Construction 7, and ProtoStar Figure 3
steps 3--9 together with Figure 4 for the negative control.

The corrected two-cycle Nova case adds a separate causal warning: a private
output that is later used as the next step's witness must be linked to the
exact fold-output occurrence. Component satisfaction or equal values do not
supply that linkage.

### 2.2 Deferred public prover-only material

The package also records public prover-only material:

- HyperNova Construction 1 sets `pk=(pp,s_1)` and `vk=pp`; the prover uses
  relation structure absent from the minimal verifier key.
- Nova and corrected cycle-based Nova distinguish proving and verification
  projections even when one source presentation packages common parameters.
- ProtoStar permits the commitment key to be hardwired in the accumulation
  prover while the accumulation verifier consumes only the public commitment
  values and group operations; the separate decider has its own use.
- PLONK and Groth16 already showed universal-SRS or proving-key projections
  that an honest prover may need even when a deliberately minimal verifier
  does not.

The earlier control analysis is preserved in
[`groth16-qap.md`](../complete-argument-organizations/groth16-qap.md),
[`plonk-and-lookup.md`](../complete-argument-organizations/plonk-and-lookup.md),
and its explicit deferred-decision record
[`convergence-and-promotion.md`](../complete-argument-organizations/convergence-and-promotion.md).
Those records classify the full-common-setup and fixed-Plan-constant routes as
native and the reusable minimal-verifier route as the opportunity evaluated
here.

These cases do not make a new lane an expressibility prerequisite. Full common
setup can remain a Core `PublicParameter`, and one fixed Plan can embed one
exact value as a `Constant`. A parametric reusable Plan may be desirable, but
that is an ergonomics and reuse property, not a contradiction in the existing
grammar.

### 2.3 Why it is not co-promoted

Both candidates would rotate some of the same Plan and downstream profiles,
but shared edit cost is not a semantic law. The frozen research contract
permits a shared grammar change only when two materially different cases
require the same owner-local law or one case exposes a direct contradiction.
The accepted-terminal facility meets that threshold independently. The public
parameter lane does not: every present case has a native representation.
Consequently this record removes parameter declarations, runtime assignments,
OIR ingress, and parameter-dependent identity changes from the selected delta.

## 3. Candidate comparison

### 3.1 Existing and proposed Plan controls

| Candidate | Source fidelity | Authority and replay | Decision |
|---|---|---|---|
| Core `PublicParameter` | exact when verifier or transcript consumes the value | already closed | retain as native control |
| Plan `Constant(value)` | exact for one setup-specialized Plan | value rotates `ProverPlanId`; replay closed by Plan body | retain as native control |
| Plan `Advice` or `ConfidentialContext` for public setup | misclassifies a public value as private | wrong disclosure and supplier contract | reject |
| ambient file, registry, or host key lookup | no typed identity or exact substitution law | unreplayable and unauthoritative | reject |
| typed public prover parameter | potentially exact for a reusable, verifier-minimal Plan | would require its own exact identity, supply, and causal-use law | defer; current cases have native controls |
| ordinary decision recipe after a genuinely present final Prover event | exact when the source has that event, as ProtoStar does after `alpha` | already closed | retain as native control |
| precompute final witness before final Challenge | violates causal dependency | cannot replay the source computation | reject |
| retain the final witness in prior Plan state | impossible when state precedes the final Challenge | same causal defect | reject |
| artificial unit or witness message after final Challenge | changes Core schedule, transcript, cost, and Interface | replay is for a different Protocol | reject |
| Relations witness transform alone | can state a witness equation but cannot construct the private value or retain Plan randomness | no private producer authority | retain as proposition, not construction |
| accepted-terminal bounded recipe | preserves source schedule and makes private construction explicit | closed Plan/session/continuation law | select |

### 3.2 Broader research-contract candidates

| Candidate | Assessment |
|---|---|
| general post-Challenge callback | Reject. An opaque callback has no finite ABI, identity, exact-used dependency closure, deterministic bound, or replay law. A callback after every coin is much broader than the source pressure. |
| universal accumulator/folding root | Reject. Nova, HyperNova/CycleFold, and ProtoStar have different public state, relations, transcript domains, and decider boundaries. Their common need is a Plan lifecycle point, not one semantic accumulator type. |
| checked authoring construction | Defer for repeated family elaboration only. It may generate finite bodies, but it cannot replace runtime derivation from a fresh Challenge. |
| runtime child Protocol execution | Reject for this problem. It adds unresolved verdict, transcript, and authority composition while the sources have one flat verifier execution. |
| imported verifier placement | Retain the owner split: a pure verifier-observable Boolean verification routes to Core `Check`; richer verifier-observable transition, observation, or output behavior routes to `ModuleEffect`; verification embedded in the predicate being proved routes to Relations. None supplies private post-terminal derivation. |

No rejected candidate becomes valid merely because it can be implemented more
conveniently.

## 4. Deferred public Plan parameters

No `PublicProverParameterDecl`, operand arm, runtime assignment, endpoint
ingress, OIR requirement, or semantic-ID field is selected by this record.
Present cases use the following native controls:

1. if verifier behavior or transcript binding consumes the value, place it in
   Core as an exact `PublicParameter` and let Plan read the authenticated Core
   coordinate;
2. if the value is prover-only and fixed for one Plan, encode it as the exact
   typed `Constant`, accepting the corresponding `ProverPlanId` specialization;
3. never disguise public setup as advice/confidential context or fetch it from
   an ambient registry.

Setup correspondence, generator independence, ceremony trust, proving-key /
verification-key consistency, and theorem applicability remain explicit
Analysis premises with Evidence where available. A future public Plan
parameter proposal must present a new frozen contract and cases that require
parametric substitution rather than merely benefit from it; it must then close
identity, admission, runtime supply, causal use, transcript separation,
endpoint ingress, and replay as one independent decision.

## 5. Accepted-terminal recipes

### 5.1 Exact semantic point

An accepted-terminal recipe runs only after one exact Core terminal occurrence
has completed with static verdict `Accept`. It runs before the Plan execution
session is finalized, but after the ordinary `RunRecord` and Core causal
completion are fixed.

It never runs for:

- a `Reject` terminal;
- an `Abort` terminal;
- canonical-FS interpretation failure;
- `StrategyStopped` before a terminal;
- another inactive or not-reached `Accept` terminal; or
- a replayed record without the exact Plan-private session.

### 5.2 Site and read grammar

The Plan recipe grammar becomes site-explicit:

```text
PlanRecipeSiteRef =
    DecisionSite(ProverDecisionPointRef)
  | AcceptedTerminalSite(TerminalRef)

PlanReadCoordinate =
    StaticConstant(ConstantRef)
  | OpenPublicInput(PublicInputRef)
  | OpenedBinding(BindingRef)
  | ObservedMessage(OccurrenceRef)
  | ObservedChallenge(OccurrenceRef)
  | ObservedOraclePublication(OccurrenceRef)
  | ObservedOracleQuery(OccurrenceRef)
  | ObservedOracleAnswer(OccurrenceRef)
  | ObservedModuleValue(OccurrenceRef, observation_ordinal)
  | PriorOwnMove(ProverDecisionPointRef)
  | AcceptedTerminalPublicOutput(output_ordinal)

RecipeOperand =
    PlanRead(PlanReadCoordinate)
  | PrivateMaterial(PrivateMaterialRef)
  | PrivateRandomness(PrivateRandomnessRequirementRef)
  | StateBefore(StrategyStateSlotRef)
  | Constant(CanonicalValue<declared type>)
  | NodeOutput(RecipeNodeRef)
```

`AcceptedTerminalPublicOutput` is legal only inside the recipe keyed by that
same terminal. Its ordinal and type come from the terminal declaration. It
does not permit a recipe to name another inactive, earlier, or future
terminal.

Decision-site availability remains an exact alias of Protocol
`GuaranteedProverRead`. Accepted-terminal availability is a constructor-wise
Plan-profile predicate; it is not membership of every coordinate in Protocol
`VisibleHistory`, because constants, public invocation inputs, and prior own
moves live in other parts of `ProverView`:

```text
TerminalOccurrence(core,t) =
  the unique admitted OccurrenceRef whose effect is ReachTerminal(t)

GuaranteedAcceptedTerminalRead(P,t,StaticConstant(c)) = true
  exactly when c is an exact admitted Core constant

GuaranteedAcceptedTerminalRead(P,t,OpenPublicInput(i)) = true
  exactly when ProverInputOpening(i) is no later than
  BeforeOccurrence(TerminalOccurrence(P.core,t)) and the complete opening
  path is guaranteed on the t-active path

GuaranteedAcceptedTerminalRead(P,t,OpenedBinding(b)) = true
  under the analogous exact binding-opening and t-path law

GuaranteedAcceptedTerminalRead(P,t,Observed*(o,...)) = true
  exactly when o precedes TerminalOccurrence(P.core,t), has the requested
  source kind/type and Prover visibility, every source scope is guaranteed
  open on the t-active path, and
  GuardImplies(guard(t),guard(o))

GuaranteedAcceptedTerminalRead(P,t,PriorOwnMove(d)) = true
  under that same law and only when d is an exact earlier Prover decision

GuaranteedAcceptedTerminalRead(
  P,t,AcceptedTerminalPublicOutput(n)) = true
  exactly when n is an in-range public-output ordinal of t
```

Here `Observed*` expands to the six existing Message, Challenge, Oracle
publication/query/answer, and module-observation constructors with their exact
owner-specific type and visibility laws. Every arm additionally requires that
`t` is an exact `Accept` terminal of `P.core`; `guard(t)` abbreviates the guard
of `TerminalOccurrence(P.core,t)`. The predicate is derived from
existing Protocol owner views and laws, not from one sample `RunRecord`, a generic
history-membership test, or a caller-supplied Boolean. A terminal guarded by
`h` cannot read a message guarded by `g` unless the exact supported
`GuardImplies(h,g)` relation holds and every required source scope opens on
that path. Inability to derive this constructive scope/order/guard entailment
is a read disagreement even when no sample run reaches the terminal.

The cross-owner intake should be a checked `PlanLifecycleReadBasis` assembled
from the exact owner-issued `StrategyDecisionView`, `PublicBindingView`,
`PublicCoinView`, and `EffectView`, with their bindings and live capabilities.
It is an operation aggregate, not a new identity-bearing Protocol view.

### 5.3 Recipe and export grammar

```text
AcceptedTerminalRecipe = {
  nodes: CanonicalSeq<RecipeNode>
}

ProverPlan += {
  accepted_terminal_recipes:
    CanonicalMap<TerminalRef, AcceptedTerminalRecipe>
}

DerivedWitnessExport = {
  key: WitnessSurfaceKey,
  source_site: PlanRecipeSiteRef,
  value: RecipeValueRef,
  value_type: ValueType
}
```

Each completion node is a finite portable-algorithm application under the
same exact Foundation ABI, evaluation contract, local-DAG, and
tagged-partial-operation laws as a decision node. `NodeOutput` is local to the selected site. A
completion node cannot capture a node ordinal from a decision or another
terminal.

An accepted-terminal recipe has no `ProverMoveBinding` and no
`state_after`. It cannot publish a message or Oracle, invoke a module effect,
change a Core value, modify a terminal payload, create a claim, alter a
challenge prefix, or write hidden post-terminal state.

Private randomness generated for an earlier decision reaches terminal recipe evaluation
through an explicitly selected strategy-state value. The completion facility
does not reopen an erased entropy supplier after the Core run. Nova therefore
retains `(T,r_T)` in state at the cross-term decision and reads that state at
the accepted terminal.

Under the current first-availability law, a direct `PrivateRandomness`
operand remains legal only at an ordinary decision site. It is not legal at
an accepted-terminal site. Any value needed there must already have become an
explicit retained state value during the generated run.

The recipe map may omit an `Accept` terminal when the Plan declares no private
completion output there. A Plan cannot declare a recipe for `Reject` or
`Abort`. Equal-valued exports from two accepting terminals remain distinct
site-owned occurrences.

Plan admission requires every accepted-terminal recipe to own at least one
derived export, every terminal-scoped export to have exactly one matching
recipe, and every completion node to lie in the transitive operand closure of
at least one export owned by that recipe. A dangling export, output-free
recipe, or dead completion node is malformed Plan structure rather than a
semantic `PlanRealizes` disagreement. Terminal evaluation uses exactly this
export-rooted closure, so OIR reachability and runtime evaluation cannot differ.

### 5.4 Why state is read-only at completion

Post-terminal state update is rejected for the selected base model:

- there is no later decision in the run that can consume it;
- it is absent from `RunRecord` and Protocol replay;
- equal public runs could leave different hidden session states; and
- cross-run accumulation would become an ambient mutable channel.

A continuation witness is instead an explicit `DerivedWitnessExport` at its
exact decision or accepted-terminal source site. A later run receives it
through a distinct typed `WitnessIngress`; Relations and Analysis can then
state the exact recurrence edge. A future long-lived mutable prover session
would require its own transition identity, capability, replay, revocation, and
failure laws. It is not smuggled into Plan state here.

## 6. `PlanRealizes` consequences

The proposition remains structural and separately admitted. Its exact
additional work is:

1. authenticate the expanded lifecycle-read basis and require exact source
   authority agreement;
2. retain the existing complete Protocol decision coverage, decision-read, and move-
   shape checks without treating terminal sites as additional Core decisions;
3. check every terminal read with `GuaranteedAcceptedTerminalRead`, including
   scope, guard, visibility, order, and terminal-output origin;
4. check private-material, retained-state, constant, and node operands at the
   terminal site, while rejecting direct terminal
   randomness reads under the first-availability law;
5. interpret every witness export in its exact decision or accepted-terminal
   local namespace and require an all-path same-type value; and
6. require every Plan read used by either recipe class to occur in the
   authenticated body and exact-used dependency closure.

Terminal verdicts, recipe/export membership, DAG formation, algorithm ABI,
result types, absence of moves/state updates, and dead-node rejection are Plan
admission postconditions from Section 5.3, not semantic Negative reasons.

The negative coordinate grammar becomes site-aware:

```text
RecipeUseRef =
    NodeInput(PlanRecipeSiteRef, RecipeNodeRef, input_ordinal)
  | MovePayload(ProverDecisionPointRef)
  | StateReplacement(ProverDecisionPointRef, StrategyStateSlotRef)

PlanReadDisagreement =
    NotGuaranteedAtSite
  | TypeDisagreement {
      owner_type: ValueType,
      use_type: ValueType
    }
  | OriginDisagreement {
      requested: PlanReadCoordinate,
      owner_derived: PlanReadCoordinate
    }

PlanRealizesDisagreement +=
    SiteReadDisagreement {
      use: RecipeUseRef,
      site: PlanRecipeSiteRef,
      coordinate: PlanReadCoordinate,
      cause: PlanReadDisagreement
    }
```

This site-general algebra replaces the decision-only
`PlanViewReadDisagreement`; it does not reuse
`NotGuaranteedAtDecision` or require a terminal output to masquerade as a
`K2ProverReadCoordinate`. At a decision site, the owner Protocol coordinate is
mapped back through the exact constructor-preserving Plan/Protocol map before an
origin disagreement is formed. At a terminal site, the owner coordinate is
derived by `GuaranteedAcceptedTerminalRead`.

The existing `OperandAvailabilityDisagreement`, `MoveShapeDisagreement`, and
`WitnessExportValueUnavailable` remain. A missing source recipe suppresses
dependent arbitrary-node/export reasons exactly as a missing decision recipe
does now for required Protocol decisions. Terminal export/recipe membership is
already closed by Plan admission; an unreferenced `Accept` terminal does not
require an empty recipe.

Malformed local refs, duplicate maps, wrong terminal verdict, wrong owner
kind, unsupported algorithms, missing preimages, refusal, limit exhaustion,
and checker failure remain outside semantic Negative. Affirmative
`CheckedPlanRealizes` still proves only finite structural coverage, typing,
causal read confinement, and state closure. It proves neither that runtime
inputs exist nor that continuation completion succeeds or produces a
satisfying witness.

## 7. Execution and replay

### 7.1 Preparation and the exact Protocol adapter

The generic Protocol execution operation and its `ProverStrategyCapability`
interface remain unchanged. Plan owns the only adapter permitted to represent
an admitted Plan through that interface:

```text
PreparePlanExecution(
  exact admitted Protocol,
  exact admitted ProverPlan,
  exact affirmative CheckedPlanRealizes,
  exact CoreInvocation,
  exact private-material and randomness authorities,
  exact evaluator and deterministic limits)
    -> Affirmative({
         session: PreparedPlanExecution,
         capability: ReadyPlanExecutionCapability
       })
     | Unsupported | MissingDependency | KindMismatch | Malformed | Refused
     | DeterministicLimitExceeded | CheckerFailure

PlanStrategyStep(
  exact running PreparedPlanExecution S,
  identical internal PlanStrategyExecutionCapability,
  exact active Protocol ProverDecisionPoint d,
  identical Protocol ProverView V,
  exact adapter-private PlanExecutionState before_d)
    -> Produce(exact ProverMove for d,
               exact PlanExecutionState after_d)
     | Stop(qualified Plan strategy cause)
```

Preparation authenticates the identical Protocol, Plan, realization result,
invocation, owner-issued read basis, private inputs, randomness bearers,
evaluator, and limits. It evaluates every admitted state initializer atomically
and creates one process-local `PlanStrategyAdapter`. The prepared session and
its ready capability are noncopyable and nonserializable and have no semantic
ID. A stale, reconstructed, partially equal, cross-Plan, cross-Protocol,
cross-invocation, or cross-session aggregate refuses.

The adapter implements Protocol's existing `StrategyStep(private_state, ProverView,
private_randomness)` contract, but callers cannot supply or substitute its Protocol
strategy capability. `PreparePlanExecution` encloses the exact capability and
`GeneratePlanRun` passes it directly to Protocol after consuming the one-use ready
right. The adapter state contains the exact Plan state vector, remaining
randomness rights, next-step occurrence, and decision-local trace; none is an
ambient lookup or caller-provided callback.

For each active decision, `PlanStrategyStep` performs one indivisible
transition:

1. authenticate `d`, `V`, and `before_d` against the same running session and
   derive the unique admitted decision recipe through `CheckedPlanRealizes`;
2. materialize every and only the recipe's available public reads, exact
   private-material occurrences, typed constants, and `StateBefore` values;
3. consume each Plan randomness bearer exactly once at its first actual
   operand demand, which must occur no earlier than its declared availability
   boundary, make that sampled value available within that site's DAG, and
   permit later-site use only through an explicit state replacement;
4. evaluate the finite recipe DAG in canonical node order under the exact
   algorithm ABIs, evaluator, tagged partial-operation rules, and limits;
5. construct the unique message, Oracle, or module move required by the exact
   `ProverMoveBinding`, and evaluate the total `state_after` map; and
6. atomically return Protocol `Produce(move,after_d)` while sealing every local node
   and decision-derived export under that exact decision occurrence.

No move, state replacement, randomness consumption, or local export becomes
authoritative before all six steps succeed. An unavailable operand, exhausted
right, evaluator noncompletion, wrong view, or wrong move shape produces
`Stop` plus its qualified Plan cause and closes the running session; it cannot
fall back to an arbitrary prover strategy or expose a partial step trace.

At a decision site, `StateBefore(slot)` denotes the immutable value in
`before_d`. Once Protocol reaches a terminal, the adapter admits no further strategy
step and seals the exact state after the last active decision (or the exact
initialized state when no decision was active) as `final_plan_state`. At an
accepted-terminal site, `StateBefore(slot)` denotes exactly that sealed
`final_plan_state[slot]`: never the initial state, a caller-mutable buffer, or
a reconstruction from `RunRecord`.

### 7.2 Generation and continuation completion

```text
GeneratePlanRun(
  exact PreparedPlanExecution S,
  identical live ReadyPlanExecutionCapability for S,
  exact initial-Oracle, challenge-resolver, check, and extension capabilities
    required by S.protocol,
  exact S.execution_evaluation_control)
    -> CompletedPlanRun(
         RunRecord(S.protocol),
         CausalGenerationCapability,
         CausalPlanGenerationCapability,
         AcceptedPlanContinuationDisposition)
     | InterpretationFailed(ProtocolFailureRecord(S.protocol))
     | StrategyStopped(PartialRunRecord(S.protocol), qualified Plan cause)
     | qualified operational noncompletion

CompleteAcceptedPlanContinuation(
  exact CompletedPlanRun G whose RunRecord reaches Accept terminal t,
  identical live CausalPlanGenerationCapability,
  identical live AcceptedPlanContinuationRight from G,
  exact continuation evaluation control using G's identical evaluator)
    -> Affirmative(CompletedPlanContinuation(t, active_arm_outputs))
     | Unsupported | MissingDependency | KindMismatch | Malformed | Refused
     | DeterministicLimitExceeded | CheckerFailure
```

`GeneratePlanRun` consumes the ready capability exactly once and calls ordinary
Protocol `GenerateRun` with only the enclosed Plan adapter capability. Only
Protocol's `CompletedRun(RunRecord,CausalGenerationCapability)` branch can mint
`CausalPlanGenerationCapability`. That Plan-owned capability retains an
immutable snapshot of the exact prepared session, adapter, record object, Protocol
causal capability, evaluator, all active decision-local values and exports,
and `final_plan_state`. It contains no second ready or randomness right.
Interpretation failure, strategy stop, or operational noncompletion closes the
adapter and mints no Plan-generation capability. All completed objects and
capabilities here are process-local, nonserializable, noncopyable, and
nonidentified.

For an admitted Plan and one `Accept` terminal `t`, the static continuation arm
contains every and only derived export whose source is either:

- a decision site guaranteed active and ordered before `t` under the exact
  scope/guard laws; or
- the accepted-terminal recipe keyed by `t`.

Exports owned by another terminal and conditionally active decision exports
not guaranteed on `t`'s path are absent from that arm. The disposition is:

```text
AcceptedPlanContinuationDisposition =
    NoAcceptedPlanContinuation
  | PendingAcceptedPlanContinuation(
      terminal: TerminalRef,
      right: AcceptedPlanContinuationRight)
```

The pending arm is formed if and only if the reached terminal is `Accept` and
its exact continuation arm is nonempty. The right is linear and one-use.
`CompleteAcceptedPlanContinuation` consumes it at entry, reads decision-site
values only from the sealed adapter trace, evaluates only the missing
terminal-recipe closure against `final_plan_state`, and then issues the complete
terminal-indexed arm atomically. ProtoStar and LatticeFold+ arms can therefore
contain only retained decision-site exports; Nova and HyperNova arms contain
terminal-derived exports; CycleFold's arm contains its retained primary
decision export plus its terminal-derived companion export.

Success issues every and only output in the active arm. Any qualified failure
issues none of that arm, even when all decision values were already retained
internally. Inactive terminal arms have no runtime value, no empty tuple
surrogate, and no access authority. A reached `Accept` terminal with an empty
arm carries `NoAcceptedPlanContinuation`; invoking completion without the
identical pending right is `Refused`.

`CompletedPlanContinuation` contains private process-local values and a fresh
noncopyable `CausalPlanContinuationCapability`. Neither has a semantic ID. The
capability retains the exact Plan-generation capability, reached terminal,
selected static arm, evaluator, limits, and consumed-right occurrence. A
digest, copied tuple, equal record, or Protocol replay cannot recreate it.

### 7.3 Two-plane completion and replay

Continuation completion occurs after Core completion is fixed:

```text
Core Accept + continuation success
  = completed Core run + one complete active continuation arm

Core Accept + continuation noncompletion
  = completed Core run + no issued continuation arm
```

Noncompletion must not rewrite `Accept`, erase the `RunRecord`, or expose a
partial arm. The ordinary `CausalGenerationCapability` attests only to the Core
record. `CausalPlanGenerationCapability` additionally attests to exact Plan
execution; `CausalPlanContinuationCapability` separately attests to atomic arm
issuance.

Preparation failure mints no session. `StrategyStopped` produces a partial Core
record and no continuation. FS interpretation failure has no terminal;
`Reject` and `Abort` select no accepted arm. The lifecycle is
`Prepared/Ready -> Running -> Completed/Closed`, with an optional
`PendingContinuation -> Continued/Closed` subtransition. No state is both
reusable for generation and authoritative for a completed run.

`ReplayRun` remains Protocol replay and never executes Plan recipes or mints a
private export. `RunRecord` intentionally omits private material, randomness,
adapter state, and decision-local values. No cold recomputation operation is
selected. Repeating preparation, generation, and continuation completion is a
fresh occurrence with fresh Plan/Protocol capabilities, even when the new record is
byte-equal to an older record. Two sessions may produce equal records while
holding different private state; the record alone is never authority for a
continuation output or Relations witness grounding.

## 8. Witness surface and Relations

### 8.1 Static surface

`PlanWitnessSurface` gains one exact occurrence class:

```text
PlanWitnessOccurrenceClass =
    SuppliedForGeneration
  | ProducedWhenSourceDecisionActive
  | ProducedWhenAcceptedTerminalReached
```

The public surface entry still contains only role, value type, and occurrence
class. It contains no `ProverPlanId`, terminal ref, local node ref, recipe ref,
runtime value, or private source map. The live
`CheckedPlanWitnessSurfaceExtraction` retains the exact source site and local
value privately.

The deferred public-parameter candidate makes no surface change.

### 8.2 Runtime confidential witness seam

Static surface extraction proves shape, not possession of a concrete private
occurrence. The selected runtime seam closes all three surface classes rather
than inventing a terminal-only authority:

```text
ConfidentialPlanWitnessFamily = "confidential-plan-witness-view"
ConfidentialPlanWitnessQualification = CausallyGeneratedPlanOnly

ConfidentialPlanWitnessReadManifest =
  NonEmptyCanonicalSeq<WitnessSurfaceKey>

ConfidentialPlanWitnessEntry = {
  key: WitnessSurfaceKey,
  role: PlanWitnessRole,
  occurrence_class: PlanWitnessOccurrenceClass,
  value_type: ValueType,
  value: CanonicalValue<value_type>
}

ConfidentialPlanWitnessView = {
  protocol_id: ProtocolId,
  plan_witness_surface_id: PlanWitnessSurfaceId,
  qualification: CausallyGeneratedPlanOnly,
  entries: FiniteSeq<ConfidentialPlanWitnessEntry>
}

ConfidentialPlanWitnessSourceRequirement =
    GeneratedSufficient
  | FinalizedRequired

ConfidentialPlanWitnessDisclosurePolicy = {
  family: ConfidentialPlanWitnessFamily,
  plan_witness_surface_id: PlanWitnessSurfaceId,
  manifest: ConfidentialPlanWitnessReadManifest,
  qualification: CausallyGeneratedPlanOnly,
  source_requirement: ConfidentialPlanWitnessSourceRequirement,
  consumer_id:
    PIRSourceConsumerRoleId(PIRInterfacePlanProfileId,family,consumer),
  purpose_id:
    PIRSourcePurposeRoleId(PIRInterfacePlanProfileId,family,purpose)
}

ConfidentialPlanWitnessDisclosurePolicyId =
  ProfiledSemanticId<"pir.confidential-plan-witness-disclosure-policy">(
    B, PIRInterfacePlanProfileId,
    ConfidentialPlanWitnessDisclosurePolicyBody(policy))

ConfidentialPlanWitnessBindingPayload = {
  family, plan_witness_surface_id, manifest, qualification,
  source_requirement, disclosure_policy_id, consumer_id, purpose_id,
  result_schema: "whole-confidential-plan-witness-selection-v1"
}

ConfidentialPlanWitnessCapabilityRequirement = {
  family, binding_payload_id, disclosure_policy_id,
  consumer_id, purpose_id, source_requirement,
  bearer_law:
    "fresh-identical-plan-generation-and-required-continuation-bearers"
}

ConfidentialPlanWitnessPolicyClosure = {
  family, binding_payload_id, disclosure_policy_id,
  capability_requirement_id
}

ConfidentialPlanWitnessBindingPayloadId =
  ProfiledSemanticId<"pir.source-binding-payload">(
    B, PIRInterfacePlanProfileId,
    ConfidentialPlanWitnessBindingPayloadBody(payload))
ConfidentialPlanWitnessCapabilityRequirementId =
  ProfiledSemanticId<"pir.source-capability-requirement">(
    B, PIRInterfacePlanProfileId,
    ConfidentialPlanWitnessCapabilityRequirementBody(requirement))
ConfidentialPlanWitnessPolicyClosureId =
  ProfiledSemanticId<"pir.source-policy-closure">(
    B, PIRInterfacePlanProfileId,
    ConfidentialPlanWitnessPolicyClosureBody(closure))

ConfidentialPlanWitnessViewSource =
    Generated(exact CompletedPlanRun G,
              identical live CausalPlanGenerationCapability)
  | Finalized(exact CompletedPlanContinuation C,
              identical live CausalPlanContinuationCapability)

IssueConfidentialPlanWitnessView(
  exact ConfidentialPlanWitnessViewSource source,
  exact PlanWitnessSurface,
  identical live CheckedPlanWitnessSurfaceExtraction,
  exact ConfidentialPlanWitnessReadManifest,
  exact consumer and purpose,
  exact ConfidentialPlanWitnessDisclosurePolicyId,
  exact admitted binding payload, capability requirement, and policy closure,
  exact Foundation operation-policy disposition and capability-requirement
    wrapper derived from those artifacts)
    -> Affirmative({
         view: ConfidentialPlanWitnessView,
         authority: CheckedConfidentialPlanWitnessViewAuthority,
         capability: ConfidentialPlanWitnessViewCapability
       })
     | Unsupported | MissingDependency | CannotAnswer | KindMismatch
     | Malformed | Refused | DeterministicLimitExceeded | CheckerFailure
```

The manifest is the nonempty canonical sorted-unique sequence of selected
surface keys; caller order never enters its body. Policy admission
derives `source_requirement` from their admitted occurrence classes and
refuses a claimed `GeneratedSufficient` policy when any selected key is
terminal-produced. `Generated` is admissible only when every selected occurrence is
available from generation. `Finalized` retains its underlying completed run
and is required when any selected occurrence is terminal-produced. For a
`SuppliedForGeneration` key, issuance reads the exact private-material
occurrence retained by the source run's prepared session. For a
`ProducedWhenSourceDecisionActive` key, it requires that exact decision to be
active in the source run record and reads the local value retained by
`CausalPlanGenerationCapability`. For a
`ProducedWhenAcceptedTerminalReached` key, it additionally requires the exact
matching `Finalized` source and reads the value from the atomically issued
active terminal arm. A `Finalized` source may also disclose selected
generation-time occurrences; it does not create a second occurrence for them.

The view is immutable, process-local, nonserializable, purpose-bound, and has
no semantic ID. `CheckedConfidentialPlanWitnessViewAuthority` is exactly a
Foundation `OwnerLocalSourceAuthorityBinding`: owner `"pir"`, family
`ConfidentialPlanWitnessFamily`, local coordinate the identical issued view,
exact payload and policy-closure IDs, operation policy
`BoundTo(ConfidentialPlanWitnessDisclosurePolicyId)`, and capability
requirement wrapping the exact requirement ID. It has no canonical body or
content ID.

The fresh `ConfidentialPlanWitnessViewCapability` retains the complete view,
that authority, manifest, Plan and surface extraction, exact completed run,
generation authority, required continuation authority, consumer, purpose,
policy artifacts, issuance occurrence, lifetime, and process generation. A
missing or expired otherwise matching live source is `CannotAnswer`; a wrong
source, session, consumer, purpose, policy, or source-requirement arm is
`Refused`; duplicate, reordered, extra, or unrequested entries are
`Malformed`. No nonaffirmative branch exposes a partial view. The policy,
payload, requirement, closure, and their IDs contain no private value,
private-derived digest, run-record digest, or runtime occurrence ID.

An equal private value, copied tuple, serialized digest, Protocol replay, or
fresh byte-equal generation cannot issue a view for a historical occurrence.

### 8.3 Relations consequences

The static `PlanWitnessBinding` body need not gain a Plan ID or terminal ref.
It accepts the new occurrence class and remains a mapping between one
source-ID-free Plan surface and relation witness occurrences.

Relations already owns the closed `CorrespondenceQuestion` and
`CheckedCorrespondence` families. The promotion adds one arm to that family;
it does not create a twenty-fourth semantic-subject kind or a parallel checked
result algebra:

```text
PlanWitnessEdgeRef =
  dense ordinal into one exact PlanWitnessBinding.witness_edges

CorrespondenceQuestion +=
  PlanWitnessRunGrounding {
    plan_binding_id: PlanWitnessBindingId,
    instance_id: RelationInstanceId,
    edges: NonEmptyCanonicalSortedUniqueSeq<PlanWitnessEdgeRef>
  }

CorrespondenceQuestionBody[PlanWitnessRunGrounding](q) =
  V(13,R{
    0:ContentRef(q.plan_binding_id),
    1:ContentRef(q.instance_id),
    2:S[N(edge)... in canonical increasing order]
  })

CorrespondenceReadManifest += {
  confidential_plan_witness:
    Option<ConfidentialPlanWitnessSelection>
}

CheckPlanWitnessRunGrounding(
  exact admitted PlanWitnessRunGrounding q,
  exact admitted PlanWitnessBinding,
  exact admitted RelationInstance,
  exact fresh PrivateWitnessAssignment and secret-value capability issued
    through IssuePrivateWitnessFieldSource,
  exact ConfidentialPlanWitnessView,
  exact CheckedConfidentialPlanWitnessViewAuthority and identical live
    ConfidentialPlanWitnessViewCapability purpose-bound to
    CorrespondenceQuestionId(q),
  exact bridge/loss-premise inputs and
    CheckLossyUseAtConsumerSource joins required by q's selected edges,
  exact admitted evaluator and deterministic limits)
    -> Qualified<CheckedCorrespondence>
```

Question admission authenticates both IDs under one exact Relations profile
and regime, resolves every edge in range, rejects empty, duplicate,
or non-increasing edge sequences, and requires every edge's relation endpoint
to belong to the exact instance Interface. It derives the complete surface-
key manifest, relation-witness selector, value type, admitted value-relation
law, bridge, and exact-used dependency closure for every edge. Missing bridge,
value-relation, type, or evaluator preimages are `MissingDependency`; wrong
profile or kind is `KindMismatch`; bad canonical shape is `Malformed`; formed
cross-binding/cross-instance references are `Refused`; and derivation runs
under the exact Relations deterministic limits. The admitted body contains no
private value, occurrence, capability, run record, qualification selector, or
caller predicate. Causal Plan generation is a fixed law of this arm rather
than a caller-selectable qualification.

The question derives one edge descriptor and relation-witness selector for
each binding edge. `ManifestFor(q)` fills the new optional confidential Plan-
witness selection with the nonempty canonical sorted-unique surface-key set;
the field is `None` for every other question arm. Multiple selectors over one
structured surface value do not duplicate the private owner read. The
operation checks:

1. the surface entry and binding edge are exact;
2. the fresh relation-secret assignment belongs to the exact instance and
   supplies the selected relation witness occurrence;
3. the Plan value comes from the exact causally generated occurrence class,
   with accepted-terminal values additionally requiring atomic continuation
   completion;
4. the edge's admitted value relation holds at the two selected occurrences;
   and
5. any lossy bridge uses its exact question-bound premise and consumer-source
   authority.

A true edge records existing `ValueAgrees(Edge(e))`; a completed false value
relation records existing `ValueDisagreement(Edge(e))` and is semantic
Negative. Missing, inactive, unfinalized, or expired required live sources are
`CannotAnswer`; a cross-run, cross-Plan, cross-surface, wrong-policy, wrong-
consumer, or wrong-purpose source is `Refused`; wrong kind or type is
`KindMismatch`; duplicate, partial, or extra manifests are `Malformed`; and a
replay-qualified rather than causally generated source is `Unsupported`. No
such failure becomes value disagreement. Any public occurrence is checked by
a separate public `RunGrounding` question, not by equal-value inference inside
this private arm.

The ordinary affirmative `CheckedCorrespondence` capability retains the exact
admitted question, binding, instance, secret assignment and capability,
confidential view/authority/capability, bridge inputs, source Plan run, and
Plan/Protocol causal authorities. This permits one further owner-local join without
placing secret or runtime material in the question ID.

```text
JoinPlanWitnessAndPublicRunGrounding(
  exact affirmative CheckedCorrespondence private_result for an admitted
    PlanWitnessRunGrounding question,
  identical live private checked-result capability,
  exact affirmative CheckedCorrespondence public_result for an admitted
    public RunGrounding question requiring causal qualification,
  identical live public checked-result and RelationRunView capabilities)
    -> Qualified<Affirmative({
         result: CheckedSameRunPlanWitnessCorrespondence,
         capability: CheckedSameRunPlanWitnessCorrespondenceCapability
       })>
     | CannotAnswer | KindMismatch | Malformed | Refused | CheckerFailure
```

This composite operation independently checks that both checked results retain
the identical admitted `RelationInstance`, `ProtocolId`, live
`CoreInvocation` object, live `CompletedProtocolRecord` object, and identical
live Protocol `CausalGenerationCapability` nested inside the private Plan-generation
bearer and the public view authority. It does not impose a generic notion of
the "intended fold output"; each public and private question already fixes its
own exact coordinates. Equal record bytes, equal values, replay-qualified
public views, fresh byte-equal generations, and two causal records with equal
encodings do not join. An expired otherwise matching bearer is
`CannotAnswer`; a live but different instance, run, invocation, or generation
is `Refused`.

This establishes a same-run occurrence bridge, not witness satisfaction or
fold preservation. Cross-run recurrence uses a separate Plan-owned one-use
handoff. For one exact accepted continuation output and one exact unfilled
`WitnessIngress` of a prepared target Plan session:

```text
IssueAcceptedPlanWitnessIngressSupply(
  exact finalized source Plan session and accepted continuation arm,
  exact unspent source PlanContinuationOutputRef,
  identical live continuation output capability,
  exact prepared target Plan session and unfilled WitnessIngress ref,
  identical live target-ingress preparation capability)
    -> Qualified<Affirmative({
         supply: ReadyPlanWitnessIngressSupply,
         supply_capability: ReadyPlanWitnessIngressSupplyCapability,
         handoff_capability: CausalPlanWitnessHandoffCapability
       })>
     | CannotAnswer | KindMismatch | Malformed | Refused | CheckerFailure
```

Issuance checks exact value type and target slot, consumes both the source
output right and target empty-ingress right, supplies the value to one fresh
target occurrence, and atomically returns the ready target supply. It cannot
split an accepted-terminal arm, duplicate one output into two ingresses, or
reuse an equal-valued output. A failed issue consumes neither side and exposes
no value. Successful issuance is one-use: the ready supply can prepare exactly
one target generation and the handoff capability can authorize exactly one
private correspondence join.

The private recurrence fact is then formed without a new question tag:

```text
JoinCausalPlanWitnessHandoff(
  exact affirmative source-output PlanWitnessRunGrounding result,
  exact affirmative target-input PlanWitnessRunGrounding result,
  identical live checked-result capabilities,
  exact CausalPlanWitnessHandoffCapability)
    -> Qualified<Affirmative({
         result: CheckedPlanWitnessHandoffCorrespondence,
         capability: CheckedPlanWitnessHandoffCorrespondenceCapability
       })>
     | CannotAnswer | KindMismatch | Malformed | Refused | CheckerFailure
```

It requires the source and target private occurrences retained by the handoff
capability, not merely equal values. Independently, one affirmative public
`EquationGrounding` uses exactly two `ExactCausallyGenerated` run slots and
retains the exact source and target run objects and `RelationInstance`
operands. The final conjunction is:

```text
JoinCausalPlanStepRecurrence(
  exact affirmative public EquationGrounding result and live capability,
  exact affirmative CheckedPlanWitnessHandoffCorrespondence and live
    capability)
    -> Qualified<Affirmative({
         result: CheckedCausalPlanStepRecurrence,
         capability: CheckedCausalPlanStepRecurrenceCapability
       })>
     | CannotAnswer | KindMismatch | Malformed | Refused | CheckerFailure
```

The join requires identical source/target runs and relation instances across
the public and private lanes. These supplies, results, and capabilities are
nonidentified, process-local runtime objects. They establish exact causal
recurrence for one adjacent pair only; `RelationRefinement`, satisfaction,
fold preservation, completeness, knowledge, and finite-family IVC induction
remain separate questions.

This direct semantic handoff does not claim serialization, persistence,
network delivery, restart recovery, or buffer provenance. Realization may
record those operational facts, but a codec or transport receipt cannot mint,
reconstruct, or substitute for any live Plan handoff capability. A serialized
value may still be admitted later as an ordinary independently supplied input;
that path has value validity but not this direct causal-handoff proposition.

No Relations subject obtains a direct Plan-authority edge. The Plan still
cites no Relations ID, and the source-ID-free surface preserves the directional
cut. The new `CorrespondenceQuestion` arm rotates that existing body and the
Relations profile, but the semantic-subject catalog remains at twenty-three
kinds. Every Relations ID under the shared profile and every Analysis subject
that imports it rotates transitively. The composite checked result is process-
local and nonidentified; its schema rotates with that profile but adds no
further semantic root.

## 9. Endpoint and OIR consequences

### 9.1 Purpose separation

The current bounded Plan-specialized Prover endpoint is rooted only at public
Prover moves and state updates. It deliberately excludes derived witness
exports and declares `NoSourceSemanticCompletion`. It therefore cannot claim
to produce a private continuation.

Retain that minimal proof-message purpose and add a distinct purpose when an
endpoint must produce a private continuation:

```text
PlanSpecializedProverEndpoint(mode)
  -> public proof-message and ordinary decision behavior only

PlanContinuationProverEndpoint(mode)
  -> the same behavior plus one accepted-terminal-indexed private
     continuation arm
```

This purpose split prevents every proof-producing endpoint from inheriting
private-output retention and continuation-completion failure surface. The
continuation purpose is not synonymous with “terminal-derived”: its active arm
may include retained decision-site exports, accepted-terminal exports, or both.
This gives ProtoStar and LatticeFold+ the same endpoint purpose as Nova,
HyperNova, and CycleFold without inventing a post-terminal dependency for
values produced earlier.

The private continuation is not an Interface transport or external verifier
completion. `NoSourceSemanticCompletion` is an endpoint-contract term, not an
Interface term, and remains true for both Prover purposes. The continuation
purpose adds a separate internal/private Plan-output contract rather than
misclassifying the continuation as external Protocol completion.

### 9.2 Source-view graph

For a purpose that reaches them, the Plan quotient expands from six tables to:

```text
ReachablePlanGraph = {
  private_material,
  randomness,
  state,
  site_qualified_recipe_nodes,
  decision_moves,
  decision_updates,
  site_qualified_derived_exports
}

PlanContinuationOutputRef =
  dense ordinal into the continuation graph's canonical
  site_qualified_derived_exports table

PlanContinuationOutputDecl = {
  output_ref: PlanContinuationOutputRef,
  source_site: PlanRecipeSiteRef,
  value_type: ValueType
}

AcceptedPlanContinuationArmDecl = {
  accepted_terminal_site: TerminalRef,
  outputs: NonEmptyCanonicalSeq<PlanContinuationOutputDecl>
}

PrivatePlanContinuationContract =
  CanonicalMap<TerminalRef, AcceptedPlanContinuationArmDecl>
```

Reachability for the ordinary Plan-specialized purpose still starts at moves
and state replacements. Reachability for the continuation purpose additionally
starts at every export referenced by at least one accepted-terminal arm, then
closes over its exact site-local nodes, public reads, private material,
randomness, and state dependencies.

For each admitted `Accept` terminal `t`, its arm contains every and only:

1. decision-derived export whose source decision is guaranteed active and
   ordered before `t` under the exact scope/guard laws; and
2. accepted-terminal-derived export whose source site is exactly `t`.

An arm is omitted when that set is empty. A decision export guaranteed before
multiple accepted terminals may be referenced by multiple arms using the same
graph-local output ref. A terminal export may occur only in its own arm.
Conditionally active decision exports not guaranteed on a terminal path remain
available through the confidential Plan-witness seam but are not falsely
promised by that terminal's endpoint arm.

Witness-surface keys remain source provenance and are rebased/excluded. Each
retained export receives one `PlanContinuationOutputRef`; its graph entry keeps
the exact decision-or-terminal source site, local recipe value, and output
type. Exact algorithms/evaluations, public-read coordinates, state
dependencies, terminal refs, and output refs/types remain semantic graph data.
Equal values or equal types never collapse distinct refs.

### 9.3 OIR contract

The OIR Plan graph needs corresponding site-qualified node, export, and
terminal-arm tables. Private continuation outputs use a dedicated namespace:

```text
PrivatePlanContinuationAccess =
  PlanContinuationOutput(PlanContinuationOutputRef)
```

`PrivatePlanContinuationAccess` is legal only inside the private continuation
contract. It is not an `EndpointValueRef`, Protocol value ref, ABI value ref, public
closure ref, or ordinary Plan-move ref, so a private output cannot leak into a
public endpoint position by reusing a generic tag.

The derived `PrivatePlanContinuationContract` names every output by graph-local
ref, source site, type, and accepted-terminal arm membership; it contains no
runtime value. Local admission resolves each selector to exactly one export,
checks every arm key and declaration, proves the decision-path guarantee or
same-terminal ownership, and rejects duplicate, dangling, cross-graph,
wrong-site, wrong-type, extra, or missing arm members. Source-read derivation,
exact-use checking, and contract formation all use that same ref. No
`(terminal,type)` or value-equality lookup is permitted.

Promotion changes every exact carrier that currently assumes decision-only
Plan nodes:

1. `EndpointProjectionPurpose` and `EndpointPurposeBody` gain
   `PlanContinuationProverEndpoint(ChallengeMode)`;
2. source Plan graph bodies, node refs, and export refs become site-qualified;
3. `AlgorithmUseSiteBody` gains a site-qualified Plan-recipe-node arm;
4. a dedicated `PrivatePlanContinuationAccessBody` names private outputs and
   is illegal in every generic endpoint/Protocol/ABI/public position;
5. local OIR admission, source-read, exact-use, and path-guarantee laws cover
   those new paths and add one `PlanContinuation(terminal_ref)` static
   obligation per retained arm; and
6. `DerivedEndpointContractBody` gains the terminal-indexed private Plan
   continuation contract field,
   while its external completion field remains
   `NoSourceSemanticCompletion`.

The private contract is `None` for the ordinary purpose. For the continuation
purpose it carries every and only nonempty accepted-terminal arm in terminal
order and every arm's declarations in output-ref order. Each static
`PlanContinuation(t)` obligation rechecks Accept gating, the sealed final-state
source, exact export-rooted terminal evaluation, decision-path guarantees, and
atomic all-or-nothing membership for `t`.

This OIR selection is static only. Runtime issuance remains the PIR Plan
operation `CompleteAcceptedPlanContinuation`: only the reached accepted
terminal's arm is active; all other arms are absent, not empty tuples. That
operation obtains decision-derived values from the sealed generation trace,
evaluates only missing terminal nodes, and atomically issues the entire active
arm. Failure issues no arm. OIR does not consume the live continuation
capability or claim runtime projection until a later Realization design
activates that boundary.

An ordinary proof-message endpoint may exclude private-export-only nodes and
exports and therefore share one source-independent graph meaning with another
Plan that differs only in those inert facts. A continuation endpoint may not.

Until the expanded endpoint/OIR bodies and durable static projection law are
promoted in the same dependency checkpoint, the old profile must fail the
profile/law join before classification because it cannot authenticate the new
Plan grammar. The Foundation semantic regime itself does not rotate. Under the
rotated profile, the revised bounded projection
classifier must either support the selected purpose completely or return typed
`Unsupported`; it must never silently erase a reachable new feature.

## 10. Exact canonical-body delta

The selected conceptual body order is:

```text
PlanRecipeSiteRefBody =
    V(0,N(decision_ref))
  | V(1,N(accept_terminal_ref))

PlanReadCoordinateBody = V(0,N(constant_ref))
  | V(1,N(public_input_ref))
  | V(2,N(binding_ref))
  | V(3,N(message_occurrence))
  | V(4,N(challenge_occurrence))
  | V(5,N(oracle_publication_occurrence))
  | V(6,N(oracle_query_occurrence))
  | V(7,N(oracle_answer_occurrence))
  | V(8,R{0:N(module_occurrence),1:N(observation_ordinal)})
  | V(9,N(prior_decision_ref))
  | V(10,N(accepted_terminal_public_output_ordinal))

RecipeOperandBody =
    V(0,PlanReadCoordinateBody)
  | V(1,N(private_material_ref))
  | V(2,N(randomness_requirement_ref))
  | V(3,N(state_slot_ref))
  | V(4,typed_constant_body)
  | V(5,N(local_node_ref))

AcceptedTerminalRecipeBody(x) =
  R{0:S[RecipeNodeBody(node)...]}

DerivedWitnessExportBody(x) =
  R{0:Q(x.key),1:PlanRecipeSiteRefBody(x.source_site),
    2:RecipeOperandBody(x.value),3:VT(x.value_type)}

ProverPlanBody(P) = R{
  0:ContentRef(P.protocol_id),
  1:S[PrivateMaterialBody(x)...],
  2:S[RandomnessRequirementBody(x)...],
  3:S[StrategyStateSlotBody(x)...],
  4:S[R{0:N(decision_ref),1:DecisionRecipeBody(recipe)}...
      in ProverDecisionPointRef order],
  5:S[DerivedWitnessExportBody(x)...],
  6:S[R{0:N(terminal_ref),1:AcceptedTerminalRecipeBody(recipe)}...
      in TerminalRef order]
}

PlanWitnessOccurrenceClassBody =
    V(0,Unit)
  | V(1,Unit)
  | V(2,Unit)
// SuppliedForGeneration | ProducedWhenSourceDecisionActive |
// ProducedWhenAcceptedTerminalReached

ConfidentialPlanWitnessReadManifestBody(x) =
  S[Q(witness_surface_key)... in canonical sorted-unique key order]

ConfidentialPlanWitnessSourceRequirementBody =
  V(0,Unit) | V(1,Unit)
// GeneratedSufficient | FinalizedRequired

ConfidentialPlanWitnessDisclosurePolicyBody(x) = R{
  0:Q("confidential-plan-witness-view"),
  1:ContentRef(x.plan_witness_surface_id),
  2:ConfidentialPlanWitnessReadManifestBody(x.manifest),
  3:V(0,Unit), // CausallyGeneratedPlanOnly
  4:ConfidentialPlanWitnessSourceRequirementBody(x.source_requirement),
  5:ContentRef(x.consumer_id),
  6:ContentRef(x.purpose_id)
}

ConfidentialPlanWitnessBindingPayloadBody(x) = R{
  0:Q("confidential-plan-witness-view"),
  1:ContentRef(x.plan_witness_surface_id),
  2:ConfidentialPlanWitnessReadManifestBody(x.manifest),
  3:V(0,Unit), // CausallyGeneratedPlanOnly
  4:ConfidentialPlanWitnessSourceRequirementBody(x.source_requirement),
  5:ContentRef(x.disclosure_policy_id),
  6:ContentRef(x.consumer_id),
  7:ContentRef(x.purpose_id),
  8:Q("whole-confidential-plan-witness-selection-v1")
}

ConfidentialPlanWitnessCapabilityRequirementBody(x) = R{
  0:Q("confidential-plan-witness-view"),
  1:ContentRef(x.binding_payload_id),
  2:ContentRef(x.disclosure_policy_id),
  3:ContentRef(x.consumer_id),
  4:ContentRef(x.purpose_id),
  5:ConfidentialPlanWitnessSourceRequirementBody(x.source_requirement),
  6:Q("fresh-identical-plan-generation-and-required-continuation-bearers")
}

ConfidentialPlanWitnessPolicyClosureBody(x) = R{
  0:Q("confidential-plan-witness-view"),
  1:ContentRef(x.binding_payload_id),
  2:ContentRef(x.disclosure_policy_id),
  3:ContentRef(x.capability_requirement_id)
}

CorrespondenceQuestionBody[PlanWitnessRunGrounding](q) =
  V(13,R{
    0:ContentRef(q.plan_binding_id),
    1:ContentRef(q.instance_id),
    2:S[N(edge)... in canonical increasing order]
  })

PlanRecipeNodeSiteBody =
    V(0,N(decision_spine_ref))
  | V(1,N(accepted_terminal_ref))

PlanContinuationOutputDeclBody(x) = R{
  0:N(x.output_ref),
  1:PlanRecipeNodeSiteBody(x.source_site),
  2:VT(x.value_type)
}
AcceptedPlanContinuationArmDeclBody(x) = R{
  0:N(x.accepted_terminal_site),
  1:S[PlanContinuationOutputDeclBody(output)... in output-ref order]
}
PrivatePlanContinuationContractBody(x) =
  S[AcceptedPlanContinuationArmDeclBody(arm)... in terminal-ref order]

EndpointPurposeBody +=
  V(3,ChallengeModeBody) // PlanContinuationProverEndpoint

AlgorithmUseSiteBody[V9] =
  V(9,R{0:PlanRecipeNodeSiteBody,1:N(plan_recipe_node_ref)})

PlanGraphRecipeNodeBody(x) = R{
  0:PlanRecipeNodeSiteBody(x.site),
  1:N(x.algorithm_dependency),
  2:N(x.evaluation_dependency),
  3:S[PlanValueRefBody(input)...],
  4:N(x.result_type_ref)
}

PlanGraphDerivedExportBody(x) = R{
  0:PlanRecipeNodeSiteBody(x.source_site),
  1:PlanValueRefBody(x.value),
  2:N(x.result_type_ref)
}

PlanGraphBody(x) = R{
  0:S[PlanPrivateMaterialBody...],
  1:S[PlanRandomnessBody...],
  2:S[PlanStateBody...],
  3:S[PlanGraphRecipeNodeBody... in site/within-site order],
  4:S[PlanMoveEntryBody...],
  5:S[PlanUpdateBody...],
  6:S[PlanGraphDerivedExportBody... in output-ref order]
}

PrivatePlanContinuationAccessBody =
  V(0,N(plan_continuation_output_ref))
// PlanContinuationOutput; legal only in PrivatePlanContinuationContract

DerivedEndpointContractBody(x) = R{
  0:S[EndpointStaticObligationBody... in full-body byte order],
  1:S[OirRequirementBody... in full-body byte order],
  2:EndpointCompletionInterfaceBody(x.completion_interface),
  3:OptionBody(
      x.private_plan_continuation,
      PrivatePlanContinuationContractBody)
}
```

This is a proposed exact delta, not a durable Appendix-A definition. Promotion
must splice these tags and fields into the complete owner bodies, preserve
their existing bounds, and update dependency catalogs without leaving a
prose-defined remainder. In particular, V9 replaces the old decision-only
Plan-recipe-node payload rather than creating two meanings for V9. The private
access body has its own namespace and never becomes an
`EndpointValueRefBody` arm. No public-parameter body, operand, graph table, or
OIR requirement appears in this selected delta.

## 11. Dependency rotation

The accepted-terminal addition and its complete continuation-output
consequences must land in one dependency-complete rotation. The deferred public
parameter candidate is absent from this rotation.

| Owner/profile or subject | Consequence |
|---|---|
| `PIRInterfacePlanProfileId` | rotates because Plan grammar, bodies, admission, extraction, and `PlanRealizes` change |
| `ProtocolInterfaceId` | rotates through its directly selected Interface/Plan profile even when its body is unchanged |
| `ProverPlanId` | rotates; new bodies and laws |
| `PlanWitnessSurfaceId` | rotates; occurrence-class and extraction law change |
| Plan execution/result schemas | rotate with the exact adapter and linear ready/running/completed/continuation lifecycle; their live capabilities remain nonidentified |
| confidential Plan-witness policy subjects | the disclosure-policy, binding-payload, capability-requirement, and policy-closure IDs rotate with `PIRInterfacePlanProfileId`; checked view authority/capability schemas rotate but remain nonidentified |
| endpoint source-view and read-manifest profiles | rotate; new Plan fields, purpose, selectors, and graph tables |
| endpoint purpose, graph, and private-output contract bodies | rotate through the continuation purpose, site-qualified node/export carriers, terminal-indexed arms, and exact output refs |
| OIR endpoint graph profile and `OirId` | rotate; imported Plan profile and graph/requirement/contract grammar change |
| OIR projection and validation profiles/results | rotate transitively |
| Relations semantic-subject catalog/profile and Plan-witness subjects | the catalog remains twenty-three kinds; the shared profile and all subjects rotate through the imported Interface/Plan profile, new occurrence class, confidential-view intake, and the new `PlanWitnessRunGrounding` arm of `relations.correspondence-question` |
| Plan-witness run-grounding checked-result and same-run join schemas | reuse `CheckedCorrespondence`; its capability and the nonidentified same-run join schema rotate with Relations |
| correspondence-question and Analysis profiles/subjects | rotate through the new `PlanWitnessRunGrounding` arm and any consumer of the same-run composite |
| realization/deployment identities over changed OIR | rotate transitively when formed |

`PIRInteractionProfileId`, `CoreId`, `ProtocolId`, `CoreInvocationId`, and the
Fiat--Shamir construction profiles do not rotate merely because this Plan
extension is selected. The accepted-terminal read predicate consumes existing
Protocol owner views rather than changing Core body or challenge interpretation,
and the Plan-owned one-use wrapper supplies its exact adapter to unchanged
`GenerateRun`, then retains the returned record and Protocol causal capability. This
no-rotation conclusion depends on that wrapper boundary: moving the adapter
state, lifecycle right, private values, or continuation operation into Protocol
would invalidate it.

If promotion instead adds a new Protocol-identified view or changes Protocol visibility,
that is a separate, broader semantic change and must disclose its additional
identity cascade. It is not needed for the selected candidate.

## 12. Failure and falsification matrix

| Mutation or event | Required result |
|---|---|
| call generation twice with one prepared session | second call lacks the consumed ready capability and refuses |
| caller substitutes an arbitrary Protocol strategy capability | impossible through the wrapper signature or `Refused`; only the enclosed Plan adapter may be passed |
| adapter skips a recipe node, constructs a different move, or supplies a partial state map | `StrategyStopped` with qualified Plan cause; no Plan-generation capability |
| consume one randomness bearer twice or before its declared availability boundary | adapter stop; no partial move, state, or decision export |
| resolve terminal `StateBefore` from initial state, mutable caller state, or `RunRecord` | `Refused`; only sealed `final_plan_state` is admissible |
| run completion recipe on canonical-FS interpretation failure | impossible: no terminal |
| run it on `Reject` or `Abort` | refused by exact terminal-verdict law |
| guarded terminal reads a conditionally absent message/challenge | Negative `SiteReadDisagreement` |
| completion node captures a decision-local node ordinal | Plan nonadmission or exact site-reference refusal |
| terminal recipe has no export, an export has no recipe, or a node is export-dead | Plan nonadmission; never a runtime/OIR discrepancy |
| move an equal recipe body to another terminal | `ProverPlanId` changes because the map key is encoded |
| direct re-read of erased decision randomness at terminal | operand availability failure; use retained state |
| completion recipe emits a unit Prover message | Plan nonadmission; terminal recipes have no move arm |
| completion recipe updates persistent state | Plan nonadmission; export and next-ingress are required |
| classify CycleFold's primary witness as depending on `rho_star` | source-dependency mismatch; primary remains a retained post-`rho` decision export |
| omit a guaranteed decision export from an accepted-terminal arm, add a non-guaranteed one, or place a terminal export in another arm | endpoint/OIR contract nonadmission |
| one active-arm export succeeds before a later terminal node exhausts its bound | no partial output; atomic continuation noncompletion |
| continuation completion fails after Core `Accept` | Core record remains accepted; no issued continuation arm |
| retry or duplicate continuation completion for one completed run | consumed continuation right refuses; no second private occurrence |
| join a prepared session to a run generated by another strategy/session | `Refused`; no `CausalPlanGenerationCapability` |
| Protocol replay attempts to mint private output authority | refused; replay lacks Plan session and causality |
| equal RunRecords carry different private state | distinct Plan outputs/sessions; no record-based collapse |
| equal-valued exports arise at two Accept terminals | distinct source-site occurrences |
| Relations grounds completion export from `RunRecord` alone | missing confidential Plan-output authority |
| an otherwise matching confidential source capability is expired | `CannotAnswer`, never false correspondence |
| disclose a terminal export under a generation-only policy | policy/source-requirement mismatch; `Refused` with no partial view |
| join equal public/private values from different causal runs | same-run join `Refused`; byte equality grants no occurrence claim |
| issue one accepted output into two target ingresses or reuse one consumed target ingress | second issue `Refused`; no duplicate ready supply or handoff capability |
| join equal-valued source and target private occurrences without the exact live handoff capability | `Refused`; value equality does not establish causal supply |
| use a codec, storage, or transport receipt as a handoff capability | `KindMismatch` or `Refused`; Realization provenance does not mint semantic Plan authority |
| public recurrence equation uses a replay-qualified slot, omits either exact run object, or changes a relation instance | EquationGrounding nonaffirmative; both slots must be `ExactCausallyGenerated` |
| final recurrence join combines public and private lanes for different source or target runs | `Refused`; no `CheckedCausalPlanStepRecurrence` |
| ordinary proof endpoint claims a private continuation | typed `Unsupported` or wrong endpoint purpose |
| project an inactive terminal arm | no value and no authority; `CannotAnswer` or `Refused`, never an empty-tuple substitute |
| swap two same-type outputs in an OIR arm or projection | exact output-ref mismatch; nonadmission or `Refused`, never silent aliasing |
| old profile authenticates new Plan tags | profile/law mismatch; never reinterpret bytes, while the Foundation semantic regime remains unchanged |

These mutations are the bounded falsification set for durable promotion. They
test authority and lifecycle, not only algebraic correctness.

## 13. Promotion verdict and remaining work

The research-contract promotion threshold is met in principle:

- Nova and HyperNova require terminal-scoped private derivation, while
  CycleFold independently requires it for the companion witness after
  `rho_star`; its primary witness remains decision-derived after `rho`;
- the public Plan parameter idea is explicitly deferred because PLONK,
  Groth16, and the folding cases retain native Core-parameter or Plan-constant
  controls and therefore do not meet the frozen promotion rule;
- the candidate has explicit identity, admission, execution, replay, failure,
  endpoint, OIR, and Relations consequences; and
- broader alternatives introduce source changes, authority cycles, or
  unnecessary universal roots.

The selection-time dependency-complete promotion checklist was:

1. `pir/interfaces-and-plans.md`, including exact bodies and
   `PlanWitnessSurface`;
2. the endpoint source-view purpose, selectors, graph, and classifier;
3. the OIR graph, purpose-specific terminal-indexed continuation contract, and
   projection law;
4. Relations profile imports, occurrence class, causal private-output grounding
   intake, the two-slot public `EquationGrounding`, and the two nonidentified
   recurrence joins;
5. the runtime Plan adapter/session/continuation boundary and Plan-owned
   one-use ingress supply, without altering generic Protocol replay; and
6. profile IDs, fixtures, negative cases, inventories, and status.

The semantic laws in items 1--5 are now absorbed by their durable PIR,
Relations, and OIR owners. The bounded evaluator exercises the selected
strategy, continuation, source-occurrence, handoff, recurrence, replay, and
projection boundaries, and the package inventories/status now record that
scope. Item 6 remains deliberately split: complete owner-profile preimages and
independently reconstructible typed profile IDs are still unpublished, and
holdout validation plus independent identity/profile freeze remain open. No
runtime Realization or implementation support follows from durable semantic-
target promotion.

The recursive-import case may still pressure the continuation endpoint, but it
does not reopen the local choice unless it demonstrates that an exact private
continuation arm cannot be represented without changing Core interaction.
Pure verifier-observable Boolean verification remains a Core `Check`; richer
verifier-observable behavior remains a `ModuleEffect`; predicate-embedded
verification remains Relations. LatticeFold+ uses a decision-derived arm and
therefore tests the unified purpose without requiring a terminal recipe.

## 14. Nonclaims

This co-design does not establish:

- implementation or endpoint support for any new Plan feature;
- correctness or termination of a recipe beyond exact Foundation denotation;
- possession, satisfaction, or validity of a derived witness;
- folding or accumulation preservation;
- completeness, soundness, knowledge, extraction, or zero knowledge;
- setup origin, key consistency, generator independence, or ceremony trust;
- source or target Fiat--Shamir theorem applicability;
- IVC/NIVC induction, recursive composition, or decider correctness;
- confidentiality or side-channel protection of concrete runtime state; or
- semantic freeze or migration readiness.
