# Execution, observation and refinement

A complete execution records its outcome, remaining state and ordered events.
A refinement then chooses which parts must agree. Read [execution](#pir-execution)
first and [observation](#observations-and-refinement) next; failure, publication
and cost examples show why a final returned value alone is insufficient.

## PIR execution

**Reading guide:** [Execution](../spec/core/execution.md) owns execution,
call bounds and outer effects; [Observations](../spec/core/observations.md) owns
their observation relations. This page explains their use;
its examples add no requirements. Read [subjects and scope](protocol-model.md) first.
The [Formal correspondence](../spec/correspondence/core.md) records the
declarations and their exact scope.

### 1. Bodies, handlers and complete results

[CORE-01](../spec/core/execution.md#bodies) separates a mathematical
body from its operation handler. A body can branch on replies without choosing
how a provider stores its state. Source formation separately checks captures:
a mathematical continuation may close over information that an admitted
endpoint is not allowed to read. The effect tree is not serialized source.

[CORE-02](../spec/core/execution.md#complete-results) retains outcome,
actual residual state and ordered events. Their distinct roles matter: a
returned value cannot reconstruct provider state; a final state cannot recover
an erased message; an event list alone does not become controller memory.
[Observations](#observations-and-refinement) explains how a judgment selects its view.

### 2. Returned errors, terminal stops and admission

Use [CORE-02](../spec/core/execution.md#outcomes) to choose
the enclosing failure boundary. A session's local rejection can be returned
data when a controller is allowed to try another session. A terminal stop
ends that controller execution. Session tags alone cannot choose between them.

Admission failures occur before this interpreter runs; a runtime guard's
refusal is a separate execution occurrence. A returned verifier decision is
also different from completion of its subsequent continuation. The
[continuation chapter](accepted-continuations.md) explains the separate retained-result
adapter where that distinction is needed.

### 3. Deterministic execution and sequencing

The defining equations are
[CORE-03](../spec/core/execution.md#sequencing),
[CORE-04](../spec/core/execution.md#deterministic-interpretation) and
[CORE-05](../spec/core/execution.md#body-composition).
Their important consequence is that an effectful prefix survives a later stop.
An optimizer uses the whole-result equality or relation required by its
replacement theorem. Returning the same scalar is insufficient when a later
consumer can read different provider state.

Associativity lets an implementation regroup sequencing while preserving
call order. Reordering calls, refunding draws or adding failure cleanup
requires additional operation/adapter laws. The new
[controls](../../formal/Tests/SpecCore.lean) show how a later read distinguishes
prefixes with equal returned values and events but different residual states.

### 4. A concrete failure boundary

Let `write n` update a cell to `n`, emit `n` and return a Boolean reply. Consider:

```text
ok ← write 1
if ok then return true else write 9
```

Two handler interpretations exhibit the difference:

| Handler behavior on each call | Whole execution from state `0` |
|---|---|
| Write and emit, then return `false` | `(returned false, 9, [1, 9])` |
| Write and emit, then stop with `reject` | `(stopped reject, 1, [1])` |

The second execution retains the write and emission from its first call;
it neither runs `write 9` nor restores state `0`. These equalities and the
failure of rollback are checked in [the execution controls](../../formal/Tests/Execution.lean).
Both handlers could satisfy an uninformative postcondition `True`, which
would not make their executions interchangeable.

The exception-shaped alternative, `Except Stop (A × S × List E)`, has no state
or events on its stopping side, so the stopped row would lose a write and an
emission that have already happened. Rolling the state back at a stop would
misreport effects that are already visible outside the execution, and
continuing after a stop would turn a terminal rejection into a recoverable
reply, which is what returned error data expresses. An operation that promises
a transaction states its rollback or compensation in its own contract.

### 5. Finiteness and the public bound

[CORE-07](../spec/core/execution.md#uniform-call-bounds) defines the
separate all-reply bound. Requesting an arbitrary natural `n` and then making
`n` further calls yields a well-founded body with no uniform natural bound.
The existing `well_founded_is_not_uniformly_bounded` theorem in
[Execution controls](../../formal/Tests/Execution.lean) establishes this example.
A frontend can restrict lengths or reject those beyond a declared public bound.

The bound counts reached calls, including one that stops. The
[ExecutionPath](../../formal/Zkc/Semantics/ExecutionPath.lean) theorem
`calls_bounded` connects the syntactic predicate to the actual call records.
A handler that emits three events before stopping still contributes one call.
Its internal work, allocation and native instructions need their own cost law.

`repeatN` elaborates a public number of steps. Its bound and phase-invariant
laws are explained in [interaction composition](composition.md#3-public-repetition-and-call-bounds).
They do not establish native-provider termination by themselves.

Well-foundedness cannot stand in for the bound, and requiring a body to have
finitely many nodes would exclude interfaces whose reply types are infinite
mathematical domains. The consequence for actual calls runs one way: a handler
that stops at once performs a single call even under a body with no uniform
bound, so a small observed count does not establish `Within`.

### 6. Monadic and probabilistic interpretation

[CORE-12](../spec/core/execution.md#outer-effects) defines
monadic execution; [CORE-13](../spec/core/execution.md#outer-effects)
states the lawful-monad and monad-lift consequences. It also identifies the
separate probability contract. This permits several interpretations of one
body without silently changing its sequencing equations.

An outer exception can remove the entire execution report, including an
already produced prefix. An inner stop retains it. The
[OuterEffects controls](../../formal/Tests/OuterEffects.lean) demonstrate both
results for the same two-operation prefix. An adapter claiming inspectable
failure must make the retained record available at its actual boundary.

For a probabilistic example, equal return/exhaustion masses remain one half
each. Discarding exhaustion and renormalizing return to one is conditioning,
not the same experiment. The [probability reference](security-properties.md#probability-initialization-and-persistent-providers)
supplies actual persistent-provider and correlated-service laws; generic
monadic execution alone does not prove those laws or cryptographic security.

### 7. Actual events, phase instrumentation and atomicity

[CORE-14](../spec/core/execution.md#actual-call-records) records actual
calls with their input phases. Erasure recovers the original run; conformance
justifies the recorded call's permission even when it stops; a public bound
limits the number of records. None of these instruments checks source admission.

[CORE-15](../spec/core/execution.md#persistent-history) separately explains when
an event list is also present in persistent state. Its per-operation history
premise is necessary for the whole-body guarantee.

The controller boundary is specified by
[CORE-06](../spec/core/execution.md#call-boundary). If a controller can react
between two emissions of a call, that interaction needs a finer model.
A retained ordered list alone does not model asynchronous delivery or rollback.

### 8. Theory choices and formal coverage

The [effect-tree rationale](../rationale/effect-tree-bodies.md) compares effect
trees with concrete IR semantics, opaque monadic actions and coinductive
interaction trees. The
[correspondence map](../spec/correspondence/core.md) distinguishes
mathematical definitions, generic theorems and actual adapter obligations.
[Composition](composition.md) and [continuations](accepted-continuations.md) apply the
common execution laws to their respective contracts.

## Observations and refinement

The [core specification](../spec/core/observations.md) owns execution/event relations;
[realization](../spec/realization/representations.md) owns represented results;
[disclosure](../spec/properties/disclosure.md) owns joint artifact/runtime disclosure; and
[evidence judgments](../spec/verification/judgments.md) own cost/evidence use.
This guide explains those contracts and their distinct observers. The
[S6 correspondence](../spec/correspondence/properties.md) includes the
normalized randomized joint-release laws.

Correctness concerns a specified observation of a complete execution. A
protocol transcript, a cache trace, a final world projection and a published
artifact can expose different information. The choice belongs to the judgment
being established and cannot be weakened after inspecting an inconvenient run.

### 1. Complete execution relations

[CORE-08](../spec/core/observations.md#event-projections) defines event projection;
[CORE-09](../spec/core/observations.md#execution-relation) defines
`Related` over exact outcomes, related residual states and projected events.
Its return type is shared. For example, a state relation may equate logical
worlds while allowing different valid caches, provided the continuation's
observations satisfy the selected relation law. A representation change needs
the separate relation on represented values as well.

The [realization relation](realization.md#1-data-and-complete-result-relation)
generalizes the reply comparison to different value types interpreted in their
actual final states. Its maintained `Execution.Relates` laws compose representation
boundaries without weakening this equal-reply relation.

[Handler replacement](../spec/core/observations.md#handler-replacement) states the
per-operation premise and its adaptive-body consequence;
[sequential](../spec/core/observations.md#sequential-composition) and
[transitive composition](../spec/core/observations.md#transitive-composition)
complete the laws formerly grouped as CORE-10. The common continuation sees replies. A scheduler reacting to
addresses or cache hits needs those observations modeled in its interface/state.
These laws compose passes; they do not make passes commute.
[CORE-11](../spec/core/observations.md#final-state-observations) gives the
extra compatibility premise for a final-state observer. The
[S1 controls](../../formal/Tests/SpecCore.lean) show why dropping that premise
or changing the selected event observer changes the conclusion.

Each premise of `Related` is used by the induction behind handler replacement:
equal replies keep both continuations on the same branch, related residual
states support their later calls, and projected event lists compose because
`flatMap` preserves append. Exact outcome equality is stronger than some public
observations need; a deliberately weaker property states its own relation and
proof instead of loosening this one. Revisit the relation when a sound
optimization is blocked by equal replies, a required observation cannot be
written as such a projection, or target code can inspect information that this
context does not contain.

### 2. Applicability and stronger contexts

An interpreted contract may restrict legal initial states. To use the generic
all-context theorem, either put the necessary invariant in `R` and show every
operation preserves it, or use handlers that define the behavior of illegal
calls, such as explicit refusal. Removing the illegal branches from a proof
does not justify quantification over all source programs.

Exact equality of complete executions at one selected state can be substituted
under a common suffix using `replacement_then`. It does not imply equality at
other states, across changed input bindings, or for a stateful observer that
interacts between previously atomic events. Such an observer must be modeled
as an interacting participant at the relevant boundaries.

Three quantifiers must stay distinct: refinement under the same reply-adaptive
program; observation agreement between permitted secret worlds; and security
after linking arbitrary allowed target code. `run_related` supplies the first.
Disclosure laws and scoped couplings address instances of the second. The third
requires a target-context model and a strategy translation or robust preservation
argument; it is not obtained by renaming a common continuation an adversary.
The [theory chapter](../theory.md#4-communication-resources-and-implementation)
connects this distinction to secure-compilation research.

For byte-level protocols, erase/expand projections must respect framing and
provider use. Dropping a transcript delimiter can change a later challenge;
an equality of a weaker projected event list would miss that change. The
[realization contract](realization.md) therefore relates buffers,
consumption and actual provider occurrences as well as decoded values.

### 3. Artifact release is a separate channel

An exact internal binding can contain private captures. Publishing that binding,
its source-specialized code, a digest, diagnostic, certificate or proof term is
an additional observation whenever the recipient can inspect it. Deleting
private runtime events does not justify this publication.

[Disclosure](../../formal/Zkc/Semantics/Disclosure.lean) defines the deterministic
contract directly. For allowed pairs of worlds `allowed w v`, a release function
is permitted when:

```text
Permitted allowed release :=
  ∀ w v, allowed w v → release w = release v
publish artifact runtime w := (artifact w, runtime w)
```

`joint_release` combines separately justified artifact and runtime channels.
`joint_requires_artifact` proves why runtime equality alone is insufficient.
Postprocessing a permitted release remains permitted. Deliberate disclosure
changes the allowed comparison by explicitly requiring equality of the approved
disclosed value; it is not silently inferred from the decision to log it.

This is an exact deterministic information-flow contract. [DISC-03](../spec/properties/disclosure.md#randomized-joint-release) requires a relation on their **joint distribution**, or a
common coupling preserving both components. Equal marginal distributions do
not suffice: for a uniform bit `R`, the artifact `R` and runtime `secret XOR R`
each hide the secret separately, but their pair reveals it exactly. The [maintained PMF laws](../../formal/Zkc/Probability/Disclosure.lean)
prove shared-coupling joint release and projection. Normalized
[controls](../../formal/Tests/RandomizedDisclosure.lean) prove the marginal
separator and a positive non-identity coupling. Computational
hiding requires its own experiment and assumptions. A low-entropy secret does not become hidden
merely because its binding is hashed. Internal receipt authenticity and public
release permission remain independent propositions.

The installed continuation adapter supplies a concrete `publicStatus` schema:
a possible verifier decision with return values erased, plus the combined
return/stop status with its value erased. Permission to reveal these statuses
is still required. The integration controls vary the actual private capture
of an admitted source: a failed arm's runtime result is unchanged, the full
receipt reveals that capture, and this status projection remains equal. Thus
the actual receipt/export interface exercises both the leakage and approved
projection cases, without claiming a native serialized artifact ABI.

### 4. Costs and confidential behavior

The preparation protocol observer erases charge events. Its cost observer
retains actual work, saved work and cache overhead. Both observations are valid
for their purposes; equality under the first does not imply equality under the
second. The same distinction applies to cache equality patterns across secret
worlds. Correct cache contents do not prove that cache accesses reveal nothing.

A performance claim states its units, scope, included work and evidence kind.
Symbolic work counts, operation counts, byte lengths and measured wall time
are different quantities. Different upper bounds need not order actual costs.
The [judgment interface](security-properties.md#judgments-premises-and-use) keeps these quantitative
premises and caller requirements explicit.

### 5. Theory choices

Relational semantics provides the actual state/observation comparison;
contextual reasoning determines which continuations may consume it; information
flow compares allowed secret worlds; algebraic trace composition supplies the
sequential law. The source view law is a fixed-source noninterference component,
not a whole-program secrecy proof. Cryptographic couplings and reductions are
defined over the experiments in [Properties](security-properties.md).

A general concurrent bisimulation, a native side-channel model and a universal
stateful-observer logic are not assumed by these finite atomic laws. They are
extensions if a promised interface permits that stronger interaction.
