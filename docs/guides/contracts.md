# Contracts, state and reusable facts

A caller needs a law about the actual operation and reached state. The
[contract rules](#interpreted-contracts-and-state) explain sequencing and
replacement; the [factor/module application](#state-modules-and-reusable-facts)
shows which facts and preparations can be reused after effects.

## Interpreted contracts and state

This guide applies the normative [common contracts](../spec/core/contracts.md)
for complete-result satisfaction, consequence and sequencing, and the
[module profile](../spec/profiles/compiler/factor-preparation.md) for semantic footprints and fact transfer;
[refinement](../spec/verification/refinement.md) and
[conditional judgments](../spec/verification/judgments.md) own replacement and
actual-candidate checking. This page explains their use.

### 1. The contract describes an actual execution

[MOD-01](../spec/core/contracts.md#contract-and-satisfaction) relates
the initial state to the complete actual result. A caller must establish the
precondition and can consume only the guarantees stated by the postcondition.
An abstract contract is useful even without a decision procedure, but its
implementation still needs a proof or an explicit trust premise.

Actual arguments, field/suite and instance interpretation matter. An external
symbol does not identify all contracts that might use that symbol.

### 2. State, aliases and observable failure

A failed write can leave a changed heap, provider state or event prefix.
The [operation controls](../../formal/Tests/OperationContracts.lean) distinguish
equal rejection/event results with different final states. The interpreter
supplies no rollback. Conversely, a particular transactional implementation
can prove its stronger failure contract.

Smaller state carriers can be related to a surrounding world. Physical
separation must cover aliases, and a private cache may still be visible to a
cost observer. [Realization](realization.md) addresses that boundary.

### 3. Facts and a justified frame

[MOD-03](../spec/profiles/compiler/factor-preparation.md#semantic-writes-and-framing)
requires the meaning of a retained fact to survive the actual transition.
The common `frame_transfer` law and concrete `means_frame` law differ in
precision and representation, while both require semantic preservation.
Outcome-specific exports use the post-state. Immutable preparation validity
has a different lifetime from a mutable-world assertion.

### 4. Contract consequence and sequencing

[Consequence](../spec/core/contracts.md#consequence) and the
[sequencing contract](../spec/core/contracts.md#sequencing-contract) supply the
common proof rules. The
[Formal laws](../../formal/Zkc/Semantics/Contracts.lean) connect it to common
`follow` and source `bind`. A weak first postcondition can prevent composition
because it admits too many possible intermediate results. Strengthen it with
proof when needed; do not silently assume only a successful path.

### 5. Backend trust and replacement are different questions

A compiler may quantify over implementations satisfying a module contract.
Replacing its backend still needs the appropriate relational law. Two
implementations satisfying a weak postcondition need not be equivalent.
[TR-02](../spec/verification/refinement.md#refinement-parameters) states the
actual environment/state/value/observation relation, and
[TR-04](../spec/verification/refinement.md#composition-and-observation)
states its composition obligation. Native correspondence and cryptographic
assumptions remain separately visible.

### 6. Theory choices and remaining interpretation work

Two rationale records compare
[semantic footprints with separation logic](../rationale/semantic-footprints.md) and
[candidate checking with verifying the optimizer](../rationale/candidate-checking.md).
The smaller interfaces suffice
for the selected logical worlds. More precise native ownership or solver
machinery must imply these consumer laws rather than replace them by labels.
The [correspondence](../spec/correspondence/transformations.md) records
actual definitions, hypotheses and countermodels.

## State, modules and reusable facts

This guide explains the selected profile in the normative
[module specification](../spec/profiles/compiler/factor-preparation.md). Its definitions distinguish a
current fact, actual availability, immutable preparation and allocation.
The [contract rules](#interpreted-contracts-and-state) covers the common proof obligations.

### 1. Logical state and availability

The [factor world](../../formal/Zkc/Modules/FactorContract.lean) interprets
actual bases, views and coordinate availability. Its `known` list is an
operational availability context. It is not a claim about an adversary's
knowledge. [MOD-04](../spec/profiles/compiler/factor-preparation.md#factor-state-and-facts)
and [MOD-05](../spec/profiles/compiler/factor-preparation.md#query-plans-and-readiness)
separate current meaning from permission to execute a demand.

### 2. Facts, dependencies and framing

The [frame module](../../formal/Zkc/Modules/FactorState.lean) supplies a
computable sufficient unaffectedness test and semantic preservation laws.
Unknown writes lose old reuse information; newly exported facts still require
proof. This conservative finite analysis can later be refined by an alias
analysis or dataflow domain with a sound interpretation.

### 3. Outcome-specific module summaries

[MOD-06](../spec/profiles/compiler/factor-preparation.md#outcome-specific-summaries) owns the summary
and transfer requirements. The [common adapter](../../formal/Zkc/Modules/FactorExecution.lean)
connects its returned Boolean outcome to complete execution. The
[compiler embedding](../../formal/Zkc/Compiler/FactorExecution.lean) preserves
the actual caller's world and events. Its theorem uses actual module laws and
initial fact/availability premises; running inference does not discharge them.

The [typed factor rule](../../formal/Zkc/Compiler/FactorOptimization.lean)
starts without asserted analysis facts, consumes source-produced summaries,
and preserves the guard. Its invariant-based rule is one sufficient profile;
more selective precondition analysis can target the same refinement judgment.

### 4. Installation, namespaces and immutable preparation

[MOD-07](../spec/profiles/compiler/factor-preparation.md#source-derived-views-and-namespaces) separates
reserved-name replacement from fresh allocation and actual registration.
[Installed source inputs](effectful-sources.md#3-installed-namespace-interpretation)
connect the resulting world to the issuer's retained captures.

[MOD-08](../spec/core/contracts.md#immutable-cache-validity)
keeps preparation relative to an actual immutable provider/key. An external
mutation can invalidate a live view while leaving a correctly keyed prepared
table valid. The [bilinear execution](../../formal/Zkc/Polynomial/Bilinear/Execution.lean)
uses both in one state and proves `call_reference` and `call_cache_valid`.
Installation failure retains its actual prefix and does not acquire a table.

### 5. Analysis and preparation in one caller

The [joined theorem](../../formal/Zkc/Polynomial/Bilinear/Compilation.lean)
compares the same caller and module capabilities with direct and memoized
preparation. [MOD-09](../spec/profiles/compiler/factor-preparation.md#guarded-caller-compilation)
explains why `compile_until_refusal` covers a broader domain than the older
legal-caller theorem. The actual guard stays at the demand, and only module
calls reached before refusal need their preconditions.

[MOD-10](../spec/profiles/compiler/factor-preparation.md#immutable-preparation-and-prices)
identifies the selected observer and exact mathematical price criterion.
Different valid caches can preserve protocol observations while a cost or
cache observer distinguishes them.

### 6. Theory choices and limits

Unary fact meaning, [state framing](../rationale/semantic-footprints.md) and
[relational replacement](../spec/core/contracts.md#satisfaction-and-replacement)
remain separate. The
[worked transformation](adding-a-transformation.md) applies them to
one actual caller. Native aliases, costs, buffering and ownership require
realization laws; nominal handle inequality is not such a law.
