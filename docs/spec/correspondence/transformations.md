# Transformation, module and judgment correspondence

Map for [common contracts](../core/contracts.md),
[module profiles](../profiles/compiler/factor-preparation.md) and
[refinement](../verification/refinement.md),
[analysis](../verification/analysis.md) and
[evidence judgments](../verification/judgments.md). `D` is a definition, `T` a theorem under
its actual hypotheses, and `O` a policy or adapter obligation.

## Ownership and notation

The
[typed factor rule](../profiles/compiler/factor-preparation.md#typed-factor-rule)
has one definition home. Its module premises match
`Zkc.Compiler.FactorOptimization.Laws.summary` and `Laws.preserves`;
`refinement` fixes equal environments/states and the invariant, and `rule`
starts both analysis lists empty. `rewrite` retains direct loop bodies,
forgets facts at loop exit, and shares or duplicates continuations according
to the equality of the two outcome transfers. Common analysis and refinement
reference this profile instead of repeating those choices.

The selected
`Source.FactorQueries` source/target signatures and the unit-certificate
application are explicit at that home. The profile distinguishes the smaller caller's
`legal_calls_before_refusal`, which needs legality alone, from
`FactorProgram.compile_enabled`, which additionally requires implementation
satisfaction and sound initial availability. Initial fact validity is required
for the value-preservation theorem, not for this enabledness implication.

More precise joins, inductive loop facts, shared regions and DAGs are design
alternatives; none is an adopted replacement rule.
The smaller caller fragment's specification name `end` corresponds to the
normal-return constructors `Zkc.Compiler.FactorProgram.Source.stop` and
`Zkc.Compiler.FactorProgram.Code.stop`.

The direct profile's `evaluatePlan M h q η s` denotes
`Zkc.Compiler.Plan.run M h q η s`. The common refinement model's `runPlan`
supplies its meaning and handler to that evaluator. The format codecs use the
common `Except` datatype, as does `Zkc.Source.Format.Codec.decode`.

## Module clauses

| Clause | Formal correspondence | Actual hypotheses and limits |
|---|---|---|
| [MOD-01](../core/contracts.md#contract-and-satisfaction), [satisfaction and replacement](../core/contracts.md#satisfaction-and-replacement) | D: `PIR.Contract`, `PIR.Satisfies` | Actual implementation and precondition; postcondition sees complete result; O: actual operation/instance resolution and sufficient consumer guarantees |
| [MOD-02](../core/contracts.md#consequence), [sequencing contract](../core/contracts.md#sequencing-contract) | D: `PIR.Contract.seq`; T: `PIR.satisfies_consequence`, `PIR.satisfies_then`, `PIR.satisfies_bind` | New pre implies old pre; every allowed returned intermediate establishes suffix pre; exact same implementation/source sequencing; conservative, not weakest preconditions |
| [MOD-03](../profiles/compiler/factor-preparation.md#semantic-writes-and-framing) | T: `PIR.frame_transfer`; D: `Zkc.Modules.FactorState.Writes`, `Zkc.Modules.FactorState.Frames`, `Zkc.Modules.FactorState.EffectFrame`, `Zkc.Modules.FactorState.survivors`; T: `Zkc.Modules.FactorState.means_frame`, `Zkc.Modules.FactorState.survivors_valid`, `Zkc.Modules.FactorState.frames_trans` | Actual semantic frame and old fact meaning; unaffected test sufficient; unknown frame imposes no restriction; O: native alias coverage |
| [MOD-04](../profiles/compiler/factor-preparation.md#factor-state-and-facts) | D: `Zkc.Modules.Factor.Key`, `Zkc.Modules.Factor.Fact`, `Zkc.Modules.Factor.State`, `Zkc.Modules.Factor.Means`, `Zkc.Modules.Factor.Valid`, `Zkc.Modules.FactorState.World`, `Zkc.Modules.FactorState.Known`; T: `Zkc.Modules.Factor.kill_valid`, `Zkc.Modules.Factor.remember_valid` | Arbitrary value type, total logical maps and all correctly sized tails; O: actual source identity and materialization correspondence |
| [MOD-05](../profiles/compiler/factor-preparation.md#query-plans-and-readiness) | D: `Zkc.Modules.Factor.check`, `Zkc.Modules.FactorState.Ready`, `Zkc.Modules.FactorState.checkPlan`, `Zkc.Modules.FactorExecution.guard`; T: `Zkc.Modules.Factor.checked_value`, `Zkc.Modules.FactorState.checked_ready`, `Zkc.Modules.FactorState.checked_value` | Fact validity for value equality; separate actual readiness; `guard` preserves state and emits nothing only at its own refused call, not the entire earlier run |
| [MOD-06](../profiles/compiler/factor-preparation.md#outcome-specific-summaries) | D: `Zkc.Modules.FactorState.Summary`, `Zkc.Modules.FactorState.Justifies`, `Zkc.Modules.FactorState.Spec`, `Zkc.Modules.FactorState.Satisfies`; T: `Zkc.Modules.FactorState.nextFacts_valid`, `Zkc.Modules.FactorState.nextKnown_sound`, `Zkc.Modules.FactorState.call_transfer`, `Zkc.Modules.FactorExecution.contract_interpretation` | Actual result-specific post-world, legal call, valid old facts and sound old availability; Boolean returned-result adapter; events not restricted by this unary summary |
| [MOD-07](../profiles/compiler/factor-preparation.md#source-derived-views-and-namespaces), [reserved name installation](../profiles/compiler/factor-preparation.md#reserved-name-installation), [monotone allocation and registration](../profiles/compiler/factor-preparation.md#monotone-allocation-and-registration) | D: `Zkc.Modules.Installation.execute`, `Zkc.Modules.Allocation.allocate`, `Zkc.Modules.FreshAllocation.Registered`; T: `Zkc.Modules.Installation.execute_satisfies`, `Zkc.Modules.Allocation.chosen_fresh`, `Zkc.Modules.Allocation.allocation_failure`, `Zkc.Modules.FreshAllocation.kept_sound` | Actual source request/captures/capacity; freshness relative to good pool; caller name preservation additionally requires actual registration and prior soundness; no native occupancy theorem |
| [MOD-08](../core/contracts.md#immutable-cache-validity), [lookup and storage policy](../core/contracts.md#lookup-and-storage-policy), [provider rebinding](../core/contracts.md#provider-rebinding) | D: `Zkc.Modules.ImmutableCache.Valid`, `Zkc.Modules.ImmutableCache.lookup`; T: `Zkc.Modules.ImmutableCache.lookup_value`, `Zkc.Modules.ImmutableCache.lookup_valid`, `Zkc.Modules.ImmutableCache.rebind`, `Zkc.Transformations.Memoization.client_preservation` | Fixed pure total provider, valid retained entries, decidable key equality; rebinding agrees at occupied keys; actual adaptive client cannot inspect cache/work through this interface |
| [MOD-09](../profiles/compiler/factor-preparation.md#guarded-caller-compilation) | D: `Zkc.Compiler.FactorGuards.CallsBeforeRefusal`; T: `Zkc.Compiler.FactorGuards.guarded_analysis_until_refusal`, `Zkc.Compiler.FactorGuards.enabled_execution`, `Zkc.Modules.FactorExecution.guarded_handlers_related` | Reached preconditions, actual module laws and initial fact/availability validity; guard erasure additionally needs enabledness; handler transport needs same actual availability and underlying relation |
| [MOD-10](../profiles/compiler/factor-preparation.md#immutable-preparation-and-prices), [concrete table preparation](../profiles/compiler/factor-preparation.md#concrete-table-preparation), [joined execution and observer](../profiles/compiler/factor-preparation.md#joined-execution-and-observer) | T: `Zkc.Polynomial.Bilinear.Compilation.compile_until_refusal`, `PIR.Preparation.contextual_memo`, `Zkc.Modules.Preparation.exact_cost_relation`, `Zkc.Modules.Preparation.priced_improvement_iff`, `PIR.Preparation.Emission.priced_improvement` | Same actual caller/installation/modules, initial cache and fact laws, reached preconditions; exact cost laws use the total preparation profile and supplied prices; projected protocol observer excludes charge events |

## Transformation and conditional evidence clauses

| Clause | Formal correspondence | Actual hypotheses and limits |
|---|---|---|
| [TR-01](../verification/refinement.md#preservation-subjects) | D: `Zkc.Compiler.Refinement`, `PIR.Execution.Relates`; O: selected protocol experiment/property transport | Classes identify necessary obligations and may overlap; a generic local relation is not a reduction or hostile-wire theorem |
| [TR-02](../verification/refinement.md#refinement-parameters), [selected execution models](../verification/refinement.md#selected-execution-models), [exact and conditional cases](../verification/refinement.md#exact-and-conditional-cases) | D: `Zkc.Compiler.ExecutionModel`, `Zkc.Compiler.Refinement.Holds`, `Zkc.Compiler.Refinement.exact`; T: `Zkc.Compiler.Refinement.exact_of_execution`, `Zkc.Compiler.Refinement.direct` | Actual environments/states satisfying the chosen initial relation; final-state-indexed values; O: actual initial-domain discharge and native progress |
| [TR-03](../verification/refinement.md#checking-the-actual-candidate), [transformation rules](../verification/refinement.md#transformation-rules) | D: `Zkc.Compiler.TransformationRule`, `Zkc.Compiler.CheckedTransformation`, `Zkc.Compiler.checkTransformation`; T: `Zkc.Compiler.CheckedTransformation.decoded_unique` | Same actual source, rule output and candidate bytes-as-data; finite codec/rule admission/native checking are additional obligations |
| [TR-04](../verification/refinement.md#composition-and-observation) | T: `PIR.replacement_then`, `PIR.Execution.Relates.follow`, `PIR.Execution.Relates.trans`, `PIR.related_observer` | Actual suffix premises, same intermediate execution and observation, final-state observer determined by the relation; O: experiment/property factorization |
| [TR-05](../verification/refinement.md#interpreted-operation-laws) | T: `Zkc.Compiler.Arithmetic.Horner.denote_expand`, `Zkc.Compiler.Arithmetic.Horner.denote_rewrite`; D/T: `Zkc.Compiler.FactorOptimization.Laws`, `Zkc.Compiler.FactorOptimization.execution`, `Zkc.Compiler.FactorOptimization.rule` | Horner needs only semiring laws and retains arbitrary effectful invocation; factor rule needs invariant-preserving summary laws at all invariant states, starts analysis empty and preserves readiness |
| [TR-06](../verification/refinement.md#effects-and-admission-timing) | T: complete-run scope of `Zkc.Compiler.FactorOptimization.execution`, `Zkc.Protocols.Sumcheck.Optimization.run_exact` | O: actual effect/order, staged input, erasure and disclosure obligations for other transformations; no general scheduling theorem is inferred |
| [TR-07](../verification/analysis.md#meaning-and-transfer), [factor analysis and proposals](../verification/analysis.md#factor-analysis-and-proposals) | D: `Zkc.Compiler.FactorReuse.infer`, `Zkc.Compiler.FactorOptimization.rewrite`; T: `Zkc.Compiler.FactorReuse.inferred_checked`, `Zkc.Compiler.FactorReuse.inferred_value`, `Zkc.Compiler.FactorReuse.inferred_ready` | Valid fact context for meaning; readiness supplied separately; current direct loops/fact loss are conservative profile choices; no complete inference or optimality theorem |
| [TR-08](../conventions.md#conformance-claims) | D: separate `Zkc.Source.Program`, `Zkc.Compiler.Plan` and correspondence above | O: explicit compiler subset and representation freedom, actual native/source/operation links; no current implementation API is a universal semantic constraint |
| [JUD-01](../verification/judgments.md#conditional-evidence), [conjunction and transport](../verification/judgments.md#conjunction-and-transport) | D: `PIR.Properties.Conditional`; T/definitions: `PIR.Properties.Conditional.conjoin`, `PIR.Properties.Conditional.transport`, `PIR.Properties.Conditional.use` | Same actual context; both requirements retained; use needs proof at that context; no digest-based rebinding |
| [JUD-02](../verification/judgments.md#evidence-bearing-check-results) | D: `PIR.Properties.Check`; T: `PIR.Properties.Check.proves_sound` | Proof-bearing established branch; arbitrary proposition; no complete decision procedure or native parser proof |
| [JUD-03](../verification/judgments.md#failure-boundaries) | D: `PIR.Properties.Inconclusive`, `PIR.Stop` | O: phase-specific diagnostics, adapter faults and process-death boundary; mathematical stops are not generic tooling statuses |
| [JUD-04](../verification/judgments.md#caller-requirements), [cost comparison and optimality](../verification/judgments.md#cost-comparison-and-optimality) | D: `PIR.Properties.Usable`; T: `PIR.Properties.separated_costs`, `Zkc.Modules.Preparation.priced_improvement_iff` | Actual caller requirement and quantities; separating upper/lower bounds or exact accounting; O: native metrics and any claimed complete optimality domain |

## Controls

The checked controls are substantive countermodels:

- `Tests.OperationContracts` retains writes before rejection, distinguishes
  equal stop/event data with unequal states, and exposes a cost observer that
  distinguishes otherwise equal protocol executions.
- `Tests.Transformation` uses independently authored candidate data, two fields,
  shifted operands, loops and actual failed prefixes; it rejects another
  source/candidate and refutes interpretation by operation spelling alone.
- `Tests.FactorOptimization` checks source-produced facts, failed overwrite,
  wrong coordinates/axes and actual unavailable queries.
- `Tests.TheoryReview` separates direct value checking from readiness, fresh
  allocator pools from populated worlds, and the reached-refusal theorem from
  the older stronger legality domain.
- `Tests.Integration` retains conditional premises and inconclusive outcomes,
  separates legal from usable, and refutes comparison by upper bounds alone.

## Profiles

The [finite phase algorithm](../profiles/compiler/finite-phases.md) and
[typed factor rule](../profiles/compiler/factor-preparation.md#typed-factor-rule)
own their selected algorithms. The common [merge condition](../verification/analysis.md#merging-descriptions)
is the propositional consequence of weakening from each alternative; it is not
a new implemented factor merge or a newly claimed Lean declaration. The existing
phase cover uses union; conjunctions of known facts have different meaning.

The [admission clarification](../verification/refinement.md#effects-and-admission-timing)
retains a separate all-reply transport premise.
[PhaseAdmission.Realizes.translate](../../../formal/Zkc/Source/PhaseAdmissionInterpretation.lean)
requires `InterpretationAdmission`; [Artifact.checkCandidate](../../../formal/Zkc/Compiler/Artifact.lean)
only handles the direct artifact. Neither supplies an arbitrary optimized
artifact/phase composition. An optimized artifact must implement its actual binding and law.
A bounded rewrite requires a new
proved rule rather than reusing the `FactorOptimization.rewrite` theorem for a different algorithm.
