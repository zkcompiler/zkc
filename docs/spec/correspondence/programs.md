# Program, input and interaction correspondence

This is an evidence map for
[typed programs](../language/programs.md), [common inputs](../language/inputs.md),
[interaction](../language/interaction.md), and their direct-plan, expression
and phase-analysis profiles. This map does
not redefine the clauses or turn an adapter obligation into a proved theorem.

The phase-certificate sidecar corresponds to
`Zkc.Source.PhaseAdmission.encodeCertificate`, `decodeCertificate` and
`certificateCodec`, with the actual phase codec and independent depth limit;
decoding alone supplies no phase-admission theorem.

`D` means a reviewed definition; `T` means a kernel-checked theorem with its
actual hypotheses; `O` means a policy or concrete correspondence obligation.
Names below use their full Lean namespace. The map is semantic review evidence;
name existence and link checks alone cannot validate it.

## Common program and plan

| Clause | Formal correspondence | Quantifiers and limits |
|---|---|---|
| [PROG-01](../language/programs.md#language-signatures), [operation meanings](../language/programs.md#operation-meanings) | D: `Zkc.Source.Language`, `Zkc.Source.Interpretation` | Arbitrary sort/operation types and selected signature; O: descriptor codecs/resolution, actual field meaning and conversion laws |
| [PROG-02](../language/programs.md#contexts-and-values), [operand lists](../language/programs.md#operand-lists) | D: `Zkc.Source.Var`, `Zkc.Source.Values`, `Zkc.Source.Environment.push`, `Zkc.Source.Operands.eval`; T: `Zkc.Source.Var.decode_index`, `Zkc.Source.Operands.eval_rename` | Ordered heterogeneous contexts; exact operand sort required; no equation equates different positions or fields |
| [PROG-03](../language/programs.md#typed-control) | D: `Zkc.Source.Program` | Intrinsic contexts at each constructor; finite syntax; no implicit loop index or mutation of lexical captures |
| [PROG-04](../language/programs.md#denotation) | D: `Zkc.Source.Program.denote`, `PIR.repeatN` | For the actual interpretation and environment; sequencing includes terminal failure through core bind |
| [PROG-05](../language/programs.md#renaming), [source sequencing](../language/programs.md#source-sequencing), [reinterpreting operations](../language/programs.md#reinterpreting-operations) | T: `Zkc.Source.Program.denote_rename`, `Zkc.Source.Program.denote_seq`, `Zkc.Source.Program.run_seq`, `Zkc.Source.Program.denote_translate` | Every typed environment/interpretation; source sequencing retains original captures; translated operations must be the same supplied interpretation |
| [PROG-06](../language/programs.md#raw-formation) | D: `Zkc.Source.RawProgram.elaborate`, `Zkc.Source.decodeOperands`; T: `Zkc.Source.Program.elaborate_erase` | Decidable sort equality; exact typed round trip under original context; O: parser and external vocabulary resolution |
| [PROG-07](../language/programs.md#structural-call-bounds) | D: `Zkc.Source.Program.callBound`; T: `Zkc.Source.Program.denote_within`, `PIR.ExecutionPath.calls_bounded` | Uniform operation bound for every typed argument list; all source environments and all typed reply paths; O: public origin of selected counts, native cost laws |
| [PROG-08](../profiles/compiler/direct-plan.md#typed-plans), [evaluation](../profiles/compiler/direct-plan.md#evaluation), [direct lowering](../profiles/compiler/direct-plan.md#direct-lowering) | D: `Zkc.Compiler.Plan`, `Zkc.Compiler.executeLoop`, `Zkc.Compiler.Plan.run`; T: `Zkc.Compiler.lower_correct` | Equality of complete execution for every interpretation, handler, environment and state; O: profile status rather than a mandatory future IR |
| [PROG-09](../profiles/compiler/direct-plan.md#checked-plans) | D: `Zkc.Compiler.CheckedPlan`, `Zkc.Compiler.checkDirect`; T: `Zkc.Compiler.CheckedPlan.decoded_unique`, `Zkc.Compiler.CheckedPlan.calls_bounded`, `Zkc.Compiler.CheckedPlan.calls_permitted`, `Zkc.Compiler.CheckedPlan.return_permitted`, `Zkc.Compiler.CheckedPlan.instrumented_erasure` | Same retained source and actual decoded candidate; bounds require uniform operation laws; phase conclusions additionally require admitted source, summary laws and initial coverage; none implies native correctness |

## Inputs and the pure frontend

| Clause | Formal correspondence | Quantifiers and limits |
|---|---|---|
| [INPUT-01](../profiles/source/named-inputs.md#exact-ordered-binding), [declarations and supplied values](../profiles/source/named-inputs.md#declarations-and-supplied-values) | D: `Zkc.Source.InputDeclaration`, `Zkc.Source.SuppliedInput`, `Zkc.Source.bindInputs`, `Zkc.Source.suppliedFromValues`; T: `Zkc.Source.bindInputs_exact` | Successful binding, actual declarations/role/supplied records/returned values; exact reification of the whole list; O: external authentication and ownership |
| [INPUT-02](../profiles/source/named-inputs.md#typed-role-stores), [equal permitted views](../profiles/source/named-inputs.md#equal-permitted-views) | D: `Zkc.Source.LocalInputs.World`, `Zkc.Source.LocalInputs.read`, `Zkc.Source.LocalInputs.bind`, `PIR.SourceView.read`, `PIR.SourceView.env`, `PIR.SourceView.SameView` for the [positional instance](../profiles/source/expressions.md#positional-inputs); T: `Zkc.Source.LocalInputs.run_agrees`, `PIR.SourceView.read_permitted`, `PIR.SourceView.read_agrees` | Same shared and actor-private stores; typed whole-run law additionally fixes source, interpretation, handler and initial state; not hidden-runtime-state noninterference |
| [INPUT-03](../profiles/source/expressions.md#expression-syntax-and-meaning), [dependencies and scope](../profiles/source/expressions.md#dependencies-and-scope), [positional inputs](../profiles/source/expressions.md#positional-inputs) | D: `Zkc.Source.Expressions.Expr`, `Zkc.Source.Expressions.Expr.eval`, `Zkc.Source.Expressions.Expr.deps`, `Zkc.Source.Expressions.Allowed`; T: `Zkc.Source.Expressions.check_iff`, `Zkc.Source.Expressions.eval_agreement` | Ring and decidable value equality for evaluation, decidable variable equality for checking; sufficient dependency list, not minimal support |
| [INPUT-04](../profiles/source/expressions.md#substitution-and-intrinsic-scope) | D: `Zkc.Source.Expressions.Scoped`; T: `Zkc.Source.Expressions.erase_restrict`, `Zkc.Source.Expressions.checked_iff_intrinsic`, `Zkc.Source.Expressions.erase_eval`, `Zkc.Source.Expressions.eval_bind` | Same expression/scope/environment; says nothing about absent values or unrelated annotations |
| [INPUT-05](../profiles/source/expressions.md#finite-closures), [whole capture readiness](../profiles/source/expressions.md#whole-capture-readiness), [issuance and actor admission](../profiles/source/expressions.md#issuance-and-actor-admission) | D: `Zkc.Source.Expressions.Closure`, `PIR.Source.captureDeps`, `Zkc.Source.Availability.ready`, `PIR.Source.issue`; T: `Zkc.Source.Availability.ready_iff`, `PIR.Source.issued_reads`, `PIR.Source.capture_default_irrelevant` | All declared capture expressions, including unused/dormant dependencies; successful issuance required for fallback independence |
| [INPUT-06](../profiles/source/expressions.md#issuance-and-actor-admission), [invocation and elaboration](../profiles/source/expressions.md#invocation-and-elaboration) | D: `PIR.Source.Bound`, `PIR.Source.admit`, `PIR.Source.elaborate`; T: `PIR.Source.admitted_reads`, `PIR.Source.admission_same_view`, `PIR.Source.issued_value`, `PIR.Source.elaboration_exact`, `PIR.Source.elaboration_boundary`, `PIR.Source.admitted_context_related` | Fixed source and binding; last law also needs fixed continuation, actual handler relation and related initial states; O: native immutable/live-reference correspondence |
| [INPUT-07](../language/inputs.md#source-selection-and-release) | T: fixed-source scope of `PIR.Source.admission_same_view`; controls in `Tests.Source` | O: actual source selection and joint disclosure law; fixed-source equality is not a theorem about arbitrary secret generators or public release |

## Interaction, admission and composition

| Clause | Formal correspondence | Quantifiers and limits |
|---|---|---|
| [INT-01](../language/interaction.md#public-families-and-semantic-subjects) | D: parameterization of `PIR.Interaction`, `Zkc.Source.Interpretation` and concrete relation families | O: semantic subject separation, parameter/invocation distinction and family quantification; no universal executable `P/A/L` checker is asserted |
| [INT-02](../language/interaction.md#roles-and-phases) | D: `PIR.Interaction` | Actual operation-dependent reply type; O: interface adequacy including hostile/malformed input domain and actual initial state |
| [INT-03](../language/interaction.md#all-reply-conformance), [returning postconditions](../language/interaction.md#returning-postconditions) | D: `PIR.Conforms`, `PIR.Boundary.Returns`, `PIR.Reaches`; T: `PIR.conformance_preserved`, `PIR.ExecutionPath.calls_permitted`, `PIR.Boundary.actual_return` | All typed replies; actual-return theorem requires a returned outcome; stopped paths make no returning postcondition claim |
| [INT-04](../language/interaction.md#phase-safe-sequencing), [bounded repetition](../language/interaction.md#bounded-repetition) | T: `PIR.Boundary.conforms_bind`, `PIR.Boundary.returns_bind`, `PIR.Boundary.repeat_formed`, `PIR.Boundary.repeat_bound` | Actual returned value/phase establishes the suffix premise; repetition invariant holds at every relevant step; O: count publicity and module resource premises |
| [INT-05](../language/interaction.md#endpoint-admission), [local information](../language/interaction.md#local-information) | D: `PIR.LocalStrategy`, `PIR.HonestRole`, `PIR.Frontend`, `PIR.EndpointContract`, `PIR.Admitted`; T: `PIR.admitted_body_unique`, `PIR.admitted_execution_related`, `Zkc.Semantics.Locality.local_factor_necessary`, `Zkc.Semantics.Locality.no_local_adapter`, `Zkc.Semantics.Locality.descent` | Supplied input/honesty predicates are not automatically adequate; same-source uniqueness; relational theorem needs handler/state relation; locality obstruction requires equal views and unequal required actions; constructive descent additionally supplies a representative, image section law and equality on every view fiber |
| [INT-06](../language/interaction.md#atomic-sessions) | D: `PIR.Sessions.sig`, `PIR.Sessions.interaction`; T: `PIR.Sessions.selected_phase`, `PIR.Sessions.other_phase`, `PIR.Sessions.actual_calls` | Decidable session equality; dependent signature/phase family; other-phase law needs a distinct session; runtime state may be shared |
| [INT-07](../profiles/compiler/finite-phases.md#abstract-phase-policy), [certificates](../profiles/compiler/finite-phases.md#certificates), [checking rules](../profiles/compiler/finite-phases.md#checking-rules), [realizing a policy](../profiles/compiler/finite-phases.md#realizing-a-policy), [coverage and soundness](../profiles/compiler/finite-phases.md#coverage-and-soundness), [checked phase admission](../profiles/compiler/finite-phases.md#checked-phase-admission), [precision and unsupported cases](../profiles/compiler/finite-phases.md#precision-and-unsupported-cases) | D: `Zkc.Source.PhaseAdmission.Policy`, `Zkc.Source.PhaseAdmission.Certificate`, `Zkc.Source.PhaseAdmission.check`, `Zkc.Source.PhaseAdmission.Realizes`; T: `Zkc.Source.PhaseAdmission.check_sound`, `Zkc.Source.PhaseAdmission.Admitted.sound` | Decidable abstract-phase equality; every accepted summary covers all typed arguments and related concrete entries; initial coverage and permitted exits required; O: resolution to actual operation meanings |
| [INT-08](../core/interpretations.md#phase-admission), [expansion bounds](../core/interpretations.md#expansion-bounds) | D: `PIR.InterpretationAdmission`; T: `PIR.InterpretationAdmission.transport`, `Zkc.Source.PhaseAdmission.Realizes.translate`, `PIR.Proc.within_interpret` | Actual reply-dependent phase relation and full lower-body laws; uniform constant operation bound for the multiplicative bound; no locality/security inference |
| [INT-09](../conventions.md#execution-envelope) | D: inductive `PIR.Proc`, `PIR.Within`, session interpretation | O: selected supported envelope and exclusions; no unrestricted recursion, asynchronous projection, adaptive corruption or complexity theorem |

## Controls

The controls exercise semantic distinctions, not merely clause/name coverage:

- `Tests.SourcePlan`: actual `ZMod 5` and `ZMod 7`, swapped same-sort operands,
  wrong-sort and out-of-range references, malformed dormant code, missing and
  foreign inputs, duplicate declarations, stopped state/event prefixes and
  unapproved artifact claims.
- `Tests.PhaseAdmission`: early challenge despite successful direct checking,
  wrong returned phase, bad loop certificates, preserved stopped prefix, a
  semantically safe zero-count body refused by the analysis, and impossibility
  of a summary justified by one selected reply.
- `Tests.Source`: missing versus zero, dormant and unused captures, changed
  snapshots, same-view issuance, and secret source-selection limits.
- `Tests.Composition`, `Tests.SourceComposition`, `Tests.Locality`: actual
  suffix entry, shared-session order, capture-preserving structured regions and
  impossible local implementation from insufficient views.

These correspondences do not prove a general native parser/backend, optimal phase analysis,
every frontend-to-common-source conversion, polynomial source adequacy or
cryptographic security.

## Profiles

The named binder and typed role stores live in
[named inputs](../profiles/source/named-inputs.md); positional expression inputs
remain a separate [source profile](../profiles/source/expressions.md). Both keep the
same binding, dependency and all-reply premises.

## Configured families

[`Source.Family`](../../../formal/Zkc/Source/Family.lean) defines complete ingress,
actual selected-member execution, fixed-program embedding, per-member admission
and constructive role knowledge. `Selects` connects actual successful ingress to
allowed inputs. `Admitted.selected` transfers the member's bound and admission
at its declared initial phase. `selected_at` additionally requires that phase
to agree with the actual residual state's phase interpretation. Neither law
certifies ingress, live input resources, native handler interpretation, or the
stored-source elaboration and input binding carried by `PIR.Admitted`; a
compiler-facing adapter supplies those separate premises.
`SelectsReady` states ingress readiness over the whole claimed domain;
`Admitted.selected_ready` retains that postcondition and transfers admission at
the actual residual phase. `run_proc` reduces process-valued ingress to ordinary
`run_bind`, allowing the existing `Boundary` composition laws to be used.
`Tests.ProtocolFamily` binds real ingress seeds to stored ports and instantiates
symbolic stored callees. `Tests.FamilyRepresentation` includes dependent inputs
and positive/negative ingress readiness controls; these are concrete fixtures,
not a universal source-binding or role-delivery theorem.
[`Protocol.Family`](../../../formal/Zkc/Source/Protocol/Family.lean) instantiates
scoped counts in the existing grammar. The common, scheduled and role `Counts`
modules prove functor laws and both projection commuting laws, including stored
callees. `nodeCount_mapCounts` proves substitution does not unroll. Counts remain
natural numbers at execution; runtime-symbolic native admission is not proved or
installed by these typed-syntax theorems.
