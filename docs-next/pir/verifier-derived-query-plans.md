# Verifier-Derived Query Plans

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Provisional owner:** `pir`
> **Authority:** None during the transition. Current normative Protocol
> semantics remain under [`docs/`](../../docs/README.md).

## 1. Contract

This page solely owns finite verifier-derived word programs, logical query
plans, checked static elaboration into one independently admitted flat
`InteractiveCore`, exact logical-to-source occurrence maps, bounds, outcomes,
and the resulting inert structural handle.

The [Interactive Core](interactive-core.md) continues to own every executable
Oracle, query, answer, derived value, guard, terminal, observation, execution,
and replay rule. A verifier-derived word is therefore not a third
`OracleOrigin`, a publication mode, a commitment, a runtime capability, or a
new Core effect. The [Oracle-Commitment
Construction](oracle-commitment-construction.md) operates only on the ordinary
source Oracles and source-query occurrences in the elaborated Core. The
[Fiat--Shamir construction](fiat-shamir.md) sees only the real public Core
observations; a plan declaration and a logical derived read add no transcript
frame.

Foundation owns identities, profiles, canonical values, portable algorithms,
evaluation contracts, typed failures, and evaluator noncompletion. Relations
may state source correspondence for a checked elaboration. Analysis may use an
exact checked elaboration when a theorem question depends on logical query
multiplicity or the source-to-leaf resource map. Neither downstream owner may
create or repair an elaboration.

The selected direction is:

```text
finite derived-word programs + finite logical query plan
                         |
                         | deterministic bounded elaboration
                         v
        independently formed and admitted flat InteractiveCore
                         |
                         | exact map checking
                         v
          CheckedVerifierDerivedQueryElaboration
```

Execution occurs only in the flat Core. The plan remains an exact logical and
correspondence coordinate; it is never interpreted as a runtime subschedule.

## 2. Why this is a satellite rather than a Core feature

Several protocol families define words that the verifier can read using
earlier fixed Oracles and public values without asking the prover to publish a
new word. Materializing such a word as a prover Oracle changes strategy
authority, transcript influence, commitment roots, and soundness experiments.
Conversely, evaluating an opaque query callback at runtime would permit
unauthenticated effects and would invalidate occurrence-keyed replay and
resource accounting.

The flat Core already has the necessary executable atoms:

- total portable derived values;
- public-data-dependent guards;
- immutable source Oracles;
- explicit `QueryOracle` and `AnswerOracle` occurrences; and
- explicit terminal paths.

What it lacks is a reusable, identified explanation that one logical read is
realized by a particular finite guarded set of those atoms. This page adds
that explanation and its checker without changing Core execution.

<!-- zkc-profile-source:verifier-derived-query-plan-semantics:start -->

## 3. Profile and intake

For one exact Foundation prior-meta basis `B`, the owner consumes:

- authenticated portable algorithms and evaluation contracts;
- exact `ValueType` values and finite canonical collections;
- an exact authenticated `PIRInteractionProfileId` closure;
- exact admitted target-Core handles; and
- Foundation typed outcomes and deterministic evaluation control.

The exact `PIRVerifierDerivedQueryPlanProfile` has family
`"pir.verifier-derived-query-plan"`, revision zero, and directly imports only
`PIRInteractionProfileId`. Its supported subject kinds are:

```text
pir.verifier-derived-word-program
pir.verifier-derived-query-plan
pir.verifier-derived-query-elaboration
```

An import is present because program algorithms, target `ValueRef` and
`OracleRef` coordinates, guards, occurrences, terminals, Core IDs, and Core
admission all retain Interaction meaning. No commitment, transcript,
Relations, Analysis, OIR, or implementation profile is imported.

The body compiler has one closed arm per advertised kind:

```text
VerifierDerivedQueryPlanDomainBodyV0 =
    WordProgramBody(VerifierDerivedWordProgram)
  | QueryPlanBody(VerifierDerivedQueryPlan)
  | ElaborationBody(VerifierDerivedQueryElaboration)
```

`VerifierDerivedQueryPlanId<K>(x)` abbreviates the Foundation profiled semantic
ID under `PIRVerifierDerivedQueryPlanProfileId` and the exact arm assigned to
kind `K`. A wrong arm is `KindMismatch`; an unknown arm is `Unsupported`; an
open default is `Refused`.

## 4. Verifier-derived word programs

### 4.1 Formal ports and local references

```text
ProgramParameterDecl = {
  value_type: ValueType,
  visibility: Public | VerifierOnly
}

ProgramOraclePortDecl = {
  index_type: ValueType,
  answer_type: ValueType,
  visibility: Public | VerifierOnly
}

ProgramLocalValueRef =
    RequestedIndex
  | Parameter(ProgramParameterRef)
  | StepOutput(ProgramStepRef)
```

The requested index has the program's declared `index_type`. Parameters and
Oracle ports use dense declaration ordinals. A step output refers only to an
earlier step in the same case. There is no ambient Core value, Oracle registry,
callback, host object, or unresolved authoring name.

### 4.2 Closed finite cases

```text
ProgramRoute = {
  algorithm: PIRAlgorithmUse,
  inputs: CanonicalSeq<RequestedIndex | Parameter>,
  case_type: ClosedFiniteVariantType
}

ProgramStep =
    PureStep {
      algorithm: PIRAlgorithmUse,
      inputs: CanonicalSeq<ProgramLocalValueRef>,
      result_type: ValueType
    }
  | SourceReadStep {
      source: ProgramOraclePortRef,
      index: ProgramLocalValueRef,
      answer_type: ValueType
    }
  | InvokeProgramStep {
      program_id: VerifierDerivedWordProgramId,
      requested_index: ProgramLocalValueRef,
      parameters: TotalMap<child parameter, ProgramLocalValueRef>,
      oracle_ports: TotalMap<child Oracle port, parent Oracle port>,
      result_type: ValueType
    }

ProgramCaseOutcome =
    Return(ProgramLocalValueRef)
  | ReachExplicitTerminal(ProgramTerminalContract)

ProgramTerminalContract = {
  outcome_label: ExactAsciiSymbol,
  verdict: Reject | Abort
}

ProgramCase = {
  case_ordinal: ordinal in ProgramRoute.case_type,
  steps: CanonicalSeq<ProgramStep>,
  outcome: ProgramCaseOutcome
}

VerifierDerivedWordProgram = {
  index_type: ValueType,
  result_type: ValueType,
  algebra_profile: PrimeFieldV0 { modulus: PrimeNatural },
  parameters: CanonicalSeq<ProgramParameterDecl>,
  oracle_ports: CanonicalSeq<ProgramOraclePortDecl>,
  route: ProgramRoute,
  cases: NonEmptyCanonicalSeq<ProgramCase>,
  output_visibility: Public | VerifierOnly,
  maximum_elaboration_depth: Natural,
  maximum_leaf_reads: Natural
}
```

The route algorithm is total, failure-free, and returns exactly the closed
case type. Cases cover every variant ordinal exactly once, so exactly one case
is selected for every admitted runtime input. A route reads only the requested
index and declared parameters. It cannot read a source answer or an invoked
program result.

Every pure step uses an admitted total failure-free algorithm with the exact
input and output ABI. A mathematically partial operation is represented by a
route case leading to an explicit terminal or by a total tagged value consumed
under an explicit branch; it is never hidden as an evaluator exception. For
example, a quotient program may route denominator-zero indices to a named
terminal and evaluate its totalized division algorithm only on the disjoint
return case.

Every route and pure algorithm is interpreted under the program's exact
algebra profile. The v0 profile admits only a prime-field carrier with a
checked prime modulus. A composite modulus is `Refused`; an otherwise formed
future algebra profile without selected semantics is `Unsupported`. Inverse,
quotient, and fold operations expose zero or invalid domains through their
closed route cases rather than relying on host-language arithmetic behavior.

A source read has no independent logical publication. It denotes one leaf in
the later static elaboration. Its answer type exactly equals the bound source
Oracle's `OracleAnswerOutputType`; a full finite Oracle's tagged absence is not
silently coerced to a logical-access element.

An invoked program is a prior exact program ID. Its parameter and Oracle-port
maps are total and kind-exact. Program-ID dependency closure must be acyclic.
Content-addressed IDs prevent a genuine self-preimage, while admission also
rejects a malformed supplied graph before expansion.

### 4.3 Nonadaptive structural boundary

Program admission derives source-answer taint. Every source-read index, every
nested invocation index, and every nested argument that can influence the
child's route or source-read indices must be free of that taint. Pure result
computation may consume answers after all corresponding reads.

Thus runtime public values may select one of finitely many authenticated
branches and compute the indices in that branch, but a source answer cannot
allocate, suppress, redirect, or retarget a later source read. An
answer-adaptive plan requires a future separately researched profile and is
`Unsupported` here.

### 4.4 Exact bounds

For each case, `LeafReads` is the number of direct source reads plus the exact
leaf count of every nested invocation. `ElaborationDepth` is one for a program
with no invocation and otherwise one plus the maximum child depth. Program
bounds equal the maxima over all cases; they are recomputed, not upper-bound
claims supplied by the author.

An unequal declared bound is `Refused`. Independent evaluator work limits are
not fields of the program and do not rotate its ID.

Static expansion also receives an external maximum-event control. Exhausting
that control yields `DeterministicLimitExceeded` and no elaboration; it does not
change program, plan, or Core identity. The v0 semantic bounds remain exact
per-program depth and leaf-read counts rather than a caller-selected template
budget.

## 5. Logical query plans

```text
QueryPlanInputDecl = {
  value_type: ValueType,
  visibility: Public | VerifierOnly
}

QueryPlanOracleDecl = {
  index_type: ValueType,
  answer_type: ValueType,
  visibility: Public | VerifierOnly
}

QueryPlanValueRef =
    PlanInput(QueryPlanInputRef)
  | PriorLogicalResult(LogicalQueryUseRef)

LogicalQueryUse = {
  program_id: VerifierDerivedWordProgramId,
  activation: Always | PublicBoolean(QueryPlanValueRef),
  requested_index: QueryPlanValueRef,
  parameters: TotalMap<program parameter, QueryPlanValueRef>,
  oracle_ports: TotalMap<program Oracle port, QueryPlanOracleRef>
}

VerifierDerivedQueryPlan = {
  inputs: CanonicalSeq<QueryPlanInputDecl>,
  source_oracles: CanonicalSeq<QueryPlanOracleDecl>,
  logical_uses: NonEmptyCanonicalSeq<LogicalQueryUse>
}
```

The logical-use sequence preserves labels by ordinal, multiplicity, and causal
order. A repeated logical read remains repeated even if all runtime indices
and answers are equal. The v0 profile exposes a prior logical result only from
an unconditionally active producer with one total static return. Its existing
target value is reused directly; elaboration does not mint a logical-result
event or join node. Supporting conditional or multi-return joins requires a
separately specified Core construction and is `Unsupported` here.

Source-answer taint is rejected from activation, requested indices, routes,
and every nested argument that can transitively affect routing or a source-read
index. It may flow into post-read pure value computation. This effect-sensitive
rule permits ordinary verifier arithmetic over earlier answers without making
the query schedule answer-adaptive.

Plan inputs and source Oracles are formal typed ports, not runtime values or
Core references. The plan can therefore be identified independently of one
target Core. Runtime values, prover strategies, commitment roots, evidence,
and evaluator budgets are absent from its identity.

One admitted plan describes one concrete parameterization and is checked
against one concrete Core. A compile-time family may produce separately
identified plans and Cores from public parameters, but that generating function
is authoring/compiler machinery rather than a v0 query-plan subject. Generic
family admission remains future work and cannot be inferred from successful
member elaborations.

## 6. Static elaboration

### 6.1 Elaboration subject

```text
RouteCaseMap = {
  route_value: DerivedValueRef,
  case_guards: TotalMap<case ordinal, exact target Guard>
}

ProgramStepImage =
    PureImage(DerivedValueRef)
  | SourceReadImage {
      query: OccurrenceRef,
      answer: OccurrenceRef,
      answer_value: ValueRef
    }
  | InvocationImage {
      child_route: RouteCaseMap,
      child_steps: TotalMap<child path, ProgramStepImage>,
      child_results: TotalMap<child return case, ValueRef>,
      child_terminals: TotalMap<child terminal case, TerminalRef>
    }

LogicalUseImage = {
  activation_guard: exact target Guard,
  route: RouteCaseMap,
  steps: TotalMap<program path, ProgramStepImage>,
  results: TotalMap<return case path, ValueRef>,
  terminals: TotalMap<terminal case path, TerminalRef>,
  ordered_leaf_queries:
    CanonicalSeq<(program path, OccurrenceRef, OccurrenceRef)>
}

VerifierDerivedQueryElaboration = {
  plan_id: VerifierDerivedQueryPlanId,
  target_core_id: CoreId,
  plan_inputs: TotalMap<QueryPlanInputRef, ValueRef>,
  plan_oracles: TotalMap<QueryPlanOracleRef, OracleRef>,
  logical_uses: TotalMap<LogicalQueryUseRef, LogicalUseImage>
}
```

The target Core is formed and admitted independently. It contains every route
value, case guard, pure value, source query, answer, and explicit terminal in
ordinary Interaction syntax. No plan ID or logical derived-word declaration
is placed in `InteractiveCoreBody`; the plan cannot alter Core admission by
nominal attachment.

### 6.2 Exact elaboration law

`ExpectedElaboration(plan, input_map, oracle_map)` recursively expands every
program case in canonical program-path order before Core authentication. It
emits a finite guarded template, including branches not selected in one run.
The resulting expected image has no runtime-created entry.

For every image, checking requires:

1. every plan input maps to one target `ValueRef` of exact type and visibility;
2. every plan Oracle maps to one target `OracleRef` with exact index type,
   answer type, visibility, scope availability, and immutable lifecycle;
3. each route value is the exact target `DerivedValueDecl` using the same
   algorithm and mapped inputs;
4. case guards compare that one route value with every and only case ordinal;
5. every pure step maps to one exact target derived value with recursively
   mapped operands;
6. every source read maps to one `QueryOracle` and its unique later
   `AnswerOracle`, under the exact conjunction of use activation and enclosing
   route guards;
7. every invocation is recursively and completely mapped;
8. every return maps to the exact target value consumed under the same guard;
9. every terminal case maps to an explicit target terminal with the declared
   verdict and guard; and
10. `ordered_leaf_queries` contains every mapped source query exactly once in
    recursive logical order, retaining repeated equal queries.

The target occurrence order must satisfy ordinary Core causality: mapped
inputs and Oracles are available before use; a query follows publication; its
answer follows that query; pure consumers follow every operand; and terminals
stop their paths. A map cannot claim that target order follows the plan when
Core admission says otherwise.

The checker compares the complete expected image with the supplied
elaboration. Missing, extra, aliased, reordered, or kind-incompatible entries
refuse. Equal output values or equal Core fragments do not repair a map.

### 6.3 Checked result

```text
CheckVerifierDerivedQueryElaboration(
  AuthenticatedAdmittedPlan,
  AuthenticatedAdmittedTargetCore,
  AuthenticatedElaboration,
  exact supported evaluator,
  deterministic work limit)
  -> Affirmative(CheckedVerifierDerivedQueryElaboration)
   | Negative(ElaborationDefectSet)
   | Unsupported | MissingDependency | CannotAnswer | KindMismatch
   | Malformed | Refused | DeterministicLimitExceeded | CheckerFailure
```

An affirmative result retains exact authenticated handles for the plan,
elaboration, target Core, selected profile closure, and complete checked map.
It is inert and serializable only as ordinary identified data plus validation
status; it grants no execution, disclosure, theorem, or compiler authority.
Revalidation recomputes all identities, admissions, expansion, maps, and
bounds.

## 7. Visibility, observations, and Fiat--Shamir

Visibility is a monotone join over plan inputs and source Oracle ports. A
public logical result whose dependency closure contains a verifier-only input,
query, or answer is `Refused`; no implicit declassification exists. A
verifier-only logical result may map only to target values and consumers whose
ordinary Core visibility rules permit it.

Plan formation, route declaration, logical-use declaration, elaboration, and
checked status are not Protocol observations. Runtime observation is exactly
the elaborated Core's ordinary behavior:

- a public source query and answer have their normal Core and transcript
  meaning;
- a verifier-only source query and answer remain private and retain the Core's
  public-coin restrictions;
- a pure derived value creates no message or transcript frame; and
- a plan-level logical read creates no additional frame.

Fiat--Shamir therefore runs after elaboration on the unchanged admitted flat
Core. Absorbing a plan, route selection, logical derived answer, or invented
derived-word fixation marker is `Refused` unless a future source protocol
contains a corresponding real public event and a different checked
construction adds it to a different Core.

## 8. Commitment, composition, Relations, and Analysis

Commitment compilation sees the target Core's actual source Oracles and leaf
queries. It may map those logical occurrences to roots and opening evidence
under its own checked construction. It cannot commit a derived word merely
because a plan names one, and it cannot deduplicate repeated logical queries
without the commitment profile's separate occurrence-to-evidence law.

Finite composition remains flat. An authoring or composition route may use a
query plan to construct its target fragment, but the composed target Core is
authenticated and admitted without retaining a child execution handle. A
future checked Core-composition satellite that maps a child's logical derived
read must consume the exact affirmative elaboration as an additional operand;
ordinary value face maps alone cannot be claimed to imply it.

Relations may ask whether a mapped result equals the source paper's quotient,
batching, projection, or folding formula and whether logical and leaf
occurrences correspond. Such a judgment does not make a negative elaboration
positive. Analysis may price logical queries and leaf reads separately and may
bind a theorem to an exact source experiment. Structural success proves no
distance, soundness, knowledge, or zero-knowledge statement.

## 9. Closed outcomes

The checker and bounded evaluator distinguish:

```text
Unsupported
MissingDependency
CannotAnswer
KindMismatch
Malformed
Refused
DeterministicLimitExceeded
CheckerFailure
```

- `Unsupported` covers an unknown program constructor, algebra profile,
  algorithm semantics, or answer-adaptive query profile.
- `MissingDependency` covers an absent program, algorithm, contract, plan
  input, source Oracle, target value, occurrence, terminal, or authenticated
  preimage.
- `CannotAnswer` covers a supported live source read whose required entry is
  unavailable without asserting a semantic negative.
- `KindMismatch` covers a valid foreign profile/kind or unequal type and ABI.
- `Malformed` covers invalid carrier shape, duplicate map keys, noncanonical
  finite collections, and strict input-decode failure.
- `Refused` covers cycles, future dependencies, nonexhaustive routes, false
  bounds, composite prime-field carriers, declassification, dynamic occurrence
  creation, and map mismatch.
- `DeterministicLimitExceeded` covers exhaustion of the independent evaluator
  work limit before a completed outcome. It is not a Core rejection or a
  transcript event.
- `CheckerFailure` covers disagreement by a selected algorithm provider,
  checker, derived ABI, or request-local authenticated binding.

A source-declared quotient collision, absent tagged value, or other protocol
terminal is an ordinary completed target-Core branch, not a ninth operational
outcome. Incidental host exceptions and process timeouts may produce no record
at all; they cannot be converted into an affirmative, negative, or semantic
terminal result.

## 10. Canonical bodies and identity

All references below are typed and all maps use canonical key order.
`PIRAlgorithmUseBody` and `InteractiveCoreBody` retain their exact imported
Interaction meanings.

```text
VisibilityBody = V(0,Unit) | V(1,Unit)
// Public | VerifierOnly

ProgramAlgebraProfileBody = V(0,R{0:N(prime_modulus)})
// PrimeFieldV0; admission checks that prime_modulus is prime

ProgramLocalValueRefBody =
    V(0,U)
  | V(1,N(parameter_ref))
  | V(2,N(step_ref))

ProgramRouteInputRefBody = V(0,U) | V(1,N(parameter_ref))

ProgramParameterBody(x) = R {
  0: ValueTypeBody(x.value_type), 1: VisibilityBody(x.visibility)
}

ProgramOraclePortBody(x) = R {
  0: ValueTypeBody(x.index_type),
  1: ValueTypeBody(x.answer_type),
  2: VisibilityBody(x.visibility)
}

ProgramStepBody =
    V(0,R{0:PIRAlgorithmUseBody(algorithm),
          1:S[ProgramLocalValueRefBody(inputs)...],
          2:ValueTypeBody(result_type)})
  | V(1,R{0:N(source_port),1:ProgramLocalValueRefBody(index),
          2:ValueTypeBody(answer_type)})
  | V(2,R{0:ContentRef(program_id),
          1:ProgramLocalValueRefBody(requested_index),
          2:CanonicalTotalLocalValueMapBody(parameters),
          3:CanonicalTotalOrdinalMapBody(oracle_ports),
          4:ValueTypeBody(result_type)})

ProgramCaseOutcomeBody =
    V(0,ProgramLocalValueRefBody(result))
  | V(1,ProgramTerminalContractBody(terminal))

ProgramTerminalContractBody(x) = R {
  0: Q(x.outcome_label),
  1: TerminalVerdictBody(x.verdict)
}

ProgramCaseBody(x) = R {
  0: N(x.case_ordinal),
  1: S[ProgramStepBody(step)...],
  2: ProgramCaseOutcomeBody(x.outcome)
}

VerifierDerivedWordProgramBodyV0(x) = R {
  0: ValueTypeBody(x.index_type),
  1: ValueTypeBody(x.result_type),
  2: ProgramAlgebraProfileBody(x.algebra_profile),
  3: S[ProgramParameterBody(parameter)...],
  4: S[ProgramOraclePortBody(port)...],
  5: R{0:PIRAlgorithmUseBody(x.route.algorithm),
       1:S[ProgramRouteInputRefBody(input)...],
       2:ValueTypeBody(x.route.case_type)},
  6: S[ProgramCaseBody(case)...],
  7: VisibilityBody(x.output_visibility),
  8: N(x.maximum_elaboration_depth),
  9: N(x.maximum_leaf_reads)
}

QueryPlanValueRefBody = V(0,N(input_ref)) | V(1,N(prior_use_ref))

QueryPlanInputBody(x) = R {
  0: ValueTypeBody(x.value_type), 1: VisibilityBody(x.visibility)
}

QueryPlanOracleBody(x) = R {
  0: ValueTypeBody(x.index_type),
  1: ValueTypeBody(x.answer_type),
  2: VisibilityBody(x.visibility)
}

ActivationBody =
    V(0,Unit)
  | V(1,QueryPlanValueRefBody(public_boolean))

CanonicalTotalLocalValueMapBody(m) =
  S[R{0:N(child_parameter_ref),
      1:ProgramLocalValueRefBody(m[child_parameter_ref])} ...
    in dense child-parameter order]

CanonicalTotalOrdinalMapBody(m) =
  S[R{0:N(child_oracle_port_ref),
      1:N(m[child_oracle_port_ref])} ...
    in dense child-Oracle-port order]

CanonicalTotalPlanValueMapBody(m) =
  S[R{0:N(program_parameter_ref),
      1:QueryPlanValueRefBody(m[program_parameter_ref])} ...
    in dense program-parameter order]

LogicalQueryUseBody(x) = R {
  0: ContentRef(x.program_id),
  1: ActivationBody(x.activation),
  2: QueryPlanValueRefBody(x.requested_index),
  3: CanonicalTotalPlanValueMapBody(x.parameters),
  4: CanonicalTotalOrdinalMapBody(x.oracle_ports)
}

VerifierDerivedQueryPlanBodyV0(x) = R {
  0: S[QueryPlanInputBody(input)...],
  1: S[QueryPlanOracleBody(oracle)...],
  2: S[LogicalQueryUseBody(use)...]
}

ProgramPathComponentBody =
    V(0,N(case_ordinal))
  | V(1,N(step_ordinal))

ProgramPathBody(path) =
  S[ProgramPathComponentBody(component) ...]

RouteCaseMapBody(x) = R {
  0: N(x.route_value),
  1: S[R{0:N(case_ordinal),1:GuardBody(x.case_guards[case_ordinal])} ...
       in dense case order]
}

ProgramStepImageBody =
    V(0,N(derived_value_ref))
  | V(1,R{0:N(query_occurrence_ref),
          1:N(answer_occurrence_ref),
          2:ValueRefBody(answer_value)})
  | V(2,R{0:RouteCaseMapBody(child_route),
          1:CanonicalProgramStepImageMapBody(child_steps),
          2:CanonicalProgramResultMapBody(child_results),
          3:CanonicalProgramTerminalMapBody(child_terminals)})

CanonicalProgramStepImageMapBody(m) =
  S[R{0:ProgramPathBody(path),1:ProgramStepImageBody(m[path])} ...
    by complete ProgramPathBody bytes]

CanonicalProgramResultMapBody(m) =
  S[R{0:ProgramPathBody(return_case_path),
      1:ValueRefBody(m[return_case_path])} ...
    by complete ProgramPathBody bytes]

CanonicalProgramTerminalMapBody(m) =
  S[R{0:ProgramPathBody(terminal_case_path),
      1:N(m[terminal_case_path])} ...
    by complete ProgramPathBody bytes]

LogicalUseImageBody(x) = R {
  0: GuardBody(x.activation_guard),
  1: RouteCaseMapBody(x.route),
  2: CanonicalProgramStepImageMapBody(x.steps),
  3: CanonicalProgramResultMapBody(x.results),
  4: CanonicalProgramTerminalMapBody(x.terminals),
  5: S[R{0:ProgramPathBody(path),
         1:N(query_occurrence_ref),
         2:N(answer_occurrence_ref)} ...
       in exact logical leaf order]
}

CanonicalTotalValueRefMapBody(m) =
  S[R{0:N(plan_input_ref),1:ValueRefBody(m[plan_input_ref])} ...
    in dense plan-input order]

CanonicalTotalOracleRefMapBody(m) =
  S[R{0:N(plan_oracle_ref),1:N(m[plan_oracle_ref])} ...
    in dense plan-Oracle order]

CanonicalLogicalUseImageMapBody(m) =
  S[R{0:N(logical_use_ref),1:LogicalUseImageBody(m[logical_use_ref])} ...
    in dense logical-use order]

VerifierDerivedQueryElaborationBodyV0(x) = R {
  0: ContentRef(x.plan_id),
  1: ContentRef(x.target_core_id),
  2: CanonicalTotalValueRefMapBody(x.plan_inputs),
  3: CanonicalTotalOracleRefMapBody(x.plan_oracles),
  4: CanonicalLogicalUseImageMapBody(x.logical_uses)
}

VerifierDerivedQueryPlanDomainBodyV0(x) =
    V(0,VerifierDerivedWordProgramBodyV0(x))
  | V(1,VerifierDerivedQueryPlanBodyV0(x))
  | V(2,VerifierDerivedQueryElaborationBodyV0(x))
```

Program identity changes with route, cases, algorithms, types, visibility, or
semantic bounds. Plan identity changes with program IDs, formal ports, logical
order, activation, or bindings. Elaboration identity changes with the plan,
target Core, or any map entry. Runtime values, source citations, display names,
compiler routes, evidence, and evaluator budgets are excluded.

## 11. Admission order

Admission is deterministic and bounded:

1. authenticate the prior-meta basis, selected profile and exact import
   closure, subject ID/body, programs, algorithms, and contracts;
2. validate carrier shape, canonical collections, types, ABIs, and visibility;
3. validate local step availability, program dependency acyclicity, closed
   route partitions, and nonadaptive taint;
4. recompute exact depth and leaf bounds;
5. validate plan port coverage, logical order, activation, and cross-use taint;
6. authenticate and independently admit the target Core;
7. recursively derive the complete expected static elaboration;
8. validate every target value, guard, occurrence, terminal, and causal edge;
9. compare the total logical-use images and ordered leaf maps exactly; and
10. mint the inert affirmative handle only after every check succeeds.

`CheckVerifierDerivedQueryElaboration(` uses no caller-selected equality,
solver, optimizer, callback, or registry. An evaluator may memoize immutable
authenticated program expansion by exact ID, but a cache hit cannot skip
support or target-map validation.

## 12. Evidence and nonclaims

The bounded instrument under
[`evaluation/verifier-derived-query-plans/`](../../evaluation/verifier-derived-query-plans/README.md)
forms five programs and one plan, elaborates 62 static events, and executes
DEEP-ALI-shaped quotient, STIR-shaped branching/nested fold, batch
Circle-FRI-shaped combination, and WHIR-shaped grouped-fold cases. An
independently coded oracle reproduces all outputs and ordered leaf reads.
It also checks a two-use activation/prior-result plan against a nine-event
flat-Core body authored without importing the elaborator. Forty-one tests
exercise cycle, adaptivity, route, algebra, componentwise bounds, transitive
visibility, explicit terminals, map, Core substitution/reordering,
missing-source, multiplicity, and resource boundaries.

That evidence is finite inhabitance and falsification only. This page and the
instrument establish none of:

- exact correspondence to DEEP-ALI, STIR, Circle FRI, WHIR, or another paper;
- correctness of a source completion or collision disposition;
- proximity, soundness, completeness, knowledge, extraction, or zero
  knowledge;
- commitment binding, hiding, opening correctness, or BCS applicability;
- support for answer-adaptive, unbounded, or dynamically generated query
  structures;
- equivalence between logical query count, source-leaf count, and physical
  opening count;
- general target-Core formation or admission beyond the independently authored
  bounded activation-and-prior-result Core;
- implementation, MLIR, backend, or endpoint conformance; or
- production fitness or cryptographic security.

## 13. Reversal conditions

Reopen this boundary only if a source-faithful constructive case demonstrates
that one of the following is necessary:

1. source-answer-dependent routing that cannot be represented by a separately
   authenticated finite Core;
2. a logical derived read that must itself be a verifier-visible protocol
   event rather than a source-level explanation;
3. a finite source protocol whose required leaf occurrences cannot be fixed
   before Core authentication;
4. composition that cannot consume the exact checked elaboration as an
   additional operand without changing Core ownership;
5. commitment compilation that must authenticate a derived word rather than
   the actual source Oracles while preserving the source experiment; or
6. a necessary failure or visibility law that cannot be expressed through
   explicit Core guards, values, and terminals.

Performance preference, API convenience, repeated arithmetic, or the name
“virtual oracle” in a source is not reversal evidence.

<!-- zkc-profile-source:verifier-derived-query-plan-semantics:end -->
