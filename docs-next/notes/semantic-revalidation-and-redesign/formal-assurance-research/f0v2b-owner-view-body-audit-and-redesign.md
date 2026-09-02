# F0-V2B0 Owner-View Body Audit and Redesign

> **Kind:** Temporary reopened-F0 owner-body audit and replacement contract
> **State:** Complete at source-audit resolution with
> `CannotAnswer/F0V2B0-C-OWNER-BODY-DETERMINACY`. The generic F0-V2A algebra
> is retained, but the six current displays cannot be compiled verbatim into
> exact target schemas. A normalized replacement is selected for F0-V2B1
> authoring and bounded derivation. F0-V2B1 has since validated that bounded
> method. F0-V2B2A has since closed the constructor census and work topology;
> B2B schema/inhabitance has since completed; executable B2C/B2D owner and
> integrated semantic closure remains open
> **Authority:** None. This note changes no PIR source, profile manifest,
> revision, semantic identity, evaluator, owner handle, or Analysis result
> **Predecessor:**
> [`F0-V2A canonical schema design`](f0v2-canonical-view-schema-design.md)
> **Executable source audit:**
> [`evaluation/formal-source-view-body-audit-f0v2b0`](../../../../evaluation/formal-source-view-body-audit-f0v2b0/README.md)

## 1. Outcome

F0-V2B0 finds that the remaining problem is not mechanical expansion of six
record displays. The current source has three classes of defect:

1. **undefined schema vocabulary:** `PIRReference`, `ProverViewCoordinate`, and
   `guard_ref` have no exact body or owner definition;
2. **prose-valued fields:** producer coordinates, producer edges, creation and
   consumer coordinates, resolver coordinates, and run-record schema are named
   without closed grammars; and
3. **semantic mismatch:** Section 11 says the finite public-coin node/edge
   tables and final classes are retained in `PublicCoinView`, but the displayed
   `PublicCoinViewBody` has no fields for them.

An exact compiler that follows only the display would omit owner meaning. An
implementation that follows all surrounding prose would have to invent fields,
paths, and stopping points not authenticated by the profile. The correct
result is therefore `CannotAnswer`, not a best-effort grammar.

The audit selects a normalized replacement body family rather than preserving
every display field. In particular:

- `ValueRef` is already the exact value-producer coordinate, so a second
  `value_origin` or unspecified complete-producer coordinate is removed;
- a decision carries its exact scope path and complete guard, not undefined
  `scope_ref`/`guard_ref` surrogates;
- the complete retained `PCGraph` result becomes explicit source data in
  `PublicCoinView`;
- declaration records remain structurally traversable where current consumers
  select their interior fields;
- one admitted module effect remains an opaque semantic atom;
- Fresh resolver and completed-record schemas receive exact PIR-owned
  description bodies; and
- all five Core views are derived together from one normalized ephemeral owner
  fact index.

This is a main-design correction. It will rotate the Interaction profile when
published; it is not an implementation-only clarification.

## 2. Evidence method

The audit compared four source classes:

1. the exact `InteractiveCore`, `Protocol`, declaration, execution, and
   `PCGraph` laws in `docs-next/pir/interactive-core.md`;
2. Appendix A canonical bodies on that page;
3. every current Analysis, Relations, and Interface/Plan selection of the six
   owner views; and
4. the exact F1-R1B admitted finite Core/Protocol carrier and its explicitly
   unsupported constructor surface.

The check was field-by-field. For each displayed value it asked:

```text
owner source
  -> stored or uniquely derived value
  -> exact semantic type
  -> exact canonical body or schema-description body
  -> structural versus atomic stopping point
  -> current consumer path
  -> full-constructor executable coverage
```

A display label, English phrase, host dataclass, K2 token, or consumer alias is
not an answer to any missing edge.

The frozen executable audit reproduces this classification as 18/18 findings:
five affirmative source prerequisites, ten `CannotAnswer` obligations, and
three refused repair routes. It freezes exact source-fragment, consumer,
manifest, and fixture digests so later source movement requires review rather
than silently changing the result. This remains a lexical and structural
source audit, not a parser, evaluator, derivation proof, or target repair.

## 3. Global findings

### 3.1 The Core and Protocol sources are adequate

The identity-bearing owner data is not the problem. Appendix A gives exact
bodies for all fourteen `InteractiveCore` fields, both `Protocol` fields, and
the stored declarations. Admission also defines unique occurrence ordinals,
scope structure, effect backlinks, value availability, visibility, claims,
reductions, terminals, and supported module behavior.

The six views may therefore be derived without adding fields to `CoreId` or
`ProtocolId`. What is missing is the exact schema and normalization contract
for those derived facts.

### 3.2 Atomicity must follow consumer semantics

F0-V2A deliberately used representative atoms. F0-V2B0 refines their target
use. The following are semantic atoms:

```text
content-addressed semantic ID
typed declaration/reference value
Core-local ordinal reference
ValueRef
ValueType
CanonicalValue at its exact ValueType
exact profile-law declaration reference
complete admitted ModuleEffectRef
```

The following must remain structural because current consumers select their
interior fields:

```text
scope/view entries
Challenge declaration and derived challenge entry
Check declaration and occurrence backlink
Terminal declaration, disposition, and occurrence backlink
claim and reduction entries
decision points and guaranteed-read entries
occurrence schedule entries
Fresh resolver and completed-record type descriptions
```

For example, Analysis forms separate coordinates for a Challenge's
`challenge_ref`, `domain`, `fresh_law`, `correlation`, and public conditions.
Relations selects one Check's algorithm, evaluation contract, and inputs and
one Terminal's verdict, required checks, and dispositions. Treating an entire
Challenge, Check, or Terminal body as one generic canonical-body atom would
make those current source questions unformable.

### 3.3 One normalized owner index should drive all five Core views

The selected internal operation is:

```text
DeriveCoreStaticFactIndex(exact AdmittedCore C) = {
  core_id,
  scope_paths,
  value_types,
  occurrence_backlinks,
  occurrence_output_types,
  decision_points,
  guaranteed_prover_reads,
  claim_creation_and_use,
  pc_graph_result,
  supported_extension_results
}
```

Every component is deterministically derived under existing Core admission and
the exact supported module declarations retained by the handle. The index is
finite, immutable, process-local, and unidentifiable. It has no canonical body,
ID, authority, serialization, cache key, or consumer input. The five view-body
compilers are fixed projections from this index plus the exact stored Core.

This index is not a new kernel. It is the shared implementation-independent
definition of facts that the current source already assigns to PIR. The public
contract remains the five view values and their existing coordinates.

## 4. Field-by-field audit

### 4.1 Public binding

| Current field | Source status | F0-V2B disposition |
|---|---|---|
| `core_id` | Exact admitted handle | Retain as `CoreId` atom |
| `scope_ref`, `parent`, `opening` | Exact stored sequence ordinal and `ScopeBody` fields | Retain structurally |
| `complete_scope_path` | Unique parent-chain derivation, no current body | Define `NonEmptyCanonicalSeq<ScopeRef>` |
| `binding_ref`, `scope_ref`, `class`, `value_ref` | Exact stored declaration plus ordinal | Retain structurally |
| `value_type` | Unique `ValueTypeOf(ValueRef)` after admission | Retain as derived `ValueType` atom |
| `value_origin` | Duplicates the exact `ValueRef` constructor and is underspecified about payload | Remove |
| `complete_value_producer_coordinate` | `ValueRef` already is the complete producer coordinate | Remove rather than define a second alias |

The normalized body is:

```text
PublicBindingViewBody = {
  core_id: CoreId,
  scopes: CanonicalSeq<{
    scope_ref: ScopeRef,
    parent: None | Some(ScopeRef),
    opening: ScopeOpening,
    scope_path: NonEmptyCanonicalSeq<ScopeRef>
  }>,
  bindings: CanonicalSeq<{
    binding_ref: BindingRef,
    scope_ref: ScopeRef,
    class: PublicBindingClass,
    value_ref: ValueRef,
    value_type: ValueType
  }>
}
```

This still supplies the exact Relations `StatementOccurrenceTable` without
copying a second producer identity.

### 4.2 Strategy decisions

The display's `scope_ref` loses the complete path used by the actual decision
law, and `guard_ref` has no Core type because guards are inline occurrence
values. `ProverViewCoordinate` is also undefined; the owner type is
`InteractiveCoreProverReadCoordinate`.

The normalized body is:

```text
PIRProverMoveType =
    MessageMove(ValueType)
  | OracleMove(OracleRef, OracleCarrierType, OraclePublicationMode)
  | ModuleMove(AdmittedModuleEffectBoundary, exact module move ValueType)

StrategyDecisionViewBody = {
  core_id: CoreId,
  decision_points: CanonicalSeq<{
    decision_ref: ProverDecisionPointRef,
    occurrence_ref: exactly decision_ref,
    scope_path: NonEmptyCanonicalSeq<ScopeRef>,
    guard: exact Guard,
    move_type: PIRProverMoveType,
    prior_decision_refs: CanonicalSeq<ProverDecisionPointRef>
  }>,
  prover_view_formation_law:
    exact PIRProfileLawReference,
  guaranteed_prover_reads: CanonicalSeq<{
    decision_ref: ProverDecisionPointRef,
    read: InteractiveCoreProverReadCoordinate,
    value_type: ValueType
  }>,
  legal_move_types: CanonicalSeq<{
    decision_ref: ProverDecisionPointRef,
    move_type: PIRProverMoveType
  }>
}
```

Maps are represented by canonical sequences of exact entries. The owner law
requires total key coverage and strict order. `prior_decision_refs` means every
earlier Prover decision in occurrence order; guaranteed visibility of a prior
move remains a separate `PriorOwnMove` read result.

### 4.3 Public coin

The displayed challenge fields are mostly recoverable, but two displayed
closures lack exact definitions and the complete retained graph evidence is
absent. The normalized owner result is:

```text
PIRPCGraphResult = {
  nodes: CanonicalSortedUniqueSeq<PCNode>,
  edges: CanonicalSortedUniqueSeq<{ source: PCNode, target: PCNode }>,
  topological_order: CanonicalSeq<PCNode>,
  classes: CanonicalSeq<{ node: PCNode, class: PCClass }>,
  sinks: CanonicalSortedUniqueSeq<PCNode>,
  acceptance_sinks: CanonicalSortedUniqueSeq<PCNode>,
  logical_access_influence: CanonicalSeq<{
    oracle_ref: OracleRef,
    cone: CanonicalSortedUniqueSeq<PCNode>,
    acceptance_intersection: CanonicalSortedUniqueSeq<PCNode>
  }>
}

PublicCoinViewBody = {
  core_id: CoreId,
  graph: PIRPCGraphResult,
  structural_public_coin_eligibility: MetaBoolean,
  verifier_private_predecessors: CanonicalSortedUniqueSeq<PCNode>,
  challenges: CanonicalSeq<{
    challenge_ref: ChallengeRef,
    occurrence_ref: OccurrenceRef,
    scope_ref: ScopeRef,
    value_type: ValueType,
    domain: ProtocolDeclarationRef<"pir.challenge-domain">,
    fresh_law: ProtocolDeclarationRef<"pir.public-coin-law">,
    correlation: CoinCorrelation,
    reduction_use: ReductionUsePolicy,
    public_conditions: CanonicalSeq<ValueRef>,
    public_condition_predecessors: CanonicalSortedUniqueSeq<PCNode>,
    reduction_consumers:
      CanonicalSeq<{ reduction_ref: ReductionRef,
                     challenge_ref: exactly this challenge_ref }>
  }>
}
```

`verifier_private_predecessors` is exactly every
`VerifierPrivateInputNode(i)` that reaches one sink. The public-condition
predecessor set is the graph predecessor closure of the corresponding value
producer nodes, including those producers themselves. These definitions
replace the two prose closures.

The graph fields make the Section 11 retention claim true and independently
checkable. The final eligibility Boolean remains a useful conclusion, but it
can no longer substitute for its derivation surface.

### 4.4 Effects and values

The current display combines schedule, declaration catalogs, backlinks, value
types, and extension resolution. Each is derivable, but phrases such as
`exact producer edges` and `exact admitted extension declaration` are not body
grammars.

The normalized body is:

```text
PIREffectOccurrenceEntry = {
  occurrence_ref: OccurrenceRef,
  scope_path: NonEmptyCanonicalSeq<ScopeRef>,
  guard: exact Guard,
  effect: exact CoreEffect, with ModuleEffectRef one opaque admitted atom,
  output_types: CanonicalSeq<ValueType>
}

PIRValueEntry = {
  value_ref: ValueRef,
  value_type: ValueType,
  direct_predecessors: CanonicalSeq<ValueRef>
}

EffectViewBody = {
  core_id: CoreId,
  occurrence_schedule: NonEmptyCanonicalSeq<PIREffectOccurrenceEntry>,
  values: CanonicalSeq<PIRValueEntry>,
  messages: CanonicalSeq<{
    occurrence_ref: OccurrenceRef,
    message_kind: Prover | DeterministicVerifier,
    declaration: structurally exact message declaration
  }>,
  oracles: CanonicalSeq<{
    oracle_ref: OracleRef,
    declaration: structurally exact Oracle declaration,
    publication_occurrence: OccurrenceRef,
    queries: CanonicalSeq<OccurrenceRef>,
    answers: CanonicalSeq<OccurrenceRef>
  }>,
  checks: CanonicalSeq<{
    check_ref: CheckRef,
    algorithm: PortableAlgorithmRef,
    evaluation_contract: EvaluationContractId,
    inputs: CanonicalSeq<ValueRef>,
    occurrence_ref: OccurrenceRef
  }>,
  terminals: CanonicalSeq<{
    terminal_ref: TerminalRef,
    verdict: TerminalVerdict,
    public_outputs: CanonicalSeq<ValueRef>,
    required_true_checks: CanonicalSeq<CheckRef>,
    claim_dispositions: CanonicalSeq<(ClaimRef,ClaimDisposition)>,
    occurrence_ref: OccurrenceRef
  }>,
  supported_extensions: CanonicalSeq<{
    occurrence_ref: OccurrenceRef,
    effect: AdmittedModuleEffectAtom
  }>
}
```

`direct_predecessors` is empty for invocation inputs and constants, equals the
declared inputs of a derived value, and equals the declaration-owned ordered
dependency list for an occurrence output. It is not the complete read closure;
F1-R1C2 computes transitive question-relative closure over these exact edges
and the exact control/scope/guard edges.

The Check and Terminal records deliberately remain structural because current
Relations and Analysis source questions select their interior fields.

### 4.5 Claims and reductions

The stored declarations are exact. The missing parts are normalized creation,
use, publication, and disposition coordinates:

```text
PIRClaimCreationCoordinate =
    InitialBinding(BindingRef, exact scope-opening boundary)
  | ReductionOutput(OccurrenceRef, ReductionRef, output_ordinal)

PIRClaimUseCoordinate =
    ReductionInput(OccurrenceRef, ReductionRef, input_ordinal)
  | TerminalDisposition(OccurrenceRef, TerminalRef, disposition_ordinal)

ClaimReductionViewBody = {
  core_id: CoreId,
  claims: CanonicalSeq<{
    claim_ref: ClaimRef,
    contract: ProtocolDeclarationRef<"pir.claim-contract">,
    scope_ref: ScopeRef,
    usage: ClaimUsage,
    source: ClaimSource,
    creation: PIRClaimCreationCoordinate,
    consumers: CanonicalSeq<PIRClaimUseCoordinate>
  }>,
  reductions: CanonicalSeq<{
    reduction_ref: ReductionRef,
    contract: ProtocolDeclarationRef<"pir.reduction-contract">,
    scope_ref: ScopeRef,
    occurrence_ref: OccurrenceRef,
    input_claims: NonEmptyCanonicalSeq<ClaimRef>,
    side_inputs: CanonicalSeq<ValueRef>,
    required_challenges: CanonicalSeq<ChallengeRef>,
    required_publications:
      CanonicalSeq<ReductionPublicationRequirement>,
    output_contracts:
      CanonicalSeq<ProtocolDeclarationRef<"pir.claim-contract">>
  }>,
  terminal_dispositions: CanonicalSeq<{
    occurrence_ref: OccurrenceRef,
    terminal_ref: TerminalRef,
    claim_ref: ClaimRef,
    disposition: ClaimDisposition
  }>
}
```

This preserves the complete publication requirements required by Relations
and Analysis. It does not copy a theorem, relation satisfaction result, or
runtime claim state into PIR meaning.

### 4.6 Fresh execution

The first three fields are exact stored/identified values and the four law
fields can be exact fixed profile-law atoms. Two fields still need new owner
types.

```text
PIRFreshResolverCoordinate = {
  challenge_ref: ChallengeRef,
  occurrence_ref: OccurrenceRef,
  value_type: ValueType,
  domain: ProtocolDeclarationRef<"pir.challenge-domain">,
  fresh_law: ProtocolDeclarationRef<"pir.public-coin-law">,
  public_conditions: CanonicalSeq<ValueRef>,
  prior_joint_members: CanonicalSeq<ChallengeRef>
}

PIRRuntimeSchema = the same finite Record/Variant/Sequence/Atom description
  universe selected by F0-V2A, in its runtime-type application

ExecutionViewBody = {
  protocol_id: ProtocolId,
  core_id: CoreId,
  challenge_interpretation: exactly Fresh,
  visible_history_law: ExactProfileLawAtom,
  resolver_coordinates: CanonicalSeq<PIRFreshResolverCoordinate>,
  generated_execution_law: ExactProfileLawAtom,
  completed_record_schema: PIRRuntimeSchema,
  interpretation_failure_schema: exactly None,
  replay_qualification_law: ExactProfileLawAtom,
  relation_run_view_issuance_law: ExactProfileLawAtom
}
```

The completed-record description expands the exact Fresh `RunRecord` fields,
all occurrence output arities/types, Fresh challenge receipts, Oracle receipts,
terminal references, and terminal public-output types. It describes a typed
runtime value; it does not create a canonical transport encoding, content ID,
portable receipt, or authority.

Canonical-framed and duplex profiles own distinct Execution schema entries.
They replace the resolver and profile receipt/failure descriptions under their
own profile identities. Interaction's Fresh entry cannot type an FS run record.

## 5. Why direct Appendix-A projection is insufficient

One alternative is to expose the complete `InteractiveCoreBody` and let every
consumer derive its own tables. That is rejected for three reasons:

1. it duplicates PIR's scope, visibility, backlink, PCGraph, decision, and
   claim-liveness derivations in every consumer;
2. a consumer could omit a control or module dependency and still present a
   well-formed projection; and
3. it would erase the existing lifecycle in which PIR issues a capability over
   owner-derived facts.

Appendix A remains the exact stored source. The normalized views are checked
owner projections from that source and its admission-retained derivations.
They are not consumer-side reimplementations.

## 6. Why K2 tokens do not solve this gap

The older K2 token/catalog experiment can name a bounded top-level projection,
but it does not define the complete nested fields, active variant paths,
sequence elements, semantic atom boundaries, or retained PCGraph evidence.
Adding one token per display field would simply move the handwritten schema
into an untyped token table.

Tokens may remain useful as compiler-internal scheduling or witness labels.
They do not replace the authenticated schema, generic resolver, or exact owner
derivation selected here.

## 7. Full-constructor coverage gap

The exact F1-R1B subject is sufficient to exercise:

- public input and Statement binding;
- root scope;
- Prover message decisions;
- one Fresh Challenge;
- one deterministic Check;
- guarded Accept and fallback Reject terminals; and
- Fresh Protocol formation.

It intentionally has no verifier-private inputs, constants, derived values,
child scopes, Oracles, claims, reductions, joint/shared challenges, verifier
messages, or module effects. Its evaluator also explicitly returns qualified
noncompletion for several of those branches.

F0-V2B cannot claim complete target grammar or derivation from that one subject.
The next gate must therefore separate:

```text
F0-V2B1  exact normalized source grammar and bounded F1-R1B derivation
F0-V2B2A constructor census and execution topology
F0-V2B2B complete schema source and inhabitance
F0-V2B2C isolated admitted carriers and owner projections
F0-V2B2D integrated carrier and complete graph pressure
F0-V2C   target publication, identity migration, and old-profile controls
```

F0-V2B2 may use admitted synthetic carriers under a deliberately extended
offline evaluator, but it must not call them current implementation support.
At minimum it must cover one child scope, verifier-private dead input, constant,
derived value, verifier message, each Oracle mode/origin/lifecycle, initial and
reduction-output claims, one reduction with before/after-challenge publication
requirements, joint/shared challenge structure, and one supported module
effect with an opaque payload.

The subsequent
[`F0-V2B1 bounded result`](f0v2b1-bounded-normalized-view-grammar.md)
matches 63/63 findings. Two source compilers and two owner derivations agree on
six values, 329 leaves, two decisions, seven guaranteed reads, and one retained
21-node/27-edge bounded PCGraph. B2-only families are maximum-zero sequences,
so this result validates the selected method without closing this
constructor-complete gap.

The subsequent
[`F0-V2B2A census`](f0v2b2a-constructor-closure-census.md) matches 44/44
findings and authenticates 79 closed source/derived cases plus twenty-three
pressure families. It validates the B2A work census only; complete schemas,
inhabitance, extended admission, owner projection, and integrated graph
closure remain B2B/B2C/B2D obligations.

## 8. Required source declarations

F0-V2B1 must publish source-bound body compilers or exact schema declarations
for at least:

```text
PIR finite description nodes and atoms
every normalized six-view body above
scope path and all new entry records
PIRProverMoveType
InteractiveCoreProverReadCoordinate body
PCClass and PIRPCGraphResult
PIRClaimCreationCoordinate and PIRClaimUseCoordinate
PIRFreshResolverCoordinate
PIRRuntimeSchema body
complete-manifest and path/boundary bodies
fixed law atoms and common resolver/enumerator laws
```

Every referenced existing body compiler must be listed in the exact schema
entry dependency closure. The source must identify whether a semantic type is
structural or atomic. A phrase such as `exact X`, an imported Markdown anchor,
or a source-language type name is not a body compiler.

## 9. Migration and compatibility

These normalized bodies intentionally differ from the F0-V1 topology-only
candidate and the current displays. F0-V2C must therefore:

1. advance Interaction's explicit local revision;
2. rebuild the six schema declarations with the F0-V2B bodies;
3. rotate the exact sixteen-profile cone already measured by F0-V1;
4. update F1-R1A/B/C old-profile controls without relabelling old bytes;
5. publish sibling construction/result view schemas only in their owner
   profiles; and
6. require both publication implementations to reconstruct identical bodies,
   dependency closures, and IDs.

No compatibility edge is implied. A later checked compatibility relation may
compare old and new owner views for one purpose, but old profile bytes cannot
be reinterpreted under the new grammar.

## 10. F0-V2B1 executable entry contract and result

The next bounded gate should:

- import the exact F1-R1B admitted Core and Fresh Protocol handles;
- derive all six normalized values without caller-authored view fields;
- compile the exact F0-V2B1 schemas through the recursive and iterative F0-V2A
  algorithms;
- compare two separately implemented owner derivations;
- resolve every concrete atomic leaf and require the exact complete manifest;
- freeze all six schema/manifest identities;
- mutate each stored source, derived backlink, scope path, type, law,
  PCGraph edge/class, decision read, Check/Terminal interior field, resolver
  coordinate, and completed-record type; and
- retain `CannotAnswer` for every F0-V2B2-only constructor.

An affirmative bounded-slice result does not close F0-V2B. F0-V2B closes only
after the constructor-complete profile passes or the target explicitly narrows
its supported semantics.

F0-V2B1 now satisfies this entry contract at bounded resolution. It additionally
refuses mutation of a retained Core under its old bearer and substitution of a
different live Core bearer into the Fresh Protocol pair. The target
implementation contract must therefore make retained admitted state
intrinsically immutable and preserve exact Protocol/Core bearer pairing.

## 11. Decision

Retain the F0-V2A generic schema algebra, but do not encode the six current
displays verbatim. Author the normalized bodies in Section 4, starting with
the exact F1-R1B slice and then a constructor-complete offline falsifier.

The fail-closed audit result is:

```text
current exact Core/Protocol stored bodies                 Affirmative
generic structural/atomic schema method                   Affirmative/F0-V2A
consumer-required target leaf granularity                 determinate
current six displayed bodies as exact canonical schemas  CannotAnswer
normalized replacement selected for authoring             Affirmative/F0-V2B0
bounded normalized grammar and derivation                 Affirmative/F0-V2B1
exact target grammar and complete derivation              open/F0-V2B2
target profile publication and migration                  open/F0-V2C
```

## 12. Non-claims

This audit does not repair the target, define every canonical field ordinal,
admit a new Core, implement PCGraph for all constructors, derive a view, form a
source capability, establish Q1, verify a compiler, validate a formal provider,
or prove a cryptographic property. It selects the exact owner-body direction
and records why copying the current displays would be unsound.
