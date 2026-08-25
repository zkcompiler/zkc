# Relations

> **Document kind:** Domain index
> **Document state:** Active target-domain index
> **Provisional owner:** `relations`
> **Authority:** None during the transition. Current relation semantics remain
> governed by the [Relations specification](../../docs/spec/relations.md).
> **Closure interpretation:** This index records a selected package-resolution
> target. `Selected`, `target`, and `exact` describe intended role, scope, and
> ownership; they do not assert integrated definition closure or semantic
> freeze. The [v0 Semantic Design Program](../project/v0-design-program.md#14-progress-and-change-control)
> owns the live gate.

## Purpose

`relations/` owns zkc's boundary to already formed relations. Stage 2 divided
that boundary into three non-collapsible contracts: relation-interface
admission, optional relation-artifact interpretation, and post-admission
correspondence to an exact Protocol Interface. Stage 3 selected a candidate
ontology, identity, binding, grounding, checking, outcome, and replay model at
its package resolution. Stage 4A then assigned candidate occurrence-local
relation satisfaction semantics to Relations. Integrated closure remains
reopened. Subject admission and correspondence still do not imply that zkc
compiled the predicate, generated a satisfying witness, or established
satisfaction.

## Owns

- relation-interface candidate, identity, semantic regime, schema, admission,
  immutable capability, and lifecycle;
- relation artifact references, exact format profiles, and artifact
  interpretation observations kept separate from interface admission;
- public-instance encoding and ABI;
- witness-port declarations and interface roles;
- anchors and their protocol-facing projection;
- `RelationCorrespondsAtInterface` over exact admitted Protocol, Protocol
  Interface, relation Interface, `RelationBinding`, `CorrespondenceQuestion`,
  conditionally required checked artifact-comparison/grounding prerequisites,
  exact source bindings, and correspondence regime;
- adapter contracts and the explicitly bounded interface facts they may
  produce;
- computed, cross-checked, and asserted classifications, affirmative and
  negative correspondence, retained agreements, residual obligations, and
  non-claims, without creating a parallel trust taxonomy;
- an admitted `RelationSemanticModel` plus occurrence-local
  `CheckRelationSatisfaction` with exact model, assumptions, basis, qualified
  polarity, confidential witness authority, and replay boundary; and
- a provisional later ownership slot for verifier-to-relation descent only
  after Stage 4B activates and supplies its exact admitted OIR/result contract.

Format-specific profiles, such as an R1CS reader, are separate change
boundaries from the generic relation contract even if both remain in this
domain.

## Does not own

- relation-source languages or relation compilation;
- external predicate truth, satisfiability, model faithfulness, or witness
  existence beyond one exact completed `CheckRelationSatisfaction` result;
- witness generation, storage, secrecy, or endpoint/runtime witness
  capabilities beyond the one holder-issued occurrence-local capability that
  `CheckRelationSatisfaction` consumes for its exact semantic check;
- protocol transcript or claim-flow semantics;
- cryptographic property judgments about a protocol;
- endpoint execution or deployment; or
- broad compatibility claims for external relation ecosystems.

Reader and adapter implementations are conformance subjects. Their observed
behavior belongs in evidence, not in the normative relation contract.

Declaring a witness port describes an interface. Relations consumes one fresh
holder-issued local witness capability only inside
`CheckRelationSatisfaction`; it neither generates nor stores the witness and
the capability dies with that checking occurrence. Supplying and consuming a
witness for endpoint or downstream runtime execution belongs to Realization and
invocation.

## Dependencies

- `foundation/` for identity, admission, encoding, and version rules;
- `pir/` definitions when specifying exact protocol anchor or statement
  correspondence; and
- conditionally after Stage 4B activation, exact admitted `oir/` subjects and
  checked results for verifier-to-relation descent.

Current relation admission, correspondence, and satisfaction have no OIR
dependency. The provisional descent slot imports nothing until its later owner
defines and admits the exact OIR/result contract.

The relation itself remains external. A digest or adapter result identifies and
describes a boundary; it does not establish the predicate it names.

Authentication verifies the independently identified relation-interface
candidate and its exact dependency closure. Admission then checks the complete
relation-interface predicate and mints only local authority over the admitted
interface. Interpreting later bytes may form an exact observation without
changing the relation interface or Protocol. Interpretation is expectation-
free and has no negative disagreement outcome. A separate artifact/interface
comparison owns affirmative agreement or well-formed negative disagreement.
Only the still-later correspondence checker consumes that checked comparison
when requested and yields an affirmative or negative
`RelationCorrespondenceJudgment`.

## Consumers and outputs

- Protocol/PIR supplies an exact admitted Protocol and a narrow PIR-owned
  correspondence view; statement wiring additionally cites the exact admitted
  `ProtocolInterfaceId`. Attaching a relation interface or interpreting bytes
  does not change Protocol or Interface identity;
- property analysis may consume authenticated relation facts only through an
  explicit subject projection;
- OIR endpoint programs and realization consume public and private interface
  roles;
- the compiler may require relation-facing prerequisites without owning them;
  and
- evidence records adapter behavior and correspondence checks at exact scope.

## Bridge ownership

`relations/` first owns direct authentication and admission of one closed
relation-interface subject. It separately owns interpretation of immutable
artifact bytes under an exact format adapter. That adapter may produce bounded
facts and unread declarations; a separate checked comparison may produce
bounded agreements, disagreements, and residual obligations. Neither can mint
relation truth or Protocol authority.

`relations/` then owns `RelationCorrespondsAtInterface`, which consumes exact
admitted Protocol, admitted Protocol Interface, admitted relation interface,
admitted `RelationBinding`, exact `CorrespondenceQuestion`, conditionally
required `CheckedArtifactInterfaceComparison` and
`CheckedCommittedObjectGrounding`, complete source bindings with separately
supplied fresh capabilities, and correspondence regime. A raw observation
cannot substitute for either checked prerequisite. The bridge
establishes only its named agreements and obligations, preserves all source
identities, and returns an affirmative or negative judgment. Missing
authority, malformed input, or an unsupported question is not a negative
correspondence. PIR owns both Protocol and Interface and defines their narrow
authenticated views; Relations owns their correspondence interpretation.

Relations separately owns `CheckRelationSatisfaction`. It consumes one exact
admitted semantic model and instance plus an occurrence-local private witness.
Its affirmative or negative capability applies only to that witness occurrence,
model, assumptions, basis, and process generation. It is not implied by
admission or correspondence and does not become a public witness identifier.
Analysis may consume the exact result but cannot redefine it.

`relations/` also provisionally owns endpoint descent because the output gains
the semantic role of relation material. Endpoint identity and verifier behavior
remain under `oir/`.

## Target documents

- [Selected Protocol and Relations Architecture](../project/protocol-and-relations-architecture.md)
- [Selected Analysis and Compiler Architecture](../project/analysis-and-compiler-architecture.md)
- [Relation Model](relation-model.md)
- [Protocol Correspondence](protocol-correspondence.md)
- [Protocol Interfaces and Prover Plans](../pir/interfaces-and-plans.md)

These pages are durable non-normative Stage 3 and Stage 4A candidate targets at
their package resolution. The current Relations specification under `docs/`
remains authoritative until explicit normative consolidation and cutover.

## Reopened integrated-closure and later-owner questions

Stage 3 selected relation-interface identity and admission,
occurrence-indexed instance/witness assignments, value bridges, artifact
observation and comparison, committed-object grounding, and Protocol
correspondence at its then-current package resolution. Stage 4A selected the
generic relation-satisfaction ownership, model, outcome, confidentiality, and
replay contract and reconciled its candidate Analysis/Compiler ingress.
Post-selection revalidation reopened the exact grounding equations, fact
algebra and selectors, reachable checked prerequisites, relation-facing
Witness surface, lossless equivalence and embedding, priced lossy projection,
and directional result meaning. After those pre-freeze questions close, later
owners must still define:

- any relation-source compilation language or checked source-to-definition
  relation;
- concrete admitted definition-language/model correspondence profiles and
  satisfaction checker implementations;
- exact Analysis family rules that consume relation and correspondence facts
  without widening their checked scope;
- verifier-to-relation descent after OIR semantics exist; and
- normative encodings, compatibility, implementation correspondence, and
  migration during Stages 7 and 8.
