# F0-V2 Canonical PIR View-Schema Design

> **Kind:** Temporary reopened-F0 architecture decision and executable-gate
> contract
> **State:** Schema architecture selected and F0-V2A bounded feasibility gate
> complete with `Affirmative/F0V2A-A-SCHEMA-ALGEBRA-FEASIBLE`. Exact target
> source grammar, profile publication, identity migration, owner-view
> derivation, and partial read closure remain open
> **Authority:** None. This note does not change PIR, a semantic profile, an
> identity, an evaluator, or an Analysis judgment
> **Predecessors:**
> [`F1-R1C0`](f1r1c-owner-view-source-determinacy.md) and
> [`F0-V1`](f0v-owner-view-publication-repair-design.md)

## 1. Decision

F0-V2 should use one finite, PIR-owned universe of view descriptions and one
generic resolver/enumerator. It should not expand the six current displays
into six unrelated handwritten path walkers, reuse Foundation value schemas as
if they described semantic view decomposition, or preserve the undefined
catch-all `PIRReference` boundary.

The selected shape is:

```text
exact admitted Core handle
  -> one simultaneous derivation of all five complete Core view values
  -> one authenticated schema entry per view component
  -> one generic schema/value conformance check
  -> one generic active-leaf enumerator and exact path resolver
  -> the canonical complete manifest

exact admitted Protocol handle
  -> one complete Execution view derivation
  -> the same schema, conformance, enumeration, and resolution machinery
```

The simultaneous Core derivation is an ephemeral owner operation, not a new
identified subject or authority. Each issued view retains its existing owner
coordinate, owner binding, and fresh capability. The common operation merely
prevents five independently authored derivations from disagreeing about shared
Core facts.

The schema universe is structural only at explicitly declared `Record`,
`Variant`, and `Sequence` nodes. Everything else stops at an exact semantic
atom. In particular, an admitted `ModuleEffectRef` is one authenticated opaque
atom in v0. Generic traversal never reflects into its declaration-typed
payload.

This is the strongest design that fits the existing owner/profile/capability
architecture without adding a Foundation kernel, a portable view identity, a
runtime registry, or a semantic token.

The executable F0-V2A package under
[`evaluation/formal-source-view-schema-f0v2a/`](../../../../evaluation/formal-source-view-schema-f0v2a/README.md)
now passes 40/40 frozen findings. Recursive and independently coded iterative
paths agree on six representative schema and complete-manifest digests, 52
active leaves, the single opaque module-effect coordinate, and three distinct
coordinates carrying one equal `ValueRef` value. Twenty-seven mutations fail
closed through both paths. Four findings intentionally remain `CannotAnswer`:
the exact target bodies, owner derivation, target migration, and proper-subset
closure. This validates the architecture as the input to F0-V2B; it does not
close F0-V2.

The subsequent
[`F0-V2B0 owner-body audit`](f0v2b-owner-view-body-audit-and-redesign.md)
finds that the current six displays cannot simply instantiate this algebra:
they contain undefined vocabulary and prose-valued fields, and the displayed
`PublicCoinView` omits retained PCGraph evidence. F0-V2B0 therefore selects
normalized replacement bodies for B1/B2 authoring while retaining this
algebra and its generic algorithms.

## 2. Why the current text is not executable

The current Interaction source already states several important invariants:

- paths contain only field, active-variant, and concrete-sequence steps;
- a coordinate ends at exactly one atomic leaf;
- complete owner bodies, not consumer tuples, define the view;
- a manifest is exact, sorted, unique, and closure-complete; and
- law-valued fields resolve to exact profile declarations.

Four gaps prevent an independent implementation from reconstructing the same
coordinate set:

1. `PIRReference` is listed as an atomic boundary but has no definition.
2. the six displayed bodies contain phrases such as `exact producer edges`,
   `resolver_coordinates`, and `run_record_schema` rather than closed nested
   grammars;
3. no authenticated description says which existing semantic bodies are
   traversed and which remain atomic; and
4. the effect carrier contains a dynamically declaration-typed module payload,
   so a generic host-language walk is neither complete nor owner-correct.

The problem is therefore not just missing field ordinals. It is the absence of
one finite description language fixing the semantic stopping points.

## 3. Candidate comparison

| Candidate | Strength | Structural defect | Disposition |
|---|---|---|---|
| **G-A: six expanded body grammars and six walkers** | Direct and initially local | Duplicates traversal, sorting, bounds, variant, map, and atom rules; makes cross-view disagreement likely | Reject |
| **G-B: Foundation `DeclarationValueType` as the view schema** | Existing finite record/variant/sequence grammar and canonical bounds | Describes values in nominal domains, not where a semantic view must stop; cannot directly type law refs, owner refs, or authenticated effect payloads | Reject as the outer grammar; embed its admitted `ValueType` only as an atom |
| **G-C: PIR description universe plus generic algorithms** | One exact traversal contract, explicit semantic atoms, reusable by Interface and later profiles | Requires a small new PIR-owned grammar and exact source publication | **Select** |
| **G-D: reflect over host records/dataclasses** | Little source text | Implementation layout becomes semantic authority; unknown and extension fields are silently interpreted | Reject |
| **G-E: top-level/K2 token catalog** | Easy bounded projections | A token names only a chosen slice and cannot prove complete nested source coverage or dependency closure | Reject |
| **G-F: Foundation-wide generic view kernel** | Cross-domain reuse if many owners converge | Prematurely moves PIR-specific atoms, derivation, and failures into Foundation | Defer unless at least one independent non-PIR owner needs the same contract |

G-C follows a well-established formal-method pattern without importing any
external theorem: define a small universe of descriptions, implement generic
operations once, and keep a relation between the description and concrete
data. Generic programming over description universes motivates the single
traversal structure; verified-format work shows why the format should drive
validators and serializers rather than merely document them. See
[Generic Programming with Dependent Types](https://people.cs.nott.ac.uk/psztxa/publ/ssgp06.pdf),
[EverParse3D](https://www.normalesup.org/~ramanana/research/everparse/pldi2022/paper.pdf),
and [Narcissus](https://www.cs.purdue.edu/homes/bendy/papers/Narcissus/narcissus.pdf).
Those systems do not verify this PIR design; they justify the shape of the
falsifiable boundary.

## 4. Selected description universe

### 4.1 Structural nodes

The provisional source-level algebra is:

```text
PIRViewSchema =
    Atom(PIRViewAtomSchema)
  | Record(CanonicalNonEmptySortedUniqueSeq<{
      field_ordinal: u64,
      schema: PIRViewSchema
    }>)
  | Variant(CanonicalNonEmptySortedUniqueSeq<{
      case_ordinal: u64,
      schema: PIRViewSchema
    }>)
  | Sequence({
      element_schema: PIRViewSchema,
      maximum_length: u64
    })
```

The tree is finite and acyclic. Field and case ordinals are strictly
increasing. Variants are nonempty. `Option`, maps, tuples, and tagged unions
are represented only by these constructors:

```text
Option<T>       = Variant { 0: Atom(Unit), 1: T }
Tuple<T0,...>   = Record  { 0: T0, ... }
CanonicalMap<K,V>
                = Sequence(Record { 0: K, 1: V }, maximum_length)
```

The selected profile fixes constitutional schema-node, depth, sequence, and
encoded-body limits. The initial proposal should reuse Foundation's existing
outer caps where they are applicable, but those values remain PIR profile
meaning and must be published explicitly. Merely fitting a Foundation
`FiniteSchema` does not form a PIR view schema.

### 4.2 Semantic atoms

The atom sum is intentionally small:

```text
PIRViewAtomSchema =
    UnitAtom
  | NaturalAtom(maximum)
  | MetaBooleanAtom
  | MetaSymbolAtom(maximum_bytes)
  | BytesAtom(maximum_bytes)
  | CanonicalBodyAtom(PIRViewLeafBodyCompilerRef)
  | CanonicalValueAtom
  | ExactProfileLawAtom(PIRProfileLawReference)
  | AdmittedModuleEffectAtom
```

`PIRViewLeafBodyCompilerRef` is an exact declaration in the selected owner
profile or one exact direct import. It names a closed canonical body function,
not executable plugin code. The profile catalog must enumerate every compiler
reference used by its schemas. Representative compilers include exact bodies
for `CoreId`, `ProtocolId`, local PIR references, `ValueRef`, `ValueType`,
Foundation declaration references, semantic module references, algorithm and
evaluation-contract references, and other already admitted semantic atoms.

This replaces the undefined `PIRReference` with an authenticated, typed, and
enumerable set. Two reference types with the same bytes but different body
compiler declarations remain different boundaries.

`CanonicalValueAtom` carries its exact admitted `ValueType` in the concrete
field boundary. The schema does not infer a type from host data or a nearby
text name.

`ExactProfileLawAtom(expected)` accepts only the one exact declaration
reference embedded in the schema. This makes the field-to-law map part of the
field grammar rather than a second table that can drift. Replacing
`core-admission-v0` with another well-formed law is therefore a schema/value
refusal, not an untyped proposition substitution.

`AdmittedModuleEffectAtom` covers the complete admitted `ModuleEffectRef`:
module ID, exact `"pir.core-effect"` declaration reference, and payload. Its
atom checker:

1. requires the exact module and declaration to agree;
2. resolves the declaration in the authenticated module closure;
3. requires evaluator support for that exact effect declaration;
4. strictly validates the payload under the declaration's owner schema; and
5. preserves the complete effect value as one leaf.

It does not enumerate payload children. A future effect-specific projection
requires an owner-published adapter with its own schema, derivation law, and
profile identity. This preserves the extension boundary already used by Core
admission and avoids treating arbitrary `MetaValueV0` as self-describing PIR
meaning.

### 4.3 Concrete boundaries and coordinates

The schema atom and admitted leaf instantiate one exact boundary:

```text
PIRViewAtomicBoundary =
    UnitBoundary
  | NaturalBoundary(maximum)
  | MetaBooleanBoundary
  | MetaSymbolBoundary(maximum_bytes)
  | BytesBoundary(maximum_bytes)
  | CanonicalBodyBoundary(PIRViewLeafBodyCompilerRef)
  | CanonicalValueBoundary(exact ValueType)
  | ExactProfileLawBoundary(exact PIRProfileLawReference)
  | AdmittedModuleEffectBoundary(
      exact SemanticModuleId,
      exact ModuleDeclarationRef<"pir.core-effect">)
```

The full field coordinate remains `(view coordinate, nonempty path,
boundary)`. The profile ID in the view coordinate authenticates the schema and
leaf-compiler catalog. No separate schema ID is necessary. A profile change
rotates the coordinate's profile component and cannot reinterpret an old
path.

## 5. One generic algorithm family

### 5.1 Schema admission

`AdmitPIRViewSchema` checks:

- exact constructor tags and fields;
- strict field/case ordering and uniqueness;
- finite depth, node count, encoded size, and sequence maxima;
- reachability and kind of every leaf-body compiler and law reference;
- no recursive host object, wildcard, callback, reflection marker, or unknown
  atom;
- exact owner subject and view-kind association; and
- exact source binding of the schema declaration selected by the profile.

### 5.2 View conformance

`Conforms(schema,value,owner_context)` is structural:

- a record has exactly the declared fields;
- a variant has exactly one declared active case;
- a sequence length is within its declared bound and every element conforms;
- a primitive atom fits its exact bound;
- a canonical-body atom round-trips through its exact body compiler;
- a canonical value is already admitted at its carried exact type;
- an exact law atom equals the declaration fixed in the schema; and
- a module-effect atom passes the authenticated effect admission above.

No default, ignored field, alternate tag, or best-effort decoding exists.

### 5.3 Active-leaf enumeration

For a conforming concrete view, `EnumeratePIRViewLeaves` walks fields in
ordinal order, the one active variant arm, and sequence elements in ascending
ordinal order. It emits exactly one coordinate/value pair at each atom. Empty
sequences emit no leaf. Repeated equal values at distinct paths remain distinct
coordinates.

This operation supplies the exact meaning needed by current downstream
`ExactPIRAtomicLeavesUnder`. Selecting a subtree means filtering the already
formed active coordinates by an exact structural path prefix; it is not a
field-name lookup or a second walk over a consumer shape.

### 5.4 Exact path resolution

`ResolvePIRViewField` independently follows the supplied steps through the
same authenticated schema and concrete view. It requires:

- `Field` only at a record;
- `VariantCase` equal to the active case only at a variant;
- `SequenceElement` within the concrete sequence only at a sequence;
- a nonempty path ending exactly at an atom; and
- the supplied boundary equal to the atom's instantiated boundary.

The required cross-check is:

```text
EnumeratePIRViewLeaves(schema,value)
  = CanonicalMap {
      c -> ResolvePIRViewField(schema,value,c)
      for every enumerated coordinate c
    }
```

and every non-enumerated candidate path refuses.

### 5.5 Complete manifest

For F1-R1C1:

```text
CompletePIRStaticViewManifest(schema,value) =
  canonical coordinate sequence of EnumeratePIRViewLeaves(schema,value)
```

The issued manifest must equal this sequence exactly. Missing, extra,
duplicate, reordered, cross-view, interior, wrong-arm, out-of-range, and
wrong-boundary entries refuse. A well-formed proper subset is
`Unsupported(PartialProjectionNotYetPublished)` until F1-R1C2 supplies the
constructor dependency graph.

## 6. Owner derivation architecture

### 6.1 Core views

The five Core entries should cite one dedicated law, provisionally
`core-static-view-family-derivation-v0`, plus one fixed component selector:

```text
DeriveCompleteCoreViewFamily(exact AdmittedCore C) = {
  public_binding: complete PublicBindingViewBody,
  strategy_decision: complete StrategyDecisionViewBody,
  public_coin: complete PublicCoinViewBody,
  effect: complete EffectViewBody,
  claim_reduction: complete ClaimReductionViewBody
}
```

The result is immutable and process-local. It has no content ID, authority,
portable bearer, or consumer-supplied field. The five components must share
the exact `CoreId`, and every repeated owner fact must be derived from one
normalized owner index inside the operation. Issuance selects one component
only after the complete family conforms to all five authenticated schemas.

This all-components conformance gate is deliberate. A bug in a dormant view
cannot leave the same Core partly valid under one owner-profile revision.
Deterministic limits may prevent the family operation from completing, but a
consumer cannot request a cheaper partial derivation and thereby evade a
failing sibling schema.

If complete-family materialization is later too expensive, a verified
streaming implementation may preserve the same all-components judgment. That
is an implementation refinement, not a weaker semantic operation.

### 6.2 Execution view

Execution remains Protocol-qualified and uses a separate exact
`protocol-execution-view-derivation-v0` law. Its body must contain exact
declaration references for visible-history, generation, replay, and run-view
issuance laws; an exact closed resolver-coordinate grammar; and the exact run
record schema. A Fresh and Fiat-Shamir Protocol sharing one Core therefore
still produce distinct owner coordinates and potentially distinct execution
views.

### 6.3 Construction and FS-result views

Canonical-framed and duplex profiles may reuse the structural universe and
generic algorithms, but they own their schema entries, atom-compiler
inventories, derivation laws, and authority families. No Interaction catalog
entry silently types a family-local construction or result body.

## 7. Publication shape

F0-V1's six `pir.static-view-schema` entries remain the right profile topology,
but F0-V2 strengthens each conceptual declaration to:

```text
PIRStaticViewSchemaDeclaration = {
  view_kind,
  owner_subject_kind,
  schema: PIRViewSchema,
  derivation_law: PIRProfileLawReference,
  component_selector,
  leaf_body_compilers:
    CanonicalSortedUniqueSeq<PIRViewLeafBodyCompilerRef>,
  resolver_law: exact common PIRProfileLawReference,
  complete_manifest_law: exact common PIRProfileLawReference,
  partial_closure_law:
    None | Some(exact PIRProfileLawReference),
  binding_payload_compiler,
  capability_requirement_compiler,
  no_policy_compiler,
  policy_closure_compiler
}
```

The earlier separate `law_field_bindings` map is removed: every fixed law leaf
is an `ExactProfileLawAtom` in the schema. The earlier per-view
`full_snapshot_derivation_law` is shared across the five Core entries and
paired with a closed selector. These are design corrections discovered during
F0-V2, not compatible reinterpretations of the F0-V1 synthetic bodies.

The profile's existing source-bound `DefinitionBodyV0` mechanism may still
publish these declarations. It authenticates exact source selectors and
dependencies; the selected source must now contain the complete grammar above
rather than only display records.

## 8. Failure partition

| Condition | Required result |
|---|---|
| Unknown profile, view family, or exact supported module-effect semantics | `Unsupported` |
| Missing schema, leaf compiler, law declaration, module, or effect declaration | `MissingDependency` |
| Formed reference targets the wrong profile kind, declaration kind, owner, or semantic regime | `KindMismatch` |
| Invalid schema encoding, duplicate/unsorted ordinal, unknown node, callback/reflection marker, malformed value, wrong path shape, inactive arm, interior endpoint, wrong boundary, or noncanonical manifest | `Malformed` |
| Well-formed value violates its exact owner schema, fixed law, exact effect contract, all-component agreement, or exact manifest equality | `Refused` |
| Exact complete view is requested but only proper-subset closure is unavailable | complete view proceeds; a proper subset is `Unsupported(PartialProjectionNotYetPublished)` |
| Declared structural or evaluation bound is crossed | `DeterministicLimitExceeded` |
| Advertised compiler, resolver, or evaluator violates its exact contract | `CheckerFailure` |

Missing evidence never becomes a negative semantic answer. A failed view
cannot mint a binding or capability.

## 9. F0-V2 executable gates

### F0-V2A — schema-kernel feasibility

Before target source changes:

- encode all four structural nodes and every selected atom class;
- build one representative conforming value for each of the six Interaction
  view kinds;
- cover nested records, active variants, empty/nonempty sequences, repeated
  equal values, exact law atoms, canonical-body atoms, canonical values, and
  an opaque admitted module effect;
- implement structurally independent recursive and iterative
  validator/enumerator/resolver paths;
- freeze schema digests and complete manifests; and
- reject schema, value, path, boundary, manifest, law, and extension-boundary
  mutations through both paths.

An affirmative F0-V2A result establishes only that the selected algebra and
generic algorithms are sufficient for the representative structures. It does
not establish the exact six target bodies or any owner derivation.

**Result:** complete at research resolution with
`Affirmative/F0V2A-A-SCHEMA-ALGEBRA-FEASIBLE`. The two paths agree on all 52
representative leaves and refuse all 27 selected mutations. The four named
target obligations remain `CannotAnswer`, so F0-V2B is now the next gate.

### F0-V2B — exact normalized six-body grammar

- translate every field in the current six displays into the selected
  structural universe;
- eliminate every prose placeholder;
- enumerate every leaf-body compiler dependency;
- publish exact fixed law atoms;
- prove that every Appendix-A reuse is either recursively described or one
  explicit semantic atom; and
- run two implementations over exact F1-R1B owner values.

F0-V2B must stop with `CannotAnswer` for any field whose exact owner source is
still missing. It may not fill a gap from K2 or an Analysis consumer.

**F0-V2B0 result:** the current displays do contain such gaps. The dedicated
audit returns `CannotAnswer/F0V2B0-C-OWNER-BODY-DETERMINACY`, selects normalized
replacement bodies, and splits completion into B1 exact bounded-slice
authoring and B2 constructor-complete derivation pressure.

**F0-V2B1 result:** the bounded candidate source now compiles identically
through recursive and worklist paths, while algorithmic and finite-oracle
owner derivations agree on six values and 329 active leaves. Its 63/63 result
validates the normalized method only. Maximum-zero B2-family sequences,
general PCGraph transfers, target publication, implementation correspondence,
and partial closure remain explicitly open.

**F0-V2B2A result:** the authenticated constructor census contains 79 closed
source/derived cases and measures twenty absent B1 variant cases plus eight
maximum-zero references. Its 44/44 result selects B2B schema/inhabitance, B2C
isolated admission/projection, and B2D integrated graph gates; all executable
constructor-closure claims remain `CannotAnswer`.

### F0-V2C — target publication and migration

- update the Interaction source and profile manifest coherently;
- split the authority-envelope compilers selected in F0-V1;
- advance explicit local revisions;
- reconstruct all profile identities through both publication compilers;
- retain old-profile substitution controls; and
- rerun profile publication, link, public-tree, F1-R1A, F1-R1B, and F1-R1C0
  gates.

Only F0-V2C changes target semantics. F1-R1C1 starts only after it succeeds.

## 10. F1 and F2 implications

The selected schema architecture strengthens the later program without
turning it into a proof:

- F1-R1C1 can compare a producer's complete manifest against a generic
  independently enumerated manifest rather than a hand-maintained field list.
- F1-R1C2 can add dependency edges over stable atomic coordinates; it need not
  redefine paths or leaf identity.
- F1-R1D can place exactly those coordinates and values in the neutral formal
  source package.
- F1-I can compare live implementation issuance with the same admitted owner
  operation and schema profile.
- F2 provider encodings can be generated from an exact source package while
  remaining untrusted until a provider-specific correspondence check succeeds.

No result here verifies a verifier, compiler, Fiat-Shamir transform, or
cryptographic property. It makes the source side of such later claims
falsifiable and independently reconstructible.

## 11. Reversal conditions

Reopen this choice if one of the following is demonstrated:

- a required current consumer must read a strict subfield of an authenticated
  module-effect payload and no owner-specific adapter can express it;
- one of the six exact bodies requires genuine recursive data rather than a
  constitutionally bounded finite tree;
- all-components Core-view validation makes authorized complete-view issuance
  infeasible under realistic deterministic limits and a streaming equivalent
  cannot preserve the same judgment;
- a second independent owner needs the exact same atom and failure calculus,
  justifying promotion of the generic subset into Foundation; or
- a stable portable view identity is required by a real workflow rather than
  only by the research package.

Absent one of those findings, adding a new kernel, token authority, portable
snapshot subject, or host-reflection lane would increase trust and migration
cost without increasing the claim supported by F1.

## 12. Non-claims

This note selects a description architecture. It does not yet define the exact
six target schemas, authenticate their source, rotate the Interaction profile,
derive a Core or Protocol view, form an exact read manifest, establish source
correspondence, validate an exporter, verify a compiler, or prove a theorem.
