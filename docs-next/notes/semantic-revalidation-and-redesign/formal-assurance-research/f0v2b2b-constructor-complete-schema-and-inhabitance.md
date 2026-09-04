# F0-V2B2B Constructor-Complete Schema and Inhabitance

> **Kind:** Temporary reopened-F0 schema-design and executable-inhabitance
> result
> **State:** Complete at schema resolution with
> `Affirmative/F0V2B2B-A-CONSTRUCTOR-COMPLETE-SCHEMA-INHABITANCE`; owner
> admission/projection and integrated semantic behavior remain B2C/B2D
> obligations; B2C1B1 has since completed four foundation projection families
> at bounded research resolution
> **Authority:** None. This note and its executable package do not change a
> PIR source, semantic profile, identity, evaluator, owner handle, compiler,
> runtime, or Analysis judgment
> **Predecessor:**
> [`F0-V2B2A constructor-closure census`](f0v2b2a-constructor-closure-census.md)
> **Executable gate:**
> [`evaluation/formal-source-view-schema-f0v2b2b`](../../../../evaluation/formal-source-view-schema-f0v2b2b/README.md)

## 1. Decision

The B2A census can be represented by one finite six-view source without a
catch-all reference, host reflection, semantic token catalog, or a new
top-level authority. The candidate keeps the existing ownership split:

```text
Interaction profile source
  -> five pir.interactive-core view schemas
  -> one Fresh pir.protocol ExecutionView schema
```

The scoped B2B claim is now affirmative: two independently structured source
compilers agree on the expanded schemas, and a schema-directed generator
inhabits every reachable constructor boundary accepted by two independently
structured validators.

This is deliberately a grammar result. The generated values are not claimed
to lie in the image of an admitted owner projection. B2C must establish that
stronger fact from immutable admitted handles; B2D must establish integrated
graph and runtime behavior.

## 2. Design correction found during B2B

The F0-V2A sequence constructor carried only `maximum_length`. That is too
weak for the normalized target bodies. It cannot distinguish:

```text
CanonicalSeq<T>
NonEmptyCanonicalSeq<T>
CanonicalSortedUniqueSeq<T>
```

The distinction is semantic enough to affect consumer safety. A max-only
schema accepts an empty scope path, an empty reduction input set, duplicate
`PCNode`s, duplicate edges, and reordered set-valued graph evidence. Owner
admission may reject those values later, but the view schema would no longer
state the boundary it claims to type.

B2B therefore revises the candidate structural node to:

```text
PIRViewSchema =
    Atom(PIRViewAtomSchema)
  | Record(CanonicalNonEmptySortedUniqueSeq<(field_ordinal, schema)>)
  | Variant(CanonicalNonEmptySortedUniqueSeq<(case_ordinal, schema)>)
  | Sequence {
      minimum_length: u64,
      maximum_length: u64,
      discipline: Ordered | SortedUnique,
      element_schema: PIRViewSchema
    }
```

This does not move collection semantics into a new kernel. It makes the
existing PIR-owned view declaration honest about its finite collection shape.
The selected profile still owns the concrete limits and the exact canonical
body functions used for ordering.

The executable package uses a deterministic JSON diagnostic encoding to
exercise `SortedUnique`. That is not the eventual owner ordering authority.
B2C must derive and compare order using the exact target body encodings.

## 3. Closed schema surface

The source has 88 named definitions and 453 source nodes. It binds all leaf
references to one sorted, closed body-compiler catalog and all law leaves to
one exact law catalog. Unknown, unused, cyclic, or open definitions refuse.

Relative to B1, B2B adds the complete structural surfaces below.

### 3.1 Public-coin structure

- `CoinCorrelation`: Independent and JointMember;
- `ReductionUse`: Exclusive and Shared;
- all fourteen `PCNode` cases;
- verifier-private, constant, derived-value, claim, reduction, module-control,
  and module-output node references;
- exact reduction consumers on each challenge; and
- lower-bound and sorted-unique collection declarations where required.

### 3.2 Decisions and effects

- message, Oracle, and module prover-move types;
- all ten `InteractiveCoreProverReadCoordinate` cases;
- deterministic Verifier message declarations;
- reduction invocation;
- Publish, Query, and Answer Oracle effects with Public and VerifierOnly
  visibility; and
- one opaque admitted-module-effect atom boundary.

The atom is intentionally opaque to generic traversal. Its schema checker
recognizes only its closed outer boundary. Exact module/declaration ownership,
payload schema, evaluator support, decision class, dependency edges, and
output visibility belong to admission and projection in B2C.

### 3.3 Owner projections

- Oracle declaration, publication occurrence, query, and answer entries in
  `EffectView`;
- supported extension entries;
- initial-binding and reduction-output claim creation;
- reduction-input and terminal-disposition claim use;
- complete reduction entries and publication requirements;
- terminal claim dispositions; and
- Published, Queried, and Answered Oracle receipt-schema branches in Fresh
  `ExecutionView`.

The Interaction-owned Execution schema remains Fresh-only. Canonical-framed
and duplex-sponge challenge receipt and interpretation-failure schemas belong
to their exact construction profiles and are not silently imported into the
Interaction schema.

## 4. Executable method

The package uses four independent axes rather than one large fixture.

### 4.1 Two source compilers

The reference compiler recursively expands named definitions while checking
the active dependency stack. The cold compiler first inspects every raw node,
constructs a definition dependency graph, resolves it in topological
worklist order, and expands each definition iteratively. They share no
compiler implementation. Their six expanded schema values and owner catalogs
are byte-identical under the package's diagnostic encoding.

### 4.2 Additive branch generation

A Cartesian product of all view fields would be large and would obscure what
was covered. The generator instead uses a baseline inhabitant and substitutes
one child suite at a time. It covers:

- every record node;
- every active variant arm;
- each atom's declared boundary values;
- the exact lower boundary of every sequence; and
- at least one nonempty value whenever the maximum permits one.

This produces 302 values over 914 path-specific requirements:

| View | Inhabitants | Requirements |
|---|---:|---:|
| PublicBindingView | 7 | 30 |
| StrategyDecisionView | 25 | 95 |
| PublicCoinView | 199 | 477 |
| EffectView | 36 | 149 |
| ClaimReductionView | 20 | 83 |
| ExecutionView | 15 | 80 |

Both validators accept every generated value. The reference validator is
recursive; the cold validator is an explicit worklist.

This is branch inhabitance, not exhaustive value enumeration. In particular,
it does not enumerate all 16,384-element sequences or all products of
independent branches.

### 4.3 Negative controls

Thirty source mutations cover owner/profile/predecessor substitution, source
identity, fields, tags, order, bounds, collection discipline, cycles, unused
definitions, compiler and law catalogs, and the module atom. All thirty change
both independently computed source identities. Twenty-five are malformed and
also fail both grammar compilers; five are well-formed alternate schemas and
are rejected by exact source identity.

Eighteen value mutations cover field omission/insertion/reordering, unknown
variant tags, missing payloads, empty nonempty sequences, upper-bound
overflow, sorted-unique duplication/reordering, compiler/body/law
substitution, natural and Boolean types, module-boundary shape, Unit, and
sequence kind. Both validators refuse all eighteen.

## 5. What the affirmative result means

The following statement is supported at this bounded research resolution:

> There exists one closed candidate description source for the normalized six
> PIR views that structurally represents every B2A repair family; two
> differently organized compilers agree on its expansion; and every reachable
> constructor branch has an accepted synthetic inhabitant under two
> differently organized validators.

This closes the risk that B2C would begin from an internally uninhabitable or
obviously incomplete view grammar. It also exposes source changes that would
otherwise be hidden behind an unchanged fixture.

It does not support any of the following stronger statements:

- every generated value comes from an admitted `InteractiveCore` or Protocol;
- every admitted owner has exactly one such value;
- the view derivation preserves owner meaning;
- the `PCGraph` edge, transfer, sink, or logical-access rules are correct;
- Fresh execution emits exactly the described runtime receipts;
- the current implementation derives or consumes these schemas;
- Interaction revision 0 already publishes this source;
- profile identity can remain unchanged; or
- any formal, relation, theorem, security, Fiat--Shamir, or Q1 claim holds.

## 6. B2C entry contract and B2C0 refinement

B2C0 has now executed the authority prerequisite. It found that the F1-R1B
handle is nonserializable but ordinarily mutable, and therefore cannot safely
be reused as the source of a later owner projection. The selected substrate
instead admits from exact canonical bytes into immutable, alias-free Core and
Fresh Protocol snapshots and pairs reconstructed dependency closures by
authenticated content. The scoped result and its remaining obligations are
recorded in
[`f0v2b2c0-canonical-byte-owner-admission.md`](f0v2b2c0-canonical-byte-owner-admission.md).

The exact-value prerequisite is now complete as B2C1A. It found that target
K1 bodies and diagnostic JSON disagree on one minimal sorted-unique PCNode
order and that identifier leaves require complete MetaValue framing. B2C1B1
has since applied this contract to the first four foundation families; two
projectors agree on 36 exact bodies over six carriers. The remaining seventeen
constructor-isolation families retain the following entry contract without
making B2C0, B2C1A, or B2C1B1 a new semantic stage or owner.

B2C1B should use the B2B source as a falsifiable candidate while deriving
values from owner state. It must not accept the generated B2B values as
fixtures. The minimum program is:

```text
exact authenticated immutable candidate
  -> extended offline admission
  -> immutable admitted Core handle
  -> reference owner projection
  -> six values conforming to B2B schemas

same admitted handle
  -> independently implemented projection
  -> byte-identical six values
```

For every B2A pressure family assigned to B2C, the gate must include one
small positive carrier and its named negative discriminator. Isolation comes
before integration: a large Core in which several mistakes compensate cannot
close a constructor family.

B2C must additionally establish:

1. exact owner-profile and Core/Protocol bearer pairing;
2. intrinsic immutability rather than merely process-local handle identity;
3. exact canonical ordering through target body encodings;
4. source-complete admission for Oracle, claim, reduction, and supported
   module declarations;
5. total derivation of all five Core views in one owner-local operation;
6. separately derived Fresh `ExecutionView` from the paired Protocol;
7. rejection of every named isolation mutation; and
8. `CannotAnswer`, not a guessed value, for any constructor whose owner law is
   still underspecified.

The preferred implementation topology remains an extension of the offline
target evaluator and existing owner handles. B2C should not introduce an
`FSKernel`, transcript-root authority, portable view ID, runtime registry, or
semantic MLIR token.

## 7. B2D handoff

B2C may prove isolated edge and transfer facts needed to admit each carrier,
but B2D owns their integrated closure:

- all `PCNode` families in one admitted graph;
- complete edge construction and deterministic topological order;
- all four `PCClass` outcomes;
- terminal-preemption control edges;
- Oracle origin/mode/visibility interactions;
- logical-access influence and acceptance intersection;
- claim/reduction/challenge interaction; and
- Fresh runtime Oracle receipt arity, type, visibility, and backlinks.

Only after B2C and B2D should F0-V2C decide profile publication and migration.
The B2B source is evidence for that decision, not authority to pre-commit it.
