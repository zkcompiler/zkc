# PIR Semantic Profile Publication

> **Document kind:** Target semantic specification and publication index
> **Document state:** Active non-normative target
> **Provisional owner:** `pir`
> **Authority:** None during the transition. Current normative protocol
> semantics remain under [`docs/`](../../../docs/README.md).

## 1. Purpose

This directory publishes the complete owner source for the six stable upstream
PIR semantic-language profiles and two dependent PIR profiles. A strict source
manifest and the exact marked fragments in its durable owner pages compile to
one complete six-field Foundation `SemanticLanguageProfileBody`. Identity
tables are derived output; two independent compilers reproduce them, and they
never participate in a profile preimage.

The published graph is:

```text
pir.interaction
|- pir.canonical-framed-fiat-shamir
|- pir.duplex-sponge-fiat-shamir
`- pir.public-setup
   `- pir.commitment-opening
      `- pir.oracle-commitment

(pir.interaction + pir.canonical-framed-fiat-shamir)
  `- pir.interface-plan

(pir.interaction + pir.canonical-framed-fiat-shamir
 + pir.interface-plan + oir.endpoint-graph)
  `- pir.endpoint-source-view
```

The display elides direct-use diamonds. Commitment opening directly imports
both Interaction and public setup. Oracle commitment directly imports
Interaction, public setup, and commitment opening.

## 2. Source artifacts

The source artifacts are:

| Key | Owner-source manifest | Durable semantic owner |
|---|---|---|
| `interaction` | [`interaction.json`](interaction.json) | [`interactive-core.md`](../interactive-core.md) |
| `canonical-framed-fiat-shamir` | [`canonical-framed-fiat-shamir.json`](canonical-framed-fiat-shamir.json) | [`fiat-shamir.md`](../fiat-shamir.md) |
| `duplex-sponge-fiat-shamir` | [`duplex-sponge-fiat-shamir.json`](duplex-sponge-fiat-shamir.json) | [`duplex-sponge-fiat-shamir.md`](../duplex-sponge-fiat-shamir.md) |
| `public-setup` | [`public-setup.json`](public-setup.json) | [`interactive-core.md`](../interactive-core.md) |
| `commitment-opening` | [`commitment-opening.json`](commitment-opening.json) | [`commitment-opening-verification.md`](../commitment-opening-verification.md) |
| `oracle-commitment` | [`oracle-commitment.json`](oracle-commitment.json) | [`oracle-commitment-construction.md`](../oracle-commitment-construction.md) |
| `interface-plan` | [`interface-plan.json`](interface-plan.json) | [`interfaces-and-plans.md`](../interfaces-and-plans.md) |
| `endpoint-source-view` | [`endpoint-source-view.json`](endpoint-source-view.json) | [`endpoint-projection-views.md`](../endpoint-projection-views.md) |

[`published-identities.json`](published-identities.json) records the derived
body length, body SHA-256, full typed content-reference bytes, and profile-ID
digest for the six frozen v0 artifacts. The owner-neutral publication gate
reconstructs and can print the complete indexed graph, including the two
dependent PIR rows. Those values are conformance results, not source inputs or
independent semantic claims.

## 3. Frozen v0 owner-source manifest

Every manifest is strict JSON with exactly these fields:

```text
ProfileSourceManifestV0 = {
  format: "zkc.pir.semantic-profile-source.v0",
  key: ExactAsciiSymbol,
  profile_family: ExactAsciiSymbol,
  revision: u64,
  owner_page: RepositoryRelativePath,
  expected_imports: CanonicalSeq<profile key>,
  supported_subject_kinds: CanonicalSortedUniqueSeq<ExactAsciiSymbol>,
  fragments: CanonicalSeq<FragmentSource>,
  definitions: CanonicalSeq<DefinitionSource>,
  subjects: CanonicalSeq<SubjectLanguageSource>
}
```

The two dependent manifests use the owner-qualified v1 edition defined by
[Semantic Profile Publication](../../foundation/semantic-profile-publication.md).
That edition moves `owner_page` into each fragment and fixes the local catalog
namespace explicitly; it does not reinterpret or upgrade the v0 rows below.

`owner_page` and marker names are build coordinates and are excluded from the
compiled profile. Each `FragmentSource` names one unique start marker and end
marker in the owner page. The exact bytes strictly between the marker lines,
after removal of the single structural LF adjacent to each marker, are the
identity-bearing fragment. The bytes must be nonempty NFC UTF-8, use LF only,
contain no trailing horizontal whitespace, and end in exactly one LF. Moving
an unchanged marked fragment or its page therefore preserves identity;
changing bytes inside the fragment rotates the profile.

`DefinitionSource` has exact fields `kind`, `name`, `revision`, `fragment`,
`selector`, and `dependencies`. The common interpretation kinds are
`pir.body-compiler`, `pir.semantic-law`, `pir.evaluator-signature`, and
`pir.failure-schema`; an owner may also publish a closed profile-local kind
whose interpretation is selected by its source-bound law, such as an FS
receipt-schema kind.
`fragment` names a local fragment and `selector` is nonempty NFC UTF-8 that
must occur in that fragment. A dependency is an exact local or imported
declaration coordinate `{profile, kind, name}`; `profile = "self"` selects the
manifest being compiled. No host function, generated identifier, digest, or
unresolved label is a definition.

`SubjectLanguageSource` has exact fields `kind`, `body_compiler`, `laws`,
`evaluator`, and `failure_schema`. Its `kind` sequence must equal the manifest's
supported-kind set exactly. Every reference resolves before a profile can
form.

## 4. Exact generated catalogs

Compilation creates these sorted-unique declaration catalogs:

```text
SourceFragmentBodyV0 = R {
  0: Q(name), 1: N(0), 2: Y(exact_fragment_bytes)
}

DefinitionBodyV0 = R {
  0: Q(name),
  1: N(revision),
  2: ProfileDeclarationRefBody(local pir.source-fragment ordinal),
  3: Y(selector_utf8),
  4: S[ProfileDeclarationRefBody(dependency) ...]
}

SubjectLanguageBodyV0 = R {
  0: Q(subject_kind),
  1: ProfileDeclarationRefBody(body_compiler),
  2: S[ProfileDeclarationRefBody(law) ...],
  3: ProfileDeclarationRefBody(evaluator),
  4: ProfileDeclarationRefBody(failure_schema)
}
```

Fragment declarations use manifest fragment order. Explicit definition
ordinals use manifest order within each declaration kind. Generated
`pir.subject-language` declarations use ascending subject-kind bytes. Catalog
kinds themselves use ascending ASCII bytes. A local reference resolves only in
the profile being formed. An imported reference contains the full typed ID of
one already compiled direct import and resolves against that exact preimage.

Every profile contains the following common catalog kinds:

```text
pir.body-compiler
pir.evaluator-signature
pir.failure-schema
pir.semantic-law
pir.source-fragment
pir.subject-language
```

The `pir.source-fragment` and `pir.subject-language` catalogs are generated.
The other four common catalogs must be nonempty in every artifact. A manifest
may add only explicitly populated `pir.*` owner-local catalogs. Their bodies
use `DefinitionBodyV0`, and at least one reachable definition must cite each
extension declaration. There is no empty, ambient, or dynamically registered
catalog.

## 5. Structured law-source body

The profile's `semantic_law_source` is the Foundation encoding `M` of:

```text
PIRLanguageProfileLawSourceV0 = R {
  0: N(0),
  1: S[PIRDirectImportUseBody ... by imported ContentRefV0 bytes],
  2: S[R{0:Q(subject_kind),
         1:ProfileDeclarationRefBody(local subject-language declaration)} ...],
  3: S[ProfileDeclarationRefBody(local evaluator signatures) ...],
  4: S[ProfileDeclarationRefBody(local failure schemas) ...],
  5: S[]
}
```

Field 5 is the exact empty sequence because this publication represents every
selected law through a source-bound catalog declaration. It cannot contain a
copy of a declaration body.

Each `PIRDirectImportUseBody` is `R{0:Y(ContentRefV0(import)),1:S[uses...]}`.
A use is one of:

```text
V(0, ProfileDeclarationRefBody(imported dependency))
V(1, R{0:Q(subject_kind),
       1:ProfileDeclarationRefBody(imported body compiler)})
V(2, ProfileDeclarationRefBody(imported evaluator signature))
V(3, ProfileDeclarationRefBody(imported failure schema))
```

The compiler derives this table from imported references in explicit
definitions and generated subject-language declarations. It also derives the
profile import set. `expected_imports` must equal that set exactly; it cannot
add a transitive-only, unused, or merely convenient edge. Use bodies are
ordered by their complete Foundation encoding and are unique.

## 6. Compilation and identity

The six Foundation profile fields are:

```text
profile_family          = manifest.profile_family
revision                = manifest.revision
profile_imports         = derived direct imports, by ContentRefV0 bytes
supported_subject_kinds = manifest set, by ASCII bytes
declaration_catalogs    = Section 4
semantic_law_source     = M(Section 5)
```

Profiles compile in topological order. Cyclic imports, unresolved references,
self-imports, duplicate names, unknown fields, absent selectors, unreferenced
definitions, catalog-shape disagreement, source-limit violations, or any
expected/derived import disagreement refuse publication and produce no ID.
The complete selected-root closure is the graph-reachable set including the
root, with no extra profile preimages.

The bounded evaluator at
[`evaluation/semantic-profile-publication/`](../../../evaluation/semantic-profile-publication/README.md)
contains a Foundation-backed reference compiler and a cold compiler with an
independent datum encoder, prior-meta reconstruction, profile-reference
framing, source extraction, graph traversal, and profile hashing. Agreement is
required over complete profile-body bytes, full content-reference bytes,
derived imports and uses, exact root closures, and the identity table.

## 7. Scope and change rule

This publication closes the PIR-owned profile preimages for the eight rows in
Section 2. It does not publish the OIR projection relation, Relations,
Analysis, Compiler, Realization, Evidence, a cryptographic theorem, or an
implementation-conformance profile. The complete cross-domain publication set
is indexed by Foundation.
A change to the source format, catalog grammar, law-source grammar, extraction
normalization, or compiler interpretation requires a new explicit publication
format. Existing bytes are never reinterpreted under a changed compiler.
