# Semantic Profile Publication

> **Document kind:** Target semantic specification and source-corpus index
> **Document state:** Active non-normative target
> **Provisional owner:** `foundation`
> **Authority:** None during the transition. This page defines a reusable
> publication mechanism; each semantic domain owns the meaning and source of
> its profiles. Current normative specifications remain under
> [`docs/`](../../docs/README.md).

## 1. Boundary

Foundation owns how a finite domain profile is reconstructed from exact owner
source, not what that profile means. A domain owns its profile family,
supported subjects, body compilers, semantic laws, evaluator signatures,
failure schemas, and direct uses of other profiles. The repository publication
index names the complete source corpus but is a build coordinate, not a global
runtime registry or an identity preimage.

The selected mechanism has two source editions:

- `zkc.pir.semantic-profile-source.v0` is the frozen PIR-specific edition used
  by the six already published upstream PIR profiles. Its interpretation and
  bytes do not change.
- `zkc.semantic-profile-source.v1` is the owner-qualified edition used by new
  PIR, OIR, Relations, and Analysis profiles. It adds one
  `catalog_namespace` field and uses law-source version `1`.

No artifact is silently upgraded between editions. An existing v0 manifest
continues to compile with namespace `pir` and law-source version `0`; changing
its format is a profile rotation even if its owner fragments are unchanged.

## 2. Complete source-corpus index

[`semantic-profile-manifests.json`](semantic-profile-manifests.json) is strict
JSON with exactly:

```text
SemanticProfileManifestIndexV0 = {
  format: "zkc.semantic-profile-manifest-index.v0",
  manifests: CanonicalSeq<{
    key: ExactAsciiSymbol,
    source: RepositoryRelativePath
  }>
}
```

Keys and source paths are unique. Sequence order is a stable presentation
order only; compilers derive the topological order from exact direct imports.
`RepositoryRelativePath` is a canonical nonempty POSIX-style relative path over
printable non-space ASCII. Absolute paths, backslashes, control or whitespace
bytes, empty components, `.` or `..` components, and alternate spellings of
one physical path are refused before file access. This prevents lexical or
path aliases from bypassing source uniqueness or fragment-overlap checks.
The index, paths, and profile keys do not enter a profile body. Adding or
removing an index row changes the repository publication set, not an existing
profile identity. A compiler accepts neither unindexed manifests nor a
filesystem-discovered profile.

## 3. Owner-qualified source edition

The v1 manifest has exactly:

```text
SemanticProfileSourceManifestV1 = {
  format: "zkc.semantic-profile-source.v1",
  key: ExactAsciiSymbol,
  catalog_namespace: ExactAsciiSymbol,
  profile_family: ExactAsciiSymbol,
  revision: u64,
  expected_imports: CanonicalSortedUniqueSeq<profile key>,
  supported_subject_kinds: CanonicalSortedUniqueSeq<ExactAsciiSymbol>,
  fragments: CanonicalSeq<FragmentSourceV1>,
  definitions: CanonicalSeq<DefinitionSource>,
  subjects: CanonicalSeq<SubjectLanguageSource>
}

FragmentSourceV1 = {
  name: ExactAsciiSymbol,
  owner_page: RepositoryRelativePath,
  start: ExactAsciiSymbol,
  end: ExactAsciiSymbol
}
```

The page coordinate belongs to each fragment rather than to the profile. This
lets one owner publish a single semantic profile from several durable pages
without copying those pages into a synthetic authority document. Page paths,
marker names, and fragment order remain build coordinates and do not enter the
compiled profile body; the exact selected fragment bytes do.

`catalog_namespace` is a nonempty lower-case dotted ASCII namespace. Every
explicit definition kind begins with that exact namespace plus `.`. The four
required definition catalogs and two generated catalogs are:

```text
<namespace>.body-compiler
<namespace>.evaluator-signature
<namespace>.failure-schema
<namespace>.semantic-law
<namespace>.source-fragment
<namespace>.subject-language
```

The fragment, definition, subject-language, declaration-reference, import-use,
normalization, reachability, and no-expected-ID rules are exactly those in the
frozen [PIR publication edition](../pir/profiles/README.md), with each literal
`pir` common-catalog namespace replaced by the manifest namespace. A profile
may add a populated owner-local catalog under the same namespace. Empty,
ambient, dynamically registered, or cross-namespace local catalogs are
forbidden.

The v1 semantic law source is the Foundation encoding of:

```text
SemanticProfileLawSourceV1 = R {
  0: N(1),
  1: S[DirectImportUseBody ... by imported ContentRefV0 bytes],
  2: S[R{0:Q(subject_kind),
         1:ProfileDeclarationRefBody(local subject-language declaration)} ...],
  3: S[ProfileDeclarationRefBody(local evaluator signatures) ...],
  4: S[ProfileDeclarationRefBody(local failure schemas) ...],
  5: S[]
}
```

This generic `semantic_law_source` is a direct-use and declaration-reference
index. It is not a second copy of the owner's executable law program. Exact
owner semantics—including body formation, semantic laws, evaluator behavior,
and failure behavior—enter the profile through the selected source fragments
and their reachable declarations. The two layers are complementary: the
generic index makes dependency ownership mechanically inspectable, while the
selected owner bytes commit the domain meaning without moving it into
Foundation.

Every import is derived from an exact imported declaration reference. Carrying
an opaque typed semantic-content or declaration coordinate inside an owner
body is not a profile import; opening its foreign body compiler, law,
evaluator, or failure schema is. Transitive reachability never discharges a
direct use. `expected_imports` must equal the derived key set exactly.

## 4. Reconstruction and rotation

Two independent compilers consume only the indexed manifests, exact marked
owner fragments, and the selected Foundation basis. They must agree on:

- every complete six-field profile body and full typed content reference;
- every local declaration ordinal and direct-import use row;
- topological order and exact root closure; and
- the complete derived identity table.

The current selected corpus contains eighteen indexed profiles. The
publication gate independently reconstructs their full typed identities,
direct imports, and root closures and can print the complete derived table.
That output is an inspection artifact rather than a committed source of truth.

The six frozen v0 profiles are permanent backward-compatibility controls. A
publication-substrate change is acceptable only when all six complete body
bytes and typed IDs remain byte-identical. A v1 owner-fragment change rotates
that profile and exactly its downstream import closure. An unrelated root or
sibling remains unchanged.

The compilers refuse malformed indexes, duplicate keys or paths, missing or
unindexed imports, cycles, namespace disagreement, missing common catalogs,
unresolved or unreachable declarations, overlapping fragments, selector or
normalization failures, surplus edges, and identity feedback.

## 5. Nonclaims

Publication establishes deterministic reconstruction of a finite semantic
language profile. It does not prove that the published laws are consistent,
that an implementation conforms to them, that a cryptographic theorem is
true, that a checker is sound, or that a live authority can be serialized.
Those remain separate owner and evidence judgments.
