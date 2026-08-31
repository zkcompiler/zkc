# Stable Profile Publication

> **Kind:** Temporary publication design and execution record
> **State:** Active
> **Authority:** None. The owning Foundation and PIR pages, together with the
> published owner-source artifacts they explicitly adopt, own every retained
> definition.

## Objective

Publish independently reconstructible profile preimages for the stable
upstream graph:

```text
PIR Interaction
|- canonical-framed Fiat--Shamir
|- duplex-sponge Fiat--Shamir
`- family-neutral public setup
   `- commitment-opening verification
      `- Oracle-commitment construction
```

The displayed tree is only a readability projection. Commitment opening
directly uses both Interaction and public setup. Oracle commitment directly
uses Interaction, public setup, and commitment opening. Those required
diamonds remain explicit in the exact import graph.

## Selected publication source

A profile is compiled from a durable owner-source manifest, not from a
placeholder law label, generated host code, or the prose page as an
undifferentiated blob. The source format has four normalized layers:

1. exact bounded UTF-8 source fragments are extracted between unique inert
   markers in the owning durable page and stored once in a
   `pir.source-fragment` declaration catalog;
2. named body compilers, semantic laws, evaluator signatures, and failure
   schemas reference one exact local source fragment and one semantic selector
   rather than copying the source bytes;
3. one generated subject-language declaration per supported subject kind
   references the exact definitions that compile and admit that kind; and
4. the structured profile law source references those declarations, derives
   its direct-import use table, and contains no duplicate declaration body.

Source paths and extraction-marker names are build coordinates and do not
enter the profile preimage. The exact extracted bytes do. Moving an unchanged
source fragment therefore preserves identity; changing its semantic text
rotates the owner profile. The selected textual source edition deliberately
rotates on formatting changes inside a marked semantic fragment. A future
typed law calculus would require a new profile revision and an explicit bridge;
v0 does not pretend Markdown and a formal calculus are equivalent.

## Exactness rules

- Every marker is unique, paired, outside the extracted bytes, and names one
  nonempty fragment.
- Fragment bytes are valid NFC UTF-8, use LF only, have no trailing horizontal
  whitespace, and end in exactly one LF.
- Catalog kinds are ASCII sorted-unique. Declaration ordinals are source
  order, and every source manifest names declarations uniquely within a kind.
- A named definition's selector must occur in its source fragment. A host
  function name or unresolved label is not a definition.
- Every supported subject kind has exactly one generated subject-language
  declaration and one law-source compiler row. Unknown or duplicate kinds
  refuse publication.
- Direct profile imports are derived from every imported declaration
  reference in declarations, subject compilers, evaluator signatures, and
  failure schemas. The manifest's expected import set must equal that derived
  set exactly.
- The compiled law source carries the derived use table. Neither the manifest
  nor a caller can pad it with a merely transitive or unused import.
- No source artifact contains its own profile ID or an expected digest. Derived
  identity records are output artifacts and never feed compilation.

## Independent reconstruction

The publication evaluator has two implementations:

- a reference compiler using the selected Foundation `MetaValueV0`, profile
  body, and typed-content constructors; and
- a cold compiler with its own datum encoder, framing, prior-meta
  reconstruction, profile-reference encoder, source parser, import traversal,
  and typed-content hashing.

Both consume only the durable source manifests and owner fragments. They must
produce byte-identical six-field profile bodies, full content references,
root-specific no-extra closures, and identity records. The cold compiler also
reconstructs the Foundation identity profile, hash suite, semantic regime,
and exact regime digest before any PIR profile is accepted.

## Required falsifiers

The package refuses at least the following mutations:

- missing, surplus, transitive-only, or cyclic direct imports;
- an imported declaration with no direct edge or a direct edge with no use;
- missing, repeated, overlapping, non-NFC, CR-bearing, or trailing-whitespace
  source fragments;
- a selector absent from its exact source fragment;
- a declaration body copied into the law source;
- a concrete Core-dependent challenge or transcript-state type in an FS
  family declaration;
- a public-setup consumer that omits its direct public-setup use;
- a subject kind without an exact compiler row;
- a host dispatch label masquerading as a semantic law; and
- an expected identity fed back into its own source.

Every rejection has a same-boundary positive control. Mutation tests operate
on temporary in-memory sources and never rewrite the durable artifacts.

## Publication order and exit

1. independently reconstruct the selected Foundation regime;
2. publish Interaction;
3. publish both Fiat--Shamir siblings and prove sibling locality;
4. publish family-neutral public setup;
5. publish commitment opening and Oracle commitment with their direct-use
   diamonds; and
6. bind a published target profile into an executable consumer only when that
   consumer implements the profile's exact body compiler and admission law;
   otherwise retain an explicitly witness-local profile and prove that its ID
   is distinct from the published target ID.

The package closes only when all six source manifests compile under both
implementations, every falsifier has its expected classification, the durable
identity table is reproduced rather than trusted, root closures are exact,
and one focused independent review has been adjudicated. This does not publish
Interface/OIR, Relations, Analysis, or any cryptographic theorem profile.

The bounded protocol witness intentionally remains on witness-local profiles.
Its finite Core body is not the durable Appendix-A `InteractiveCoreBody`, so
substituting the published target profile would authenticate an uncompiled
body and overstate conformance. The target publication and behavioral witness
are complementary evidence lanes until an exact body compiler joins them.
