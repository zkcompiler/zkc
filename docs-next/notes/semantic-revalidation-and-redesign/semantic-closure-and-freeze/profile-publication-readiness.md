# Profile Publication Readiness

> **Kind:** Temporary review adjudication and repair contract
> **State:** Ready for stable-upstream publication
> **Authority:** None. Retained decisions belong to Foundation and the
> affected semantic owners.

## Purpose

This record adjudicates the independent pre-publication review against the
durable target. It does not copy the review and does not treat the reviewer as
authority. A finding is retained only when it can be reconstructed from the
profile mechanism, an owning body schema, or an executable counterexample.

## Selected publication rules

1. **Direct-use imports.** A profile directly imports every profile whose
   declaration or law it directly uses. Transitive reachability does not
   discharge a direct use, and a merely reachable profile is not copied into
   the direct edge set. The owner publishes a closed use table and admission
   requires exact equality with `profile_imports`.
2. **Catalogs are the declaration source of truth.** A law source references
   catalog entries by exact `ProfileDeclarationRef`; it does not repeat their
   bodies. A duplicate body is malformed unless the owner defines a separate
   declaration with a separate semantic role.
3. **Hybrid law publication.** Typed tables own imports, declaration roles,
   subject-body compilers, evaluator signatures, and failure schemas. A law
   that has no selected typed calculus is published as an exact bounded ASCII
   clause, not as an unbound host-function name. Law-source version and profile
   revision are explicit independent fields and imply no compatibility.
4. **Dependent runtime schemas.** FS receipt declarations are closed schema
   templates parameterized only by authenticated construction fields and the
   selected Core challenge type. A concrete Core-dependent schema cannot be a
   family-profile declaration.
5. **Opaque references are not imports.** Carrying a typed content reference
   to a foreign profiled subject does not import its language. Opening,
   projecting, or invoking a foreign law does.

## Finding dispositions

### Accepted and repaired before stable profile publication

- The Foundation exact-use rule did not decide direct versus transitive edges.
  The direct-use equation and owner use-table obligation now do.
- PIR static-view `_law` fields named an unadvertised standalone semantic kind.
  They now use exact profile declaration references.
- FS runtime receipt declarations were described as concrete closed schemas
  even though challenge and transcript-state types are construction dependent.
  Interaction now owns a closed dependent-template grammar.
- Public-setup consumers lacked an explicit profile edge. The public-setup
  profile is retained, but becomes family neutral and imports only Interaction;
  each consumer that interprets the view must import it directly.

### Accepted with a different resolution

- Folding `PublicSetupInvocationView` into Interaction would remove one
  profile, but would also make a derived projection-law change rotate every
  Core and Protocol. A separate Interaction-only projection profile preserves
  family neutrality and narrower identity rotation without multiplying by FS
  family.
- The endpoint source-view profile need not import the duplex family merely to
  reject it. The supported arm will be a positive exact canonical-family
  match; every other authenticated family receives the generic construction-
  family refusal. This keeps dispatch closed without importing unsupported
  semantics.
- Projection validation is a live operation governed by the projection-
  relation profile, not a separately identified semantic subject. The
  unformable validation profile was removed; an inert diagnostic fingerprint
  is explicitly nonsemantic and nonauthoritative.

### Routed to dependent-profile publication

- OIR must own the complete endpoint graph declaration grammar. PIR may own
  extraction and source authority but may only reference the OIR declarations;
  the current split physical appendix cannot be published as a profile.
- The endpoint source-view profile needs an explicit supported-kind catalog;
  bounded supplement and bearer mechanics must be separated into portable
  semantic subjects versus process-local authority before publication.
- Analysis supported kinds, law contracts, and positive-polynomial sort
  ownership need explicit tables rather than set subtraction or prose names.

These findings do not block publication of the stable upstream Interaction,
FS-family, public-setup, commitment-opening, and Oracle-commitment profiles
once their own preimages pass the rules above. They do block dependent
Interface/OIR, Relations, and Analysis profile publication.

## Required falsifiers

The publication instrument must reject:

- a missing direct edge hidden by transitive reachability;
- a surplus direct edge with no use coordinate;
- a use-table row that resolves to no catalog, body, signature, or law clause;
- a duplicated declaration body in both catalog and law source;
- a concrete challenge type embedded in an FS family profile;
- a public-setup consumer with no direct public-setup-profile import;
- an endpoint graph profile that depends on a source-view-owned declaration;
- a reintroduced validation profile with no portable supported subject kind;
- a host-dispatch label presented as a closed semantic law.

Every mutation has a same-boundary positive control. Profile bytes and IDs are
published only after two independent encoders reconstruct the same complete
preimage and a second decoder recomputes the typed ID.

## Work order

1. close the stable upstream publication rules and refreeze the semantic
   preflight checkpoint;
2. publish Interaction and the two FS-family profiles bottom-up;
3. publish the family-neutral public-setup, commitment-opening, and
   Oracle-commitment profiles;
4. complete recursive-composition research before dependent profile freeze;
5. repair endpoint graph ownership and publish Interface/OIR, Relations, and
   Analysis profiles; and
6. perform one bounded independent freeze review.
