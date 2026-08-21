# Relations

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Provisional owner:** `relations`
> **Authority:** None during the transition. Current relation semantics remain
> governed by the [Relations specification](../../docs/spec/relations.md).

## Purpose

`relations/` owns zkc's boundary to already formed relations. It identifies an
external predicate and its interface without pretending that zkc compiled the
predicate, generated a satisfying witness, or proved satisfaction.

## Owns

- RelationContract identity, schema, and lifecycle;
- relation artifact references and admitted format profiles;
- public-instance encoding and ABI;
- witness-port declarations and interface roles;
- anchors and their protocol-facing projection;
- statement correspondence and relation-to-protocol binding;
- adapter contracts and the explicitly bounded interface facts they may
  produce;
- computed, cross-checked, and asserted classifications, residual obligations,
  and non-claims, without creating a parallel trust taxonomy; and
- verifier-to-relation descent when an endpoint becomes material for an outer
  relation.

Format-specific profiles, such as an R1CS reader, are separate change
boundaries from the generic relation contract even if both remain in this
domain.

## Does not own

- relation-source languages or relation compilation;
- predicate truth or witness satisfaction unless a future exact judgment and
  evidence boundary explicitly provides it;
- witness generation, storage, secrecy, or runtime capabilities;
- protocol transcript or claim-flow semantics;
- cryptographic property judgments about a protocol;
- endpoint execution or deployment; or
- broad compatibility claims for external relation ecosystems.

Reader and adapter implementations are conformance subjects. Their observed
behavior belongs in evidence, not in the normative relation contract.

Declaring a witness port describes an interface. Supplying and consuming a
runtime witness capability belongs to realization and invocation.

## Dependencies

- `foundation/` for identity, admission, encoding, and version rules;
- `pir/` definitions when specifying exact protocol anchor or statement
  correspondence; and
- `endpoints/` definitions for verifier-to-relation descent.

The relation itself remains external. A digest or adapter result identifies and
describes a boundary; it does not establish the predicate it names.

## Consumers and outputs

- PIR supplies sealed opaque anchors and statement labels; it does not consume
  or change identity when a RelationContract is attached;
- judgments may consume authenticated relation facts only through an explicit
  subject projection;
- endpoints and realization consume public and private interface roles;
- the compiler may require relation-facing prerequisites without owning them;
  and
- evidence records adapter behavior and correspondence checks at exact scope.

## Bridge ownership

`relations/` owns the transition from Sealed PIR, a post-seal RelationContract,
and optional relation bytes to a correspondence result. The bridge establishes
what external relation role the protocol material denotes; it does not alter
the sealed artifact. PIR owns the referenced protocol definitions and does not
duplicate them here.

`relations/` also provisionally owns endpoint descent because the output gains
the semantic role of relation material. Endpoint identity and verifier behavior
remain under `endpoints/`.

## Candidate internal topics

- relation contracts and identity;
- public instance, anchors, and witness interfaces;
- statement and protocol correspondence;
- format adapters and bounded readers;
- trust, assumptions, and non-claims; and
- verifier-to-relation descent.

## Open boundary questions

- Which correspondence judgments are relation-local, and which properties
  belong in the post-seal property calculus?
- How should adapter evidence be separated from the normative interface facts
  an adapter is permitted to produce?
- When, if ever, should witness satisfaction become a zkc judgment rather than
  an external proposition?
- Does descent mature into relation semantics, composition architecture, or a
  distinct recursive-realization boundary?
