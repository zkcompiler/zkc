# Foundation

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Provisional owner:** `foundation`
> **Authority:** None during the transition. Current normative rules remain in
> the individual [specifications](../../docs/spec/overview.md).

## Purpose

`project/` owns the cross-domain contract discipline and project-wide
invariants selected by Stage 2. `foundation/` owns only reusable mechanisms
later extracted when multiple zkc domains demonstrably identify,
authenticate, admit, evolve, or exchange typed subjects with identical
semantics. It applies or cites the project rules; it does not redefine them as
a common executable transition model.

It is not the place for every concept that several documents mention.

## Owns

- reusable content-identity and canonicalization mechanisms where their
  meaning is independent of the subject domain;
- reusable vocabulary and mechanisms for the project-owned distinctions among
  representation, authentication, admission, immutable local authority, and
  qualified rejection, once the extraction test below passes;
- reusable typed subject-reference, closure-manifest, identity-effect,
  capability-effect, outcome, and replay mechanisms whose semantics are shown
  to be identical across domains;
- reusable authority, citation, registry-envelope, and fail-closed mechanics
  that pass the extraction test;
- reusable serialization and transport mechanisms that, once the extraction
  test passes, enforce the project-owned rule that content and references never
  carry continued process-local admission or resource authority;
- reusable representations for encoding-domain, transport, semantic-regime,
  and evolution axes shown to have identical meaning across domains;
- binding-time and lifecycle terminology that cites the project-owned
  distinctions and is used with the same meaning across domains;
- reusable extension-admission and version-evolution mechanisms under the
  project and domain policies that govern their use;
- reusable diagnostic-allocation mechanisms where allocation behavior is not
  domain-specific, while Project retains the global policy; and
- a terminology index that routes each semantic term to its actual owner.

Each artifact-owning domain still defines the exact fields, bytes, dependencies,
semantic regime, admission predicate, capability behavior, outcomes, and
identity preimage.

## Does not own

- the protocol object, ProtocolVocabulary, or PIR operation semantics;
- relation formats or correspondence;
- property indices, rules, bounds, or derivations;
- compiler transforms, objectives, or selection;
- OIR programs, endpoint kinds, holes, or execution behavior;
- realization providers, deployments, or invocations; or
- evidence conclusions and current support claims.

Foundation also does not own a universal `Transition` runtime type,
`TransitionId`, wire envelope, checker registry, fact root, portable admission
receipt, or composition law. A domain may later justify a purpose-specific
durable result for a named consumer; Foundation does not generalize that result
into shared authority. Domain-owned propositions do not become
interchangeable merely because their contracts share descriptive fields.

The current `carrier.md` and `vocabularies.md` therefore cannot move here as
whole documents. Only their truly domain-neutral mechanics are candidates.

## Admission test for shared material

A concept belongs in `foundation/` only when all of the following hold:

1. at least two semantic domains use the same mechanism;
2. the mechanism has the same meaning and invariants in each domain;
3. placing it under either consumer would invert or duplicate authority;
4. it can be specified without importing one consumer's object model; and
5. removing it from `foundation/` would force normative duplication.

Otherwise, the concept remains with its semantic owner and other domains cite
it through a bridge.

## Dependencies and consumers

Foundation has no semantic dependency on PIR, relations, property analysis,
the compiler, OIR, realization, or evidence. It may cite them as examples,
but examples cannot enter its definitions.

Every semantic domain may consume extracted foundation mechanisms. That
fan-out makes foundation changes high-impact; it does not make Foundation a
higher semantic authority than Project's cross-domain discipline or the domain
that owns an artifact.

## Identity and authority boundary

Foundation may define how an extracted canonical-identity or capability
mechanism works. Project owns the cross-domain conditions and completeness
discipline; each domain decides what its subject means, which exact predicate
admits it, how its capability copies or expires, and which domain-specific
facts a consumer may derive from it.

The intended split is:

```text
project: cross-domain contract discipline and invariants
foundation: reusable mechanisms admitted by the equivalence/extraction gate
domain: exact subject, lifecycle, predicate, capability, and consumer contract
```

Applying the project-owned authority rule, an identifier authenticates content;
it is not a capability. A capability is opaque, narrow, and local to the
authority that reconstructed it. Bytes, ordinary FFI values, mutable clones,
and provenance may preserve an identity claim or citation, but they do not
carry authority. A receiver must decode, authenticate, close the exact
dependencies, and re-admit the subject before minting new local authority.

Foundation may eventually expose a capability-neutral catalog projection for
linting contract completeness. That projection must remain descriptive: it
cannot execute every transition, own domain truth, or introduce a global
composition algebra.

## Downstream schema topics

- semantic authority and admission;
- identity and canonical encoding;
- artifact lifecycle and immutability;
- binding times and object references;
- extension and registry-envelope discipline;
- version evolution and diagnostics; and
- terminology and owner index.

These are topics, not directories to create in advance.

## Open schema questions

- What exact typed subject-reference schema expresses family, semantic
  identity, and regime without becoming a universal transition envelope?
- Which capability traits are genuinely common while copy, borrow, threading,
  attenuation, revocation, expiry, and single-use rules remain domain-owned?
- Which parts of diagnostic allocation are semantic evolution rules and which
  are project contribution policy?
- What minimum registry envelope remains independent of the concrete
  vocabularies and admission predicates it cites?
- What exact shared vocabulary enumerates lifecycle and qualified-outcome terms
  without collapsing domain-local result variants?
