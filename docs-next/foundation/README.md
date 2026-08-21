# Foundation

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Provisional owner:** `foundation`
> **Authority:** None during the transition. Current normative rules remain in
> the individual [specifications](../../docs/spec/overview.md).

## Purpose

`foundation/` owns the smallest shared semantic substrate needed for multiple
zkc domains to identify, authenticate, admit, evolve, and exchange typed
artifacts without redefining those mechanisms independently.

It is not the place for every concept that several documents mention.

## Owns

- common content-identity and canonicalization principles;
- decoded, authenticated, admitted, immutable, and rejected artifact lifecycle
  distinctions that apply uniformly across artifact kinds;
- common authority, citation, registry-envelope, and fail-closed admission
  mechanics;
- shared encoding-domain and transport rules;
- binding-time and lifecycle terminology used across domains;
- extension admission and version-evolution discipline;
- global diagnostic-allocation policy where it is not domain-specific; and
- a terminology index that routes each semantic term to its actual owner.

Each artifact-owning domain still defines the exact fields, bytes, dependencies,
and semantics in its own identity preimage.

## Does not own

- the protocol object, ProtocolVocabulary, or PIR operation semantics;
- relation formats or correspondence;
- property indices, rules, bounds, or derivations;
- compiler transforms, objectives, or selection;
- OIR programs, endpoint kinds, holes, or execution behavior;
- realization providers, deployments, or invocations; or
- evidence conclusions and current support claims.

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

Foundation has no semantic dependency on PIR, relations, judgments, the
compiler, endpoints, realization, or evidence. It may cite them as examples,
but examples cannot enter its definitions.

Every semantic domain consumes some foundation rules. That fan-out makes
foundation changes high-impact; it does not make foundation a higher semantic
authority than the domain that owns an artifact.

## Identity and authority boundary

Foundation may define how a canonical identity mechanism works and how an
admitted capability is minted. It does not decide what an artifact means or
which domain-specific facts a consumer may derive from it.

The intended split is:

```text
foundation: canonical mechanism, lifecycle, and admission invariants
domain: exact semantic preimage, dependencies, and consumer contract
```

## Candidate internal topics

- semantic authority and admission;
- identity and canonical encoding;
- artifact lifecycle and immutability;
- binding times and object references;
- extension and registry-envelope discipline;
- version evolution and diagnostics; and
- terminology and owner index.

These are topics, not directories to create in advance.

## Open boundary questions

- Is there enough genuinely shared artifact semantics to justify a future
  `artifacts/` or `representation/` domain, or should carrier rules remain
  distributed between PIR and endpoints?
- Which parts of diagnostic allocation are semantic evolution rules and which
  are project contribution policy?
- Is the protocol environment a generic authority bundle or a PIR-specific
  authority that merely uses foundation admission mechanics?
- Can one common registry envelope remain independent of the concrete
  vocabularies it carries?
