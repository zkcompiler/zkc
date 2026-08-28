# Foundation

> **Document kind:** Domain index
> **Document state:** Active target-domain index
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

## Selected documents

- [Executable Semantic Foundations](executable-foundations.md) defines the
  selected K1 candidate for bootstrap, typed identity, exact semantic-language
  profiles, semantic modules, domain-indexed values, portable algorithms,
  deterministic evaluation control, inert source-authority envelopes, and the
  boundary between semantic completion and operational noncompletion. Domain
  language contents, predicates, judgments, policy derivations, live
  capabilities, and resource policies remain with their owners. Bounded K3-B
  Relations, K3-C Analysis, and K3-D OIR have demonstrated three aligned
  consumer extractions, and K3-E has exercised their joined profile and inert-
  envelope boundary over one finite witness. This satisfies the bounded
  extraction gate only; it does not move owner predicates or live authority
  into Foundation and does not freeze the kernel.

## Owns

- reusable content-identity and canonicalization mechanisms where their
  meaning is independent of the subject domain;
- the exact standalone semantic-language-profile envelope, authenticated
  profile-import closure, profiled-subject wrapper, and effective-context
  equality law selected by K1, including the exact disjoint standalone catalog
  for canonical values, evaluation contracts, external-operation contracts,
  portable algorithms, semantic-language profiles, semantic modules, and
  semantic primitives, while each domain owns its actual profiled language;
- reusable vocabulary and mechanisms for the project-owned distinctions among
  representation, authentication, admission, immutable local authority, and
  qualified rejection, once the extraction test below passes;
- reusable typed subject-reference, closure-manifest, identity-effect,
  capability-effect, outcome, and replay mechanisms whose semantics are shown
  to be identical across domains;
- the minimal inert source-authority envelope that preserves exact
  owner-profiled references, owner/family agreement, and same-regime shape
  without interpreting or transporting authority;
- reusable citation, registry-envelope, and fail-closed mechanics that pass
  the extraction test;
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

Foundation fixes the common canonical-value encoding, typed identity-preimage
framing, profile envelope, and inert authority envelope selected by K1. Each
artifact-owning domain still defines its exact domain-specific semantic body,
profile contents and exact-use derivation, subject-specific dependency
meaning, admission predicate, complete policy-closure derivation, capability
behavior, outcomes, and domain policy.

## Does not own

- the protocol object, ProtocolVocabulary, or PIR operation semantics;
- relation formats or correspondence;
- property indices, rules, bounds, or derivations;
- compiler transforms, objectives, or selection;
- OIR programs, endpoint kinds, holes, or execution behavior;
- realization providers, deployments, or invocations; or
- evidence conclusions and current support claims.

Foundation also does not own a global language-profile registry, one composite
project-wide semantic regime, domain policy facts, an authored aggregate
policy closure, owner admission, or any live capability. Subject-specific
ordinary modules remain separate from the generic effective language context.

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

Foundation may define how an extracted canonical-identity, exact-profile
closure, or capability-neutral authority-envelope mechanism works. Project
owns the cross-domain conditions and completeness discipline; each domain
decides what its subject means, which exact language and policy dependencies
are complete, which exact predicate admits it, how its capability copies or
expires, and which domain-specific facts a consumer may derive from it.

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

Foundation now exposes only a capability-neutral source-authority envelope.
Its exact owner-profiled IDs are descriptive inputs to the named owner. The
owner authenticates their preimages and derives the complete policy closure;
an aggregate consumer derives a canonical union rather than authoring a second
summary. The envelope cannot execute transitions, own domain truth, validate a
policy derivation, mint a capability, or introduce a global composition
algebra.

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

- Which later subject families require refinements of the selected typed
  identity without becoming a universal transition envelope?
- After the selected nonserialization rule, are any additional capability
  traits genuinely common while borrow, threading, attenuation, revocation,
  expiry, and single-use rules remain domain-owned?
- Which parts of diagnostic allocation are semantic evolution rules and which
  are project contribution policy?
- What minimum registry envelope, if any beyond exact supplied profile and
  dependency bundles, remains independent of the concrete vocabularies and
  admission predicates it cites?
- What exact shared vocabulary enumerates lifecycle and qualified-outcome terms
  without collapsing domain-local result variants?
