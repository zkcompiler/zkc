# zkc Specification Overview

This is the compact map for the normative specification. If this overview and
an individual specification disagree, the individual specification governs.
Architecture explanations, implementation status, demonstrations, and roadmap
material are intentionally outside the normative corpus.

The corpus describes zkc's intended semantic contract. Explicitly reserved,
provisional, or deferred sections may be ahead of the implementation; they are
not current support claims. [Current Status](../status.md) is the authority for
what the checkout implements and exercises today.

## System model

zkc compiles already formed zero-knowledge protocols. A protocol contains an
ordered transcript spine and a linear graph of typed claims and reductions.
The seal boundary checks the closed protocol object, its structural
Fiat-Shamir admissibility,
its reduction and terminal attachments, and the complete set of obligations
that endpoint projection must realize. A successful seal receives a canonical
content identity. Projection derives verifier or prover OIR from that same
sealed object and checks realized coverage against the sealed obligations.

Security analysis is post-seal. The Soundness Kernel evaluates an explicit
derivation plan under content-addressed rule declarations and authenticated
protocol facts. It returns a conditional, notion-indexed judgment with exact
bounds and inherited qualitative hypotheses. Completeness uses the same typed
machinery but remains a separate notion and track: it neither proves nor
borrows soundness. The Compiler Core searches finite provider-defined
transform domains, validates candidates under the same judgment machinery,
and deterministically rechecks selection.

## Current format boundary

The current protocol format is PIR and the current endpoint format is
OIR. ProtocolVocabulary is `zkc.protocol_vocabulary`. Its six
jointly admitted source sections are:

```text
predicate_specs
claim_profiles
check_contracts
hole_contracts
reduction_contracts
terminal_rules
```

The the canonical encoding decoder is fail closed on a wrong producer marker,
malformed carrier, structural-verification failure, or stored-identity
mismatch. Protocol-environment loading and artifact admission separately
refuse unknown registry names, fields, or constructors, stale cited
digests, unresolved references, ABI mismatches, and invalid cross-section
closures. A human-readable identifier is not semantic authority where the
specification requires a content digest.

Verifier and prover OIR are dual endpoint kinds. Prover OIR carries typed
opaque witness handles, digest-authorized holes, and per-slot construction
routes; verifier OIR carries the corresponding proof-stream operations and
checks. These endpoint semantics do not define a general backend Realization
Compiler.

Relation compilation is external. The current `r1cs` claim profile carries
only digest-shaped `a`, `b`, `c`, and `public` anchors. Seal and derivation do
not parse the relation payload, generate a witness, or decide that a witness
satisfies the relation. A stable relation-bound witness artifact and adapter,
and a general Realization Compiler, are not current specification surfaces.

## Normative documents

| Document | Owns |
|---|---|
| [Protocol Kernel](kernel.md) | The protocol object; WF, LIN, BIND, obligation coverage, reduction closure, terminal closure, identity, and boundary signatures. |
| [Soundness Kernel](soundness.md) | Typed security indices and results, rules and bindings, explicit derivations, exact conditional bounds, completeness separation, and the external trust boundary. |
| [Compiler Core](compiler.md) | Provider-defined candidate domains, transform plans, realization checks, soundness-aware constraints, objectives, selection, and decision checking. |
| [Vocabularies](vocabularies.md) | Closed extensible vocabularies, ProtocolVocabulary v4 admission, contract schemas, policies, and admission or reservation status. |
| [Boundaries](boundaries.md) | Admitted seal, project, and link contracts; consumer checks and conformance tiers. |
| [Endpoints](endpoints.md) | OIR verifier and prover endpoint semantics, protected effects, execution, refusals, and rejects. |
| [Carrier](carrier.md) | The PIR/OIR MLIR representation, typed resources, embedded cited content, canonical identity, and registry interface. |
| [Versioning](versioning.md) | Current stable and unstable surfaces, format evolution, and diagnostic-ID allocation. |

## Reading rules

- Normative terms define intended behavior; tests and implementations provide
  conformance evidence and may reveal specification defects.
- Every external theorem, assumption, opaque predicate, supplier, and adapter
  remains at its declared trust boundary. A citation or digest never proves
  the referenced proposition by itself.
- Proof rejection, unsupported execution, compiler refusal, conditional
  security, completeness, and implementation conformance are distinct
  outcomes.
- Reference-twin agreement, where available, is evidence only for its declared
  parity boundaries, not a second universal implementation or proof of the
  specifications.

For non-normative context, see [Project Overview](../overview.md),
[Architecture](../architecture.md), [Ecosystem](../ecosystem.md),
[Current Status](../status.md),
[Roadmap](../roadmap.md).
