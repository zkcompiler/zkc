# Protocol IR

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Provisional owner:** `pir`
> **Authority:** None during the transition. Current protocol semantics remain
> governed by the relevant [normative specifications](../../docs/spec/overview.md).

## Purpose

`pir/` owns the protocol as zkc's compiled semantic subject: its ordered
transcript, claim flow, checks, challenges, reductions, terminal behavior,
composition, and transition from editable Open PIR to immutable Sealed PIR.

The domain name remains provisional. The research must determine whether PIR
is the long-lived semantic product name or the current representation of a
more general protocol domain.

## Owns

- the protocol object and its semantic parts;
- transcript spine ordering and protected protocol effects;
- claims, reductions, checks, challenges, material bindings, routes, and
  terminal closure;
- protocol-specific vocabularies, profiles, policies, and extension points;
- identity-bearing CheckContract and HoleContract citations, their
  protocol-facing ABI, and route or attachment meaning;
- Open PIR and Sealed PIR lifecycle;
- structural formation, well-formedness, linearity, binding, closure, and seal
  judgments;
- projection obligations exported to endpoint consumers;
- static protocol composition and `link`;
- PIR carrier semantics, canonical PIR identity preimage, and artifact format;
  and
- authenticated structural facts explicitly exported to later consumers.

## Does not own

- relation satisfaction, relation-source compilation, or witness generation;
- soundness, knowledge, completeness, zero knowledge, or their bounds;
- compiler search, scoring, or selection merely because it produces PIR;
- OIR or realized endpoint coverage;
- backend emission, deployment, invocation, or concrete runtime suppliers;
- evidence grades or current implementation support; or
- MLIR classes and pass structure as architectural boundaries.

Structural predicates such as formation, `WF`, linearity, binding, closure,
seal, and link remain here even though they are judgments. The top-level
`judgments/` domain does not own every proposition written with an inference
rule.

## Dependencies

- `foundation/` for identity, authentication, admission, encoding, and common
  lifecycle rules; and
- domain-owned vocabulary entries for any admitted external extension.

PIR carries relation-shaped anchors and identities opaquely. Sealing does not
load a RelationContract or import post-seal relation-interface facts.

PIR must remain meaningful without depending on the compiler or endpoint
realization. A protocol may be authored and sealed without first being found by
the optimizer or successfully projected to every target.

## Consumers and outputs

- `judgments/` consumes authenticated protocol facts and exact subjects;
- `relations/` consumes Sealed PIR, a post-seal RelationContract, and optional
  relation bytes to derive correspondence without changing PIR;
- `compiler/` consumes and produces protocol subjects through checked
  transforms, with outputs returning as Open PIR;
- `endpoints/` consumes Sealed PIR and its projection obligations;
- `evidence/` binds conformance observations to exact PIR subjects.

## Bridge ownership

PIR owns Open-to-Sealed transition and static link. It owns the definitions of
facts and obligations it exports, but not the consumer's interpretation:

- admitted PIR to a property-analysis view belongs to `judgments/`;
- Sealed PIR to OIR belongs to `endpoints/`; and
- PIR facts used by compiler constraints belong to the compiler ingress or
  constraint contract.

## Candidate internal topics

- protocol model and vocabulary;
- Open PIR construction and editing;
- structural judgments and closure;
- sealing, identity, and artifact lifecycle;
- composition and link;
- PIR carrier and canonical encoding; and
- exported facts, obligations, and consumer interfaces.

## Open boundary questions

- Should the stable subject be called “protocol” with PIR nested as a carrier?
- Which individual CheckContract and HoleContract fields belong to the
  protocol-facing citation, the abstract endpoint call, or the concrete
  supplier binding?
- Which composition invariants are structural PIR facts and which require new
  property judgments?
- Should artifact lifecycle remain here while only generic lifecycle mechanics
  live in foundation?
