# Endpoints

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Provisional owner:** `endpoints`
> **Authority:** None during the transition. Current endpoint semantics remain
> governed by the [Endpoints](../../docs/spec/endpoints.md),
> [Boundaries](../../docs/spec/boundaries.md), and
> [Carrier](../../docs/spec/carrier.md) specifications.

## Purpose

`endpoints/` owns the canonical prover and verifier programs derived from a
fixed protocol: PIR-to-OIR projection, OIR semantics and identity, endpoint
ABI, protected effects, verifier/prover duality, and the abstract execution
contract a realization must preserve.

It stops where concrete suppliers, generated artifacts, deployment, and
invocation begin.

## Owns

- endpoint kinds and semantic roles;
- PIR-to-OIR projection and projection refusal;
- realized obligation coverage and source provenance;
- OIR program, artifact, carrier, canonical identity, and
  identity-authenticated ABI for the current format;
- proof-stream and statement interfaces;
- protected transcript, challenge, check, hole, and decision effects;
- projected `check_call` and `hole_call` behavior;
- verifier/prover duality and counterparty consistency;
- abstract supplier requirements and hole interfaces;
- abstract execution semantics and typed result taxonomy; and
- endpoint-specific preservation obligations that a realization must satisfy.

## Does not own

- protocol structure, seal, or projection-obligation definition;
- relation truth or runtime witness ownership;
- property judgments or compiler transformations;
- selection of concrete libraries, kernels, services, devices, or transports;
- emitted source trees or binaries;
- deployment, invocation, session, or concrete runtime lifecycle;
- attributed run records or conformance grades; or
- current backend support.

Endpoint semantics and endpoint implementations remain distinct even when a
reference interpreter executes OIR directly.

The abstract execution relation belongs here. A reference interpreter is a
realization of that relation and an evidence source; its implementation does
not become semantic authority.

## Dependencies

- `foundation/` for artifact identity, admission, encoding, and evolution;
- `pir/` for Sealed PIR, endpoint obligations, events, routes, and source
  provenance;
- `relations/` for public-statement and witness-interface roles; and
- domain-owned contract definitions cited by endpoint operations.

Projection must not depend on the protocol compiler: any suitable Sealed PIR
may be projected regardless of how it was authored.

## Consumers and outputs

- `realization/` consumes OIR and abstract supplier requirements;
- `relations/` may consume a verifier endpoint through a separately owned
  descent bridge;
- `evidence/` records projection, interpreter, conformance, and execution
  observations; and
- guides expose projection and endpoint-inspection workflows.

## Bridge ownership

`endpoints/` owns Sealed-PIR-to-OIR projection because the bridge creates the
endpoint semantic object. PIR owns the obligations to be realized; endpoints
owns exact coverage, OIR construction, and refusal.

The OIR-to-concrete-artifact bridge belongs to `realization/`. Endpoints states
what must be preserved and realization states how an exact implementation and
binding claim to preserve it.

## Candidate internal topics

- endpoint model and kinds;
- projection and coverage;
- OIR programs, carrier, identity, and ABI;
- verifier semantics;
- prover semantics and construction holes;
- abstract execution and result taxonomy; and
- preservation interface to realization.

## Open boundary questions

- Which remaining CheckContract and HoleContract fields belong to PIR citation
  and routing, abstract endpoint behavior, or concrete realization binding?
- Which parts of an execution profile are abstract endpoint requirements and
  which are concrete realization bindings?
- Which invocation values are authorized by endpoint ABI and which belong only
  to a deployed realization?
- When does an optimization remain OIR-preserving scheduling, and when is it a
  protocol transformation that must return to PIR and compiler review?
