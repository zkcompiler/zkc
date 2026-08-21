# Realization and runtime

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Provisional owner:** `realization`
> **Authority:** None during the transition. Current realization material is
> split among the reserved [boundary contract](../../docs/spec/boundaries.md),
> the non-normative [target architecture](../../docs/architecture.md), and
> operational claims in [Current Status](../../docs/status.md).

## Purpose

`realization/` owns the downstream lifecycle that implements a fixed endpoint:
supplier binding, emission, generated artifacts, preservation contracts and
judgments, deployment, invocation, sessions, and concrete execution.

This separate domain preserves a central semantic firewall: OIR states accepted
endpoint behavior; a realization chooses how that behavior is implemented.

## Owns

- realization requests, target and capability descriptions;
- exact supplier bindings for codecs, sponges, checks, holes, kernels, or
  services;
- concrete CheckContract and HoleContract supplier selection and execution;
- emission and generated-artifact identity;
- lowering, scheduling, fast-path, and backend preservation contracts;
- deployment artifacts and resource bindings;
- invocation objects, per-run authorized inputs, and session lifecycle;
- concrete prover and verifier execution under a bound realization;
- attributed operational run and session records;
- runtime refusal classes distinct from verifier proof rejection; and
- implementation-produced event logs or semantic digests before they are
  converted into evidence records.

Much of this surface is not yet normative. Architecture-only and reserved
topics must remain labeled as such until exact schemas and identities exist.

## Does not own

- relation, protocol, or OIR meaning;
- protocol transformations or accepted-behavior changes;
- endpoint projection or canonical OIR identity;
- security, completeness, or zero-knowledge conclusions;
- the evidence grade granted to an implementation record; or
- current public support claims.

A realizer may optimize implementation while preserving OIR. If it changes
transcript behavior, proof ABI, statement binding, checks, routes, or terminal
decision, the change is no longer merely realization and must return to the
owning semantic layer.

## Dependencies

- `foundation/` for artifact identity, admission, and lifecycle primitives;
- `endpoints/` for OIR semantics, ABI, abstract suppliers, protected effects,
  and preservation obligations;
- `relations/` for statement and witness-interface roles at invocation; and
- external provider authorities explicitly pinned by each realization.

Realization does not semantically depend on compiler selection. Any admitted
endpoint may be realized if a target can satisfy its contract.

## Consumers and outputs

- users and systems deploy and invoke realized endpoints;
- `evidence/` consumes exact artifacts, environment descriptions, logs, and
  run results to form bounded records;
- `project/` summarizes supported realization paths through global status; and
- guides describe emission, deployment, and invocation workflows.

## Bridge ownership

`realization/` owns three distinct transitions: OIR plus supplier binding to an
emitted artifact; emitted artifact plus resources and policy to a deployment
binding; and deployment plus invocation inputs to an operational run and
result. Each transition must state its own identity, preservation relation,
refusals, and residual assumptions rather than collapsing the lifecycle into
one artifact.

The operational-record-to-evidence-record bridge belongs to `evidence/`.
Realization owns the attributed run; evidence governs the bounded record and
the relying consumer owns the decision to accept it for a claim.

## Candidate internal topics

- targets, providers, and supplier capabilities;
- emission and generated artifacts;
- lowering, scheduling, and fast paths;
- preservation and conformance interfaces;
- deployment and resource binding;
- invocation, sessions, and runtime capabilities; and
- concrete execution and result production.

## Open boundary questions

- Is there enough current normative content for one realization domain, or
  should some topics remain target architecture until schemas mature?
- Which realization identity and evidence record should describe the reference
  interpreter without turning its implementation into semantic authority?
- Should deployment and invocation become separate subdomains once their
  identities and authority models stabilize?
- Which supplier choices are semantically observable and therefore part of
  endpoint identity rather than realization identity?
- Does future runtime confidentiality or capability policy belong here or in a
  separate operational domain?
