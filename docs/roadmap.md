# Roadmap

zkc is growing from a checked protocol representation into a compiler that can
bind protocols to external relations and witnesses, compose protocol
components, and realize prover and verifier endpoints on concrete backends.
[Current Status](status.md) describes what works today, while
[Architecture](architecture.md) describes the intended system.

The areas below are ordered by dependency. Relation compilation remains
upstream: zkc consumes and binds relation artifacts but does not compile
relation source.

## Bind relations, statements, and witnesses

The next foundation is a stable interface between zkc and existing relation
tooling. It will:

- identify a relation artifact and the format or profile used to read its
  interface;
- describe its ordered public-statement ABI and private witness ports;
- bind the relation instance, public statement, sealed protocol, and endpoint
  invocation; and
- provide typed witness handles with explicit ownership, confidentiality, and
  lifetime.

Witness consumption comes first. Generators, trace builders, streams, and
confidential services can remain external providers behind the same interface.
zkc may later include selected generation passes, but generation should not be
required to use the protocol compiler.

## Compose protocol components

Real proof systems combine commitment schemes, polynomial protocols,
transcript logic, reductions, and sometimes child verifiers. zkc needs explicit
composition rules for:

- shared transcript and challenge scopes;
- typed component interfaces and claim joins;
- relation, statement, and witness bindings that survive linking; and
- bounded representation of a verifier used as a child component.

The first integration target will be a small zkVM-shaped system made from
several protocol components. Its VM relation will still come from an external
relation compiler; the purpose is to exercise protocol composition rather than
to build a zkVM frontend.

## Realize endpoints on concrete backends

OIR describes prover and verifier behavior, but zkc does not yet compile it to
general-purpose backend implementations. The realization layer will:

- match endpoint requirements to named backend capabilities;
- lower memory layouts, encodings, and call boundaries without changing
  protocol semantics;
- record which implementation supplies each required operation; and
- preserve a checkable correspondence between the endpoint and the generated
  artifact.

The first version should support one backend end to end. Additional libraries,
services, accelerators, and deployment targets can then use the same
requirement and correspondence model.

## Connect formal evidence

The current repository records formalization receipts and checks selected
ArkLib declarations for drift. A full bridge requires more than attaching a
theorem name to a rule. It must:

- identify the exact protocol or component subject described by the theorem;
- carry evidence in a provider-neutral format;
- admit that evidence for one named claim under an explicit consumer policy;
  and
- establish correspondence between the formal subject and the compiler
  object.

Lean and ArkLib are natural initial integrations, but the interface should not
depend on one proof assistant. Formal correspondence can be added
component-by-component and does not need to block the first composition or
backend work.

## Extend system-level security and scale

Once those interfaces are stable, zkc can cover broader system properties:

- complete computational soundness paths through Fiat–Shamir protocols;
- zero-knowledge judgments and obligations for protocol transformations;
- recursion with explicit contracts and cost accounting;
- aggregation and multi-shard systems that preserve identities and
  assumptions across boundaries; and
- wider protocol and backend coverage driven by concrete integrations.

## Natural extensions

Several useful features can grow alongside the main path: lightweight DSLs
and import frontends that lower to Open PIR, new Protocol Kernel checks for
additional protocol models, witness-provider and generation adapters, and
more backend or hardware targets.

zkc will not infer relation meaning, source correspondence, witness
satisfaction, or backend correctness from a file name or digest. It can bind
those subjects and consume explicit evidence about them while leaving their
original semantic authorities intact.
