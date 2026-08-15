# Roadmap

zkc is growing from a checked protocol representation into a compiler that can
bind protocols to external relations and witnesses, compose protocol
components, realize prover and verifier endpoints through generated
implementations, and move protocol parameters under judgment.
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

## Realize endpoints through emission

OIR describes prover and verifier behavior; emission turns one endpoint into
a standalone implementation under an explicit supplier binding that names one
implementation for every codec class, construction pin, and hole contract the
endpoint requires. The next steps deepen that path rather than adding a
layer. They will:

- widen supplier bindings and targets behind the same binding discipline —
  embedded libraries, devices, and services beside generated code;
- make correspondence measurable, with generated endpoints graded against the
  independent implementations they borrow kernels from and benchmark gates
  that expose assembly overhead as a number;
- extend handle contracts so data residency and layout stay explicit wherever
  a silent copy would falsify the performance claim; and
- carry deployment surfaces — setup material, embedding, invocation plans —
  without letting them authorize semantics.

A capability-matching or general lowering layer is not planned. Performance
authority stays at named points: reference-passing handle contracts with
explicit layout, orchestration loops owned by the generated code, benchmark
evidence against the borrowed implementations, and explicit supplier
designation. Generating fused kernels that no supplier provides is the one
concern that would justify new machinery, and it waits for a concrete need.

## Move protocol parameters under judgment

zkc already applies checked structure-changing transformations whose
judgments survive the rewrite. The same machinery extends to a choice every
deployment makes by hand today: picking protocol parameters. It will:

- let a protocol family describe its parameter space, so each candidate seals
  and prices as a first-class subject;
- keep distinct security-accounting regimes distinct objects, so a proven
  bound and a conjectured bound never blur into one number;
- use measured endpoint cost profiles as the search objective, connecting the
  benchmark evidence above to the selection; and
- keep selection deterministic and re-checkable, in the same discipline as
  the existing checked transformations.

This area depends on emission's measurements: a search without a cost profile
can optimize nothing but proof size.

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
backend work. The same admission discipline is what will eventually let
identity, judgments, receipts, and measurements assemble into one
independently checkable report; that schema stays unfixed until the analyses
it would carry exist.

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
