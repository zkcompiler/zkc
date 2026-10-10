# Extending the compiler and runtime

Extend the supported mathematical pipeline at the owner of the new behavior.
Read the [contribution guide](../../.github/CONTRIBUTING.md),
[architecture](../architecture.md) and affected specification first. The installed
[compiler API](../../compiler/README.md) and crate READMEs own exact interfaces.

## Choose the boundary

| Change | Owner |
|---|---|
| Reusable protocol or helper | Ordinary `.zkc` library and Entry |
| Authoring syntax, static checking or source Assets | Language and source-to-IR Translation |
| Mathematical type/operation | Domain contract, IR formation and interpretation |
| Transparent ordered algorithm | Local body and its effect/resource contract |
| Optimization or realization | Transforms with an actual-candidate preservation check |
| Physical implementation or conversion | Contracts, Target and backend binding |
| Relation frontend | Relation adapter with exact field/layout and source-adequacy scope |
| Invocation, authority or publication | Entry/proof/joint Host interface |

A whole-protocol callback would erase the computations the compiler is intended
to inspect. Compose ordinary operations and installed primitives instead.

Resolve a cross-component contract before an extension discards semantic
information, moves ownership or changes an existing claim. Leave implementation
choices open until a concrete consumer exercises them. An extension point is
useful when that consumer can use it without rewriting generic binding or
checking; an interface description or refusal alone does not demonstrate support.

### Applying the boundary to AIR and protocol evaluation

The [relation bundle](../spec/domains/relation-bundles.md) owns deterministic
statement/witness conditions and the separate staged predicate. Its schema and
reference evaluator belong to Relation and the independent runtime model.
External AIR syntax, selectors and source-adequacy checks belong to the adapter.
Importing a new AIR does not require a protocol-specific dialect operation.

The [ring arena](../spec/domains/ring-expressions.md) owns typed arithmetic and
substitution. Its reusable bulk operations have domain contracts, ordered
Algebra dialect operations and backend implementations. Their inputs contain no
protocol rounds, roles, commitments or acceptance decisions. The
[Sumcheck library](../../libraries/sumcheck/expression.zkc) composes those
operations with messages, challenges and checks in ordinary source. The Entry
package carries their expression bodies and the Host independently admits them
against the program's digest references. The compiler admits the captured bodies,
derives their static dimensions and checks explicit structural sharing. Generic
IR transformations do not yet traverse the arithmetic inside these assets.

A new sampling distribution changes the service contract and its realization;
putting it inside a protocol helper would hide its randomness and transcript
requirements. Storage sharing belongs to the Runner/backend representation
boundary, because allocation identity must not become a protocol observation.

Change core semantics when a required value, control behavior or observation
cannot be represented by the existing model. A new proof system alone does not
establish that need. First express its scheduling and checks as a library;
add domain operations for reusable mathematics and backend kernels for its
physical implementations. Keep concrete Entry configuration in examples.

## Logical contracts and source exports

[Operation contracts](../compiler/operation-contracts.md) own signatures, static
arguments, permissions, effects, resource transitions and representation facts.
Update neutral declarations and their exact consumers together. Catalog presence
does not grant a source spelling, codec, total recipe or transcript construction.
Each boundary needs explicit admission.

An operation that can stop, consume a resource, query a service or change history
belongs to ordered execution. Do not mark it pure/speculatable merely because
its successful arithmetic is deterministic. Unknown facets yield no positive
analysis facts. Same-typed ports still need the right semantic order.

## Dialects, passes and pipelines

Mandatory verifiers belong in IR; they must not require Translation or workflow
services. Translation owns Language emission/comparison, relation adapters and
checked export. Transforms consumes core readers and operation interfaces without
calling a command-line driver. Compiler composes complete requests.

A pass preserves or invalidates analyses for the actual changed IR. Validate
local signatures, nested captures/carries, role availability, ordered actions,
affine successors and closed dependencies. Source locations and copied metadata
locate evidence; they do not prove it. Follow the
[preservation contract](../compiler/verification.md) through serialization and
Host maps, not only through an intermediate in-memory module.

Physical changes validate proposed implementations/conversions independently,
then check actual materialization. An unsupported but equal rewrite may refuse;
do not weaken admission to make an optimizer succeed. Mutation controls should
change the relevant operand, receive, type, resource or terminal while leaving
unrelated structure valid.

## Runtime and native implementation

All executable extensions use `zkc.program/0` and the shared Runner. Update C++
export and Rust admission for the same exact type/control contract. Hosts retain
their application responsibilities: authenticated identity, input and setup
binding, limits, failure reports, cleanup and publication.

A backend implements the operation's mathematical and representation contracts,
including malformed input, capacity and partial failure. Test against independent
expectations from original inputs. Identical schemas and two consumers agreeing
on the same wrong artifact do not establish source correctness. Native exact
identity remains authoritative; the native proof contract adds admission
and authority requirements to the shared executable.

Domain and kernel contributions remain explicit extensions: declarations need
their own interpretation, physical implementation, registration and consumer
checks. The native service registry is currently closed to four RNG contracts
and their providers. An installed domain or kernel does not add an arbitrary
request/reply service family; that requires a future service extension.

## Relations and independent formal work

Relation import validates domain data. Wider external frontends must identify
unsupported operations before erasing them, preserve exact field/public layout
and state the scope of source encoding adequacy. The
[relation ingress guide](../compiler/relations.md) covers Assets, native
adapters and optional LLZK integration.

Lean models provide reusable laws at their stated semantic subjects. An extension
may add an explicit native interpretation or independent reference, but no old
source/table theorem automatically validates a new native operation or program.
[Assurance](../assurance.md) controls that claim.

Select affected checks from the [test guide](../../common/tests/README.md#selecting-checks).
Installed-header/component changes need installed consumers; codec and Host
changes need actual execution and refusal cases. Broaden validation when failures
or unresolved concerns justify it, and report the scope actually run.
