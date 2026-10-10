# Realization models

The shared [representation](../../../docs/spec/realization/representations.md),
[codec](../../../docs/spec/realization/codecs.md) and [artifact](../../../docs/spec/realization/artifacts.md)
contracts define the laws used by these independent models. The
[correspondence map](../correspondence/realization.md) identifies their actual
Lean declarations and remaining native obligations.

## Values in actual states

A returned-value relation is indexed by actual final states. A logical value can
therefore correspond to a buffer handle whose contents are read in that state.
Sequencing relates the consumer of that handle in the resulting heap; composition
uses the same intermediate execution. The [simulation controls](../../Tests/Simulation.lean)
reject stale contents, rollback after failure and missing events.

## Decoding and failed receives

Honest roundtrips, arbitrary-success faithfulness and complete receive behavior
are distinct codec laws. In the [scalar-byte model](../spec/profiles/realization/scalar-bytes.md),
a noncanonical full word consumes eight bytes while underrun consumes none.
A pure decoder returning `none` cannot express that difference. The
[operational adapter](../../Zkc/Protocols/ScalarBytecode/Execution.lean) retains
the actual read packet and failure state. This is a model theorem; native parser
correspondence is separate.

## Execution, providers and custody

A source-selected adapter binds actual arguments to the consumer's source/site,
domains, inputs and captures. Algebra, codecs, provider transitions and storage
have separate laws. Equal weak unary contracts do not establish that two
backends are interchangeable.

The instruction-list model returns its machine exit as data. Its append law
requires the proved absence of a primitive incomplete halt; it does not permit
resuming an outer stopped execution. Likewise, the atomic continuation model
does not supply crash persistence, distributed consistency or hostile-owner
authentication.

The [native runtime](../../../docs/runtime/design.md) and its [assurance policy](../../../docs/assurance.md#native-correspondence)
retain their own execution and correspondence boundaries. Arkworks native
arithmetic and optional ArkLib mathematical consumers are separate dependencies;
neither connection proves the other.
