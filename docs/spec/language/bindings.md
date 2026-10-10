# Closed operation bindings

This profile defines closed installed operation bindings and physical types for
[executable programs](../formats/program.md). The mathematical compiler and Rust
admission consume the same declared contracts independently. Source spelling and
capabilities are owned by [Language](README.md).

## Meaning and ownership

A binding is a closed application of an installed operation contract to static
identities. Its name is a module symbol used for resolution. It is not a session,
challenge origin, resource identifier or proof of the installed contract.

The installed declaration supplies its parameter sorts, associated identities,
requirements, and input/output type constructors. Serialized code cannot invent
these facts. A physical selection supplies an implementation of that particular
closed operation and exact physical ports. Logical admission rejects physical
types; physical admission requires implementation selections. A logical binding
may already constrain the eventual implementation, while retaining logical ports.

An installation is finite: it names particular nominal domains and operation
contracts, not the universe of types in the generic model. A library definition
can be checked under symbolic requirements before a supported closed instance is
selected.

## Carrier

The executable retains an explicit operation-binding array alongside its
local functions, participants and entry points:

```
["zkc.program/0", bindings, functions, participants, entries]

binding = [symbol, logical_contract, static_arguments, implementation]
```

An empty implementation string leaves selection open at common/logical stages.
An explicit choice is checked at every stage and must be honored by planning.
Physical examples
include `arkworks/poly.fold` and `arkworks-msb/poly.fold`. Their selection is
checked for that exact contract, not accepted as a free backend prefix.
Local `op` records reference a binding symbol. Their separate parameters retain
the operation's dynamic/static attributes, such as a field constant or an
explicit transcript origin; they do not replace the binding's static identities.

For installed numerical attributes, admission checks the required arity first.
It then checks each value in order: decimal syntax, canonical spelling, and
that position's range before reading the next value. A cross-attribute condition
such as the matrix transpose flag follows those checks. Thus an out-of-range
first dimension takes priority over a noncanonical second dimension. This is
an ordering rule within attribute admission, not a global priority rule for
unrelated defects elsewhere in a carrier. Input-size limits still precede
decoding.

Logical types apply an installed constructor to ordered static arguments. Each
parameter has kind `Domain(sort)`, `Type` or `Nat`. A domain argument names an
installed nominal identity of the declared sort; a type argument is another
logical type; a natural argument is a canonical decimal in `0..1048576`.
Formation is independent of representation and implementation availability.

Zero-argument constructors retain their bare spelling (`bool`, `index`,
`indices`); one-domain constructors retain `kind:identity`, such as
`table:bls12-381.fr` or `group:bls12-381.g1`. Other applications use
`constructor<argument,...>`, for example `fixed_vector<field:koala-bear,4>`.
These forms are canonical: `field<koala-bear>`, whitespace, empty arguments,
leading zeros in naturals and physical types nested as arguments refuse.
Neither a matching sort nor an invented constructor installs a type. Existing
atomic constructors check their explicit admitted identity sets.

A physical type adds one outer `@representation`. That representation must
support the complete logical application, including every nested type and natural
argument. Missing support is a physical-selection refusal, not a malformed
logical type. MLIR retains both parts in `!plan.data<logical, representation>`;
domain-owned logical MLIR types preserve their static arguments before planning.

The bounded reader admits at most 4096 bytes per nonvariant logical spelling,
eight combined structural/variant nesting levels and 200000 nodes per type
parse. The node budget counts constructor and atomic type nodes, structural
Domain/Nat arguments, and the existing variant descriptor nodes; nesting cannot
reset it. The existing variant spelling and payload bounds also apply.
The outer representation name is checked separately. These are admission limits,
not mathematical restrictions on the type theory.

Copy and drop each require the constructor's declared permission and that
permission for every Type argument. A container of an affine element cannot
acquire copying through a wrapper. A public or serializable element does not
give the container a codec: codec, observation and implementation support remain
explicit installation facts.

Source names and direct kernel use obey the Language profile's permissions and
installed source stage. Catalog presence alone cannot expose construction-only
transcript operations or establish construction provenance.

In MLIR, `local.binding` is a symbol declaration. Mathematical dialect
operations reference it with a `binding` symbol attribute. This includes
operations with no operands: their result domain is explicitly selected.
The common-protocol interaction and role-projection structure is unchanged.

The finite numerical installation also admits `koala-bear` field, vector, matrix,
coefficient-polynomial and quadratic-round carriers with Plonky3 implementations.
Field facts remain independent of group and PCS associations. The octic
extension, its selected transcript/index-sampling suite, and the separately
named [vector commitments](../domains/oracles.md) add their own capabilities;
they do not manufacture a group or multilinear opening capability. Unavailable operations or
wrong-provider selections refuse. The [operation guide](../../compiler/operation-contracts.md)
and [structured wire contract](../formats/messages.md)
record the implementation boundary; generic signatures remain independent of
these installed choices.

Transcript observation binds the complete payload type and its admitted codec
independently of the transcript challenge domain. The native
[proof profile](../formats/proof.md) and
[structured observation contract](../formats/messages.md#transcript-observation)
fix the exact supported combinations.

Function records retain logical-origin metadata separately from executable
symbols and implementation choices. `.zkc` origins identify qualified source
definitions; exact static selection is retained by the checked closure and
emitted symbol. Preserving metadata alone proves no source correspondence.

## Representations and conversion

Physical planning resolves each operation binding independently. Callable and
control interfaces take the installed default physical ports. Kernel
results receive the selected implementation's ports. Consequently, two values
with the same logical type may have different physical types in one artifact.

For tables, `arkworks.mle-lsb/0` and `arkworks.mle-msb/0` denote different actual
storage orders for the same logical MSB-coordinate polynomial. Changing the
representation label alone is invalid. A crossing requires an ordered
`arkworks/table.relayout` instruction with a physical-only `table.relayout`
adapter binding. Its arguments are field identity, source representation and
target representation. Equal endpoints and incompatible domains are rejected.

The planner inserts conversions at actual use/return boundaries. It does not
move them across protocol actions or erase them as mathematical identities.
Allocation, limits and stopped executions remain obligations of the execution
and correspondence adapters. Neither type agreement nor an ordinary successful
value comparison proves preservation for an arbitrarily constrained allocator.

Physical selection validates explicit implementation choices against the actual
binding. Planning is transactional: unsuccessful selection leaves logical IR
intact. The [physical decision contract](../../compiler/representation.md#checked-physical-decisions)
distinguishes proposals, validation and materialization.

## Implementation boundaries

- [Native contracts and types](../../../compiler/include/zkc/Contracts/Bindings.h)
  and [MLIR planning](../../../compiler/lib/Conversion/Bindings.cpp).
- [Native preservation checks](../../compiler/verification.md).
- [Generic static requirements](../../../lean/docs/spec/profiles/source/generic-definitions.md).

This carrier does not implicitly interchange opening protocols with different
interaction behavior, add mathematical field coercions, or prove the external
cryptographic implementation. Those require their own contract and adapter.
