# Closed operation bindings

This profile makes nominal domains and operation applications explicit in the
common-protocol carrier. Profile names are authoring defaults elaborated
into explicit bindings; the portable carrier does not accept a profile
string in place of those bindings.

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

The protocol and participant carriers retain an explicit operation-binding
array alongside their callable bodies and entry points:

```
["zkc.protocol/1", bindings, functions, protocols, instances, entries]
["zkc.participants/1", bindings, stage, functions, participants, entries]

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

Logical value types have the spelling `kind:identity`, except `bool`, which has
no domain argument. Examples are `table:bls12-381.fr`, `group:bls12-381.g1` and
`proof:multilinear.kzg.bls12-381/1`. A physical type adds `@representation`.
The spelling is a transport: MLIR retains separate logical type and
representation parameters in `!plan.data<logical, representation>`.

The text form omits a module-wide profile:

```text
module {
  bind empty = poly::empty_point(bls12-381.fr);
  fn Empty() -> Point<"bls12-381.fr"> {
    let point = empty();
    return point;
  }
}
```

In MLIR, `pir.operation_binding` is a symbol declaration. Mathematical dialect
operations reference it with a `binding` symbol attribute. This includes
operations with no operands: their result domain is explicitly selected.
The common-protocol interaction and role-projection structure is unchanged.

The finite numerical installation also admits `koala-bear` field, vector, matrix,
coefficient-polynomial and quadratic-round carriers with Plonky3 implementations.
Field facts remain independent of group and PCS associations. The octic
extension, its selected transcript/index-sampling suite, and the separately
named [vector commitments](../../domains/oracles.md) add their own capabilities;
they do not manufacture a group or multilinear opening capability. Unavailable operations or
wrong-provider selections refuse. The [domain guide](../../../compiler/protocol-libraries.md)
and [wire catalogue](../../../compiler/artifact-format.md#explicit-vector-and-ristretto-domains)
record the implementation boundary; generic signatures remain independent of
these installed choices.

Transcript observation selects its payload identity and codec independently from
the transcript's challenge domain. For example, `transcript.observe.table` takes
transcript, coefficient field and codec identities and requires `Encodes.table(E,F)`.
The installed `zkcv.table.bls12-381.fr/1` codec is the existing ZKCV version-one
framing and logical MSB-coordinate scalar serialization. The generic contract
does not equate the observed field with `T.ChallengeField`. Challenge generation
does use the transcript construction's associated challenge field.

Function records carry a logical-origin pair, consisting of the
original definition name and ordered static parameter bindings. MLIR stores it
as `logical_origin`; projection and planning preserve it. Generated executable
symbols and implementation choices are separate. Ordinary source functions use
their declared name with no static bindings by default; an explicit origin can
group functions without equating them.

Concrete symbols and logical origins are separate namespaces. An explicit root
origin reserves its actual logical origin, not the function's concrete name;
ordinary helper specializations can share an origin with an existing concrete
function. Self-origins, shared groups and materialized configurations' generic
definition origins are valid. Neither the origin spelling nor a generated-symbol
prefix grants declaration authority. Preserving origin metadata is not by itself
a proof that native code implements the original generic definition.

## Representations and conversion

Physical planning resolves each operation binding independently. Callable and
control interfaces take the installed default physical ports. Kernel
results receive the selected implementation's ports. Consequently, two values
with the same logical type may have different physical types in one artifact.

For tables, `arkworks.mle-lsb/1` and `arkworks.mle-msb/1` denote different actual
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

Fixed implementation selections are supplied to the native driver with
`--implementations=FILE`, containing `[binding_symbol, implementation]` pairs.
Unknown symbols, duplicate selections and incompatible implementations fail.
Planning is transactional: an unsuccessful selection leaves the logical MLIR
module intact. This interface supplies reproducible fixed choices, not search.

## Implementation boundaries

- [Native contracts and types](../../../../compiler/include/zkc/Protocol/Bindings.h)
  and [MLIR planning](../../../../compiler/lib/Protocol/BindingPhysical.cpp).
- [Mixed operation fixture](../../../../tests/fixtures/bound-operations.pir)
  and [native pipeline controls](../../../../compiler/test/bound_protocols.py).
- [Generic static requirements](generic-definitions.md).

This carrier does not implicitly interchange opening protocols with different
interaction behavior, add mathematical field coercions, or prove the external
cryptographic implementation. Those require their own contract and adapter.
