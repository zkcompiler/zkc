# Nominal data and execution boundaries

`Zkc.Source.Structured.Ty` owns the recursive type vocabulary.
`Zkc.Source.Structured.Carriers.Value` is its value interpretation. A model
supplies arithmetic and helper semantics for those carriers; selecting a Lean
carrier does not prove field, group, embedding or sampling laws.

## Typed source values

Source admission checks complete nominal descriptors, ordered operands and
results. Fields remain distinct even when a mathematical interpretation uses
the same carrier. Products retain their nominal identity and ordered children;
sequences and fixed vectors remain different types, including at length zero.
No interpretation of a runtime value by itself proves a protocol relation,
length bound, finite sampling universe or byte-codec law.

Logical handles have their own ownership and custody checks, including handles
inside supported logical aggregates. A handle is not permission to read its
logical payload. Transporting ordinary data and realizing an oracle are
separate boundaries. See [structured source](structured-source.md) for the
admitted vocabulary and [source construction](source-construction.md) for the
mathematical interpretation boundary.

## Public statements and realization

A source-relative claim retains its actual subject, ordered observations,
selected interpretation and requested relation. Mapping those values to a
public statement or transcript requires an exact association, not equality of
Lean carrier types or matching lookup names.

The previous constructed-domain payload, public-binding and participant
interpreters are retired. Their nominal codec and concrete transcript claims
are withdrawn with them. Native types, publication formats and runtime codecs
remain governed by the [shared contracts](../../../docs/spec/contracts.md).
A new formal realization must prove its data, outcomes and resource relation
against those actual contracts; this page asserts no compiled-byte connection.
