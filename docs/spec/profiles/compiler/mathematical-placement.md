# Mathematical placement and pure outlining

Placement maps an admitted [mathematical protocol](../source/mathematical-protocols.md)
to an independently admitted located common protocol. Both subjects are
retained. The placed carrier extends the existing
[common protocol](../source/common-protocols.md) with inline total pure regions
and public indexed iteration; participant projection needs the same cases.

## Witness and checking judgment

The [format owner](../../../compiler/mathematical-format.md) defines the
serialized witness. Its semantic obligations are:

- Every mathematical role component in the independently computed demand domain
  maps to a typed located binding. The domain includes argument interfaces,
  ordered results, declared results and the backward closure of effect/result
  operands through total nodes. The witness cannot select its own coverage.
  Availability is checked against the actual source.
- Each message's sender component renames its existing sent operand. Its
  receiver component maps to a fresh receive binding. The schema, peer,
  origin and effect order agree. No received value is replaced by an honest
  sender expression.
- Public/relation bindings, ordered result ports and explicit product packing
  agree. The per-role result map bijects source ports with typed target subtrees,
  covering every product leaf exactly once; empty products require explicit
  entries. Unused internal aliases are not additional result ports.
- Calls preserve actual callee bodies, static substitution, injective role
  bindings, captures and capability aliasing. Loops preserve count, index,
  invariant ports, yield and iteration path.
- Source services, stops and their dynamic paths agree. Pure node elimination
  or duplication uses the admitted total interpretation; no effect is merged.

With checked correspondence of actual local libraries, operations, wires,
roles, root identities and dynamic sites, the required theorem is:

```text
checkPlacement(M, L, witness) = true
  -> for every role r,
       mapResult(witness.resultMap[r],
         renameInterface(witness, openMeaning(M,r)))
           = locatedMeaning(L,r)
```

`renameInterface` uses the common checked declaration tables and reply types;
it preserves root aliasing and maps each invocation/iteration frame.
`mapResult` transforms successful ordered ports and preserves every effect
and stop. Meanings are defined independently of the checker and of each
other. Hashes identify captured artifacts; checking uses the actual admitted
terms. A matching digest is not a proof of semantic equality.

The judgment includes all well-typed receive/service replies. Honest-only
testing cannot discharge it. Handler refinement can subsequently transport
complete executions, including stopped post-state and prior events.

## Inline pure regions and outlining

The inline checkpoint interprets a pure region as `.done(eval(args))`.
Existing `localCall` instead exposes a service action whose reply may be
arbitrary. Replacing one by the other does not preserve the raw open `Proc`.

For an outlined candidate require:

```text
foldIntroducedPureCalls(witness, outlinedMeaning) = inlineMeaning
```

The checked map identifies only compiler-introduced pure calls and checks
their actual definitions, typed arguments and result packing. A reference
handler executes those definitions; installed operation laws establish the
corresponding `.done` result. The fold introduces no semantic state change
or source event. All original services, queries, messages and stops are
forwarded unchanged. A general event erasure cannot hide a genuine service.

Physical allocation/kernel events, lifetimes and resource failure belong to
the separate [representation relation](../../realization/representations.md).
It must preserve the selected complete outcome on its stated resource domain.
The mathematical purity law does not supply that physical theorem.

## Conformance

A conformance claim identifies the covered constructors and actual supplied
checker, operation meanings and representation premises. Existing projection
laws apply only to their own grammar. [Status](../../../status.md#mathematical-protocol-foundation)
reports implemented coverage.
