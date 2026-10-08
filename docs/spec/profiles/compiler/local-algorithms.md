# Canonical local algorithm expansion

This profile expands acyclic ordered local applications before participant
projection. The independent [stored-definition model](../source/definitions.md)
supplies selected inlining laws; native expansion and accounting have their own
[preservation checks](../../../compiler/preservation.md).

## Formation and intermediate representation

A local definition contains ordered primitive operations, role-free applications,
[structured local regions](local-control.md) and a return or explicit stop.
`local.apply` names a closed local definition and supplies its ordered argument
and result types. The mathematical profile also permits
[data-only helper realization](mathematical-protocols.md#executable-local-calls-and-type-use);
preparation materializes it before expansion. No unresolved helper or static
selection enters the executable. `.zkc` static checking belongs to the
[Language profile](../source/mathematical-language.md).

The local call graph, including unused definitions, is acyclic and has at most
64 edges on a path. Captures are explicit; declaration order does not supply
scope or authorize an unresolved reference.

The ordinary affine-use checks apply at each call boundary and inside each
callee. Passing an affine argument consumes that binding; only declared results
are available afterwards. Repeated use, repeated return, or a wrong nominal type
is refused before expansion. This does not make every Boolean a mandatory-use
verdict. An executed `control.require` remains a guard even if all other results
of its containing helper are unused.

A callee may stop without producing its declared results. Expansion preserves
that stop and removes the caller suffix on that path. If specializing every arm
of an `if` or `match` leaves a join with declared results but no producing arm,
expansion refuses at that control operation (`algorithm-terminal-results`); it
never emits undefined or invented results.
An explicitly result-less all-stopping region remains supported.

Native common IR retains these applications as typed `local.apply` operations
inside isolated `local.func` definitions. Module admission checks the call graph,
local-only scope, complete signatures and affine use as well as MLIR's symbol
and SSA checks. Arbitrary control-flow regions, indirect calls, external callees
and calls to protocols are not legal local applications. Participant and physical
IR require all local applications to have been expanded; residual `local.apply`
operations are refused at export.

## Expansion and accounting

The policy identifier is `canonical-expanded-locals/1`. It defines execution of
this subset by ordered, capture-free expansion before projection. Each nested
call substitutes its actual argument values, retains every primitive in source
order, and binds its returned aliases into the caller. A return adds no primitive
and runs the caller suffix only after the callee's primitives complete. No
primitive, guard, sample or semantic failure is removed, duplicated by sharing,
reordered or speculated. Multiple call occurrences execute distinct copies.

Returned aliases can make distinct duplicable capture bindings denote the same
value. Expansion retains the first capture occurrence, substitutes the region
arguments consistently, and removes duplicate loop capture forwarding. This
also applies inside nested regions. Affine argument reuse is still refused
before expansion; capture canonicalization does not authorize resource copying.

Native instruction, allocation and retained-value budgets apply to the resulting
executable body under the existing participant and backend policies. There is
one runtime local frame at the enclosing protocol `local` action. An inner
`apply` has no runtime frame, entry charge, return charge, or local destruction
point. Entered local control regions do create child frames under the
[local-control accounting contract](local-control.md#execution). Intermediates
remain in their owning frame until its cleanup or a checked storage release. Physical conversions and inserted
releases retain their existing accounting rules.

This policy does **not** assert exact resource equivalence with an interpreter
that allocates a frame or charges for every source `apply`. In particular,
flattening can extend lifetimes. Fixed-budget native failure and exhaustion are
observations of the canonical expanded machine; no sufficient-resources premise
is used to erase them. Complete logical primitive results include returned or
stopped outcome, reached effects, consumed resource state and the first failing
occurrence. The existing formal inlining theorem applies to its own selected
primitive interpretation, not automatically to native allocations or raw source
elaboration.

Compile-time expansion is separately bounded. Native expansion charges each visited instruction and region body, including empty
callees and both conditional arms, against 32768 visits across the local definitions. Existing module
instruction and byte limits still apply to the output. A call path has at most
64 edges, and an encoded operation site is a source name of at most 128
bytes. Limit failures are compiler refusals, not protocol execution results.

## Origins and identity

An expanded primitive occurrence retains its enclosing function, ordered
application/callee path and original primitive site. The encoding is `lc`
followed by `_BYTE_LENGTH_COMPONENT` for each path component and leaf site.
Functions without applications retain their sites. Generated names and debug
locations are not evidence of source correspondence.

`.zkc` function origins identify qualified definitions with empty native static
bindings; the checked closure and emitted symbol retain the actual static
selection. Native proof construction resolves actual prepared occurrences under
its [origin contract](native-proofs.md#transcript-state-and-occurrence-identity).
Dynamic iteration coordinates remain explicit. The compiler compares expanded
operands, order, attributes and resource flow against retained input; it does not
accept copied origin metadata as a substitute.

Native artifact identity is exact. No normalized source selector or compatibility
policy is supplied by this profile.
