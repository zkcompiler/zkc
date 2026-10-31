# Scoped helper expansion

Ordinary helper expansion operates on admitted standard `func.func` bodies with
explicit scope and outcome control. The compiler retains the original and reads
the actual candidate independently before publication. The
[formal bridge](../../../lean/docs/spec/structured-source.md) imports its declared
subset; general native expansion retains its own correspondence obligation.

## Formation and intermediate representation

A role-free executable helper is a scoped standard function. Its body carries
ordered primitive applications, closed control bodies and explicit completion
or stopping outcomes. Ordinary helper calls borrow the caller's scope. Typed
mathematical computations and finite requests remain visible until numerical
realization selects and independently checks their implementation.

The source reader admits the complete closure, including dormant definitions,
resolved symbols, signatures, explicit capture coordinates and static data
premises. The call graph is acyclic and a path has at most 64 edges. Declaration
order does not provide scope. Indirect calls, unresolved or external callees,
and calls to protocols are not ordinary executable helper calls. `.zkc` static
checking belongs to the [Language profile](../language/README.md).

Affine-use and nominal-type checks apply at each call boundary and inside each
callee. Passing an affine argument consumes that binding; only declared results
are available afterward. Repeated use, repeated return and wrong nominal types
are refused before expansion. An executed `control.require` remains an ordered
primitive even when the caller does not use any ordinary result.

A callee may stop without producing its declared results. Substitution preserves
that stop and removes the unreachable caller suffix on that path. Branches and
loops retain their explicit outcome and continuation structure. No undefined
result is fabricated to satisfy a join.

## Expansion and accounting

Each call substitutes actual arguments, retains primitive order and binds the
returned aliases into the caller. A borrowed helper return introduces no local
completion charge. The caller suffix executes only after normal return.
Expansion does not remove, reorder or speculate primitives or reached effects;
multiple call occurrences execute distinct copies.

Returned aliases can identify distinct duplicable capture bindings. Expansion
keeps the first actual capture and rewrites every corresponding formal position,
including static data premises, consistently in the outlined region. The source
affine checks still apply: capture canonicalization does not authorize copying
resources.

The enclosing participant invocation owns its runtime local frame. Entered
control regions create the child scopes specified by the
[execution contract](control.md#execution). Intermediate values remain in their
owning scope until cleanup or checked storage release. Physical conversions and
inserted releases retain their separate accounting rules.

Expansion does not claim exact resource equivalence to an interpreter that
allocates a new frame or charges at every source helper call. It preserves the
canonical scoped execution contract, including first failure, reached effects
and consumed resource state. Fixed-budget failure remains observable; a
sufficient-resources premise does not erase it. Formal results for a selected
primitive interpretation do not automatically prove native allocation behavior
or source elaboration correct.

Construction and independent checking have separate cumulative limits. The
standalone producer allows 100000 construction units and 16 MiB of occurrence
encoding work; a containing numerical transaction supplies its shared remaining
allowances. The producer charges visited operations and their SSA coordinates,
including repeated helper substitutions and outlined bodies, before allocation.
Generated definition and binding inventories are bounded separately. The
independent reader starts with its own 1000000-unit checking allowance and reads
the actual source and candidate; it does not trust producer counters or a
selection plan. Existing source and carrier limits apply independently.

A refusal publishes neither a candidate nor partial requested origin records.
Compile-time capacity refusal is not a protocol execution result. Optional
numerical comparison capacity can trigger the specifically permitted ordered
retry; semantic mismatches remain terminal. Neither the journal nor a generated
name establishes correspondence.

## Origins and identity

An expanded occurrence retains its enclosing function, ordered call/callee path
and original leaf site. The encoding is `lc` followed by
`_BYTE_LENGTH_COMPONENT` for every path component and the leaf. Encodings longer
than 48 bytes use `lc_h_` followed by the unpadded base64url encoding of the
complete SHA-256 digest (43 characters, alphabet `A-Z a-z 0-9 - _`);
the complete path remains in the independently recovered origin record. The
encoder charges the complete pre-digest length before constructing the string.

Standalone helper expansion encodes occurrences consistently in producer and
reader. Integrated numerical preparation retains top-level occurrence sites and
prefixes nested helper paths. The reader derives the actual path from source
calls and compares it with the candidate; copied origin metadata is insufficient.

`.zkc` function origins identify qualified definitions with empty native static
bindings; the checked closure and emitted symbol retain the actual static
selection. Native proof construction resolves actual prepared occurrences under
its [origin contract](construction.md#transcript-state-and-occurrence-identity).
Dynamic iteration coordinates remain explicit.

Native artifact identity binds exact bytes under the
[artifact identity contract](../../runtime/artifact-identity.md).
