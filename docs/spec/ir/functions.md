# Canonical local algorithm expansion

This profile expands acyclic ordered local applications before participant
projection. The independent [stored-definition model](../../../lean/docs/spec/profiles/source/definitions.md)
supplies selected inlining laws; native expansion and accounting have their own
[preservation checks](../../compiler/verification.md).

## Formation and intermediate representation

A local definition contains ordered primitive operations, role-free applications,
[structured local regions](control.md) and a return or explicit stop.
`local.apply` names a closed local definition and supplies its ordered argument
and result types. The mathematical profile also permits
[data-only helper realization](protocols.md#executable-local-calls-and-type-use);
preparation materializes it before expansion. No unresolved helper or static
selection enters the executable. `.zkc` static checking belongs to the
[Language profile](../language/README.md).

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

The policy identifier is `canonical-expanded-locals/0`. It defines execution of
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
[local-control accounting contract](control.md#execution). Intermediates
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

Compile-time expansion is separately bounded. One preparation invocation owns
32768 **substitution visits** across all local definitions and both expansion
phases. Expanding a call in a root definition charges that call and every
instruction visited in the substituted callee, including returns, nested region
bodies, both conditional arms and further calls. An empty helper still charges
its return. Repeated invocations are charged separately, including copies of a
helper whose own declaration was expanded earlier. Budgets never restart at a
function, protocol entry or phase boundary.

The existing body of each root definition belongs to **source inspection**:
each body operation, including nested operations and terminators, is charged
once per phase against a separate cumulative 1000000-operation allowance before
selection or expansion. Merely preserving or copying existing root instructions
does not consume substitution visits. This separates bounded source traversal
from the potentially exponential work of substitution. The independent reader
has its own cumulative 1000000 checking allowance, checks preserved bodies as
well as expanded ones, and recomputes both producer balances. Existing module
instruction and byte limits still apply to the output. A call path has at most
64 edges, and an encoded operation site is a source name of at most 128 bytes.
Limit failures are compiler refusals, not protocol execution results.

`RetainMaps` selects every local definition that transitively calls an admitted
map, finite fold or finite collect declaration. It also selects local callbacks
named by each finite declaration's `step`, `body` or `predicate` attribute when
those callbacks contain calls. These references are preparation dependencies
even when the callback's ordinary call chain reaches no preparation declaration.
In each selected body it expands the full transitive ordinary helper chain,
including scalar reducers, retaining only admitted preparation calls. Callback
selection does not select unrelated callers of the same callback or helpers.
Helper copies are charged to the callback root; each helper's own declaration
is selected only if it independently meets these rules. Other local definitions
and call-free callbacks remain exactly unchanged, including their sites.
Selection includes unused definitions and unused finite declarations and does
not depend on which protocol entry currently refers to them. `Finish` requires
preparation declarations to have been realized, expands every remaining caller
and preserves call-free definitions exactly. In each phase the reader independently
derives which definitions require expansion. Unchanged definitions are compared for
operation order, attributes, SSA operands/results, block arguments and regions;
diagnostic locations are excluded. Neither unchanged-body handling nor an empty
retention selection waives admission or staged correspondence checking. Candidate
IR, occurrence state and requested origins publish atomically after checking.

## Origins and identity

An expanded primitive occurrence retains its enclosing function, ordered
application/callee path and original primitive site. The encoding is `lc`
followed by `_BYTE_LENGTH_COMPONENT` for each path component and leaf site.
Functions without applications retain their sites. Generated names and debug
locations are not evidence of source correspondence.

Staged expansion records paths relative to each declaration. When preparation
introduces a new call to a previously expanded helper, expansion prefixes those
recorded paths with the new invocation path and adds its depth. Nested regions
retain that invocation prefix exactly once. The independent reader checks the
composed paths, depths and unique occurrence records.

A raw declaration preserved during retention has not yet been expanded. Its
sites receive their first canonical encoding if `Finish` expands that body.
Previously expanded occurrences instead keep their checked paths and sites,
including when the entire function is now call-free. Inspection alone does not
create an expansion path or erase an existing one.

`.zkc` function origins identify qualified definitions with empty native static
bindings; the checked closure and emitted symbol retain the actual static
selection. Native proof construction resolves actual prepared occurrences under
its [origin contract](construction.md#transcript-state-and-occurrence-identity).
Dynamic iteration coordinates remain explicit. The compiler compares expanded
operands, order, attributes and resource flow against retained input; it does not
accept copied origin metadata as a substitute.

Native artifact identity binds exact bytes under the
[artifact identity contract](../../runtime/artifact-identity.md).
