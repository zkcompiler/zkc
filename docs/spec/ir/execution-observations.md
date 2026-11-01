# Execution observation analysis

`ExecutionObservationAnalysis` summarizes the logical observations of actual
admitted numerical helpers. It is a builtin-module MLIR analysis, with the
same immutable-subject lifetime as `InteractionAnalysis`. Its native consumer
is the structured verifier observation checker. This document specifies the
summary; the public-coin policy and serialized report have their own owner.

Each summary contains formal-port dependency sets for returned values, a set
for possible logical stops, and separate `mayReturn` and `mayStop` flags. Scope
ports are administrative and are excluded. Sets are conservative: they are not
proofs that changing an input changes an output, that an encoding is injective,
or that a transcript binds an input. A stop is distinct from returning false.
Budget, allocation, provider availability and cleanup failures remain outside
this logical observation judgment.

The analysis consumes `protocol::readSourceExecutionClosure`, which checks the
actual scope/outcome CFG and recovers its structured association. It does not
reconstruct another executable graph. Mathematical helpers use `TotalClosure`.
Numerical calls substitute actual dependency sets into cached formal summaries.
An eager call is inspected even if it returns no data or its results are unused.
Its possible stop dependencies affect all subsequently reached observations.
Unknown semantics refuse the query; they never supply an empty dependency set.

Branches include the actual condition or variant scrutinee, distinct capture
formals and the selected payload. A stopped arm does not supply successful
results. Loops retain the initial carry as a zero-trip possibility and compute
a finite monotone fixed point through carry, iterator, bounds and conditional
backedges, without enumerating an iteration maximum. Finite fold/collect reuse
the checked callback ABI and inspect the actual body and predicate. Their
dependency transfer conservatively closes all domain, state and capture inputs
together; it does not claim element-level dependence precision.

Installed primitives require the `DeterministicData` facet and immutable logical
data types recursively. Copyable public-value constructors include commitments,
proofs and finite polynomial carriers; mathematical-expression eligibility is
not the criterion for immutability. Private immutable support is explicitly
limited to sequences, finite field arrays, fixed vectors and SHAKE snapshots, with all Type children
and variant payloads checked recursively. Formal polynomials and quotient-ring elements are immutable algebraic values
without executable ports; observation grants no wire encoding. Private setup keys, opening-state
handles and affine services are excluded; Copy alone grants no data authority.
Generic Type formals do not grant or deny this interpretation: the explicit
facet is checked on the actual recursively immutable input/output types. A
declaration-level conservative effect classification cannot substitute for
that instantiation check. In particular, an immutable sequence of public data
is accepted while a sequence containing private authority remains refused.
This facet is partial: all inputs can affect a logical
stop. The direct primitive occurrences are retained as actual IR references,
including their binding, parameters and selected implementation. The summary
is conditional on the exact interpretation of those selections; a default
interpretation is not silently assigned to a custom implementation.
Service/resource operations and unclassified effects refuse. `PublicReplay`
alone is insufficient. Direct callee references form a shared summary graph;
they do not expand repeated calls into duplicate instruction histories.

The caller supplies one cumulative `facts::Work`. Reading a scoped closure
debits its actual retained IR, including dormant definitions. Constructing
summaries debits transfers, substitutions and joins. Cache queries debit summary
width, and consumers debit their own substitutions and report traversal. Each
function has at most 1,024 data inputs/results and a maximum call depth of 64,
including cached heights. Work/depth exhaustion is sticky. Failures distinguish
`execution-observation-owner`, `execution-observation-unsupported` and
`execution-observation-capacity`. No partial summary is returned.

The owner must clear the analysis **before** changing any body, binding, layout,
type or selected policy that it inspected. Pointers remain valid until that
clear, pass invalidation or destruction. Different source/candidate snapshots
require distinct instances. Sibling helpers are inspected only under the
builtin-module owner, consistent with MLIR analysis and pass ownership.
