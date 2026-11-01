# Protocol observation analysis

`ProtocolObservationAnalysis` is a builtin-module analysis of admitted,
immutable Protocol IR. It composes the actual definitions and repeats supplied
by [InteractionAnalysis](interactions.md) and the actual helper bodies checked
by [ExecutionObservationAnalysis](execution-observations.md). It does not run
preparation, build another executable graph, or admit a source module. The
independent public-coin requirement and construction checker remain separate
consumers. In particular, this analysis does not establish transcript binding,
an authenticated provider, an encoding's injectivity, or a sampling theorem.

## Shared summaries and dependence

A summary belongs to one actual declaration or repeat block and one observer
role. Its formal ports are the block arguments. An application substitutes the
actual arguments and maps the observer through the application's actual role
map. Callee summaries are shared; two applications of a shared callee still
have distinct occurrence identities. A repeat has one retained body summary,
not one copy per iteration or per maximum.

Each summary's dependency basis contains its formal inputs, observed queries
and receives, and references to child call/repeat results and stops. A child
reference denotes the actual child transfer through that action's argument
substitution. It is neither an unconstrained received value nor independent
randomness. Formal dependencies are substituted directly; nonformal child
observations retain these explicit references. A reader follows the resulting
definition DAG and the actual call/repeat associations. Zero-width dependency
vectors denote unavailable role components; an atom-free definition internally
uses one unset padding bit to distinguish an available constant.

A receive at the observer creates a new observed value instead of following
the sender's private expression. Role assembly selects only the actual
observer component. Mathematical operations use their semantic dependency
interface. Numerical and total helper calls use the checked numerical summary,
including possible logical stops from unused and zero-output local calls.
Unknown observer effects refuse. A dependency is a conservative may-depend
fact, not a claim that an input influences the result or that the operation
will be reached. Summaries can include infeasible continuations; a consumer
must not infer successful execution from a summary's existence.

Logical guard, helper and repeat-count stop dependencies contribute to later
observations and returned results. Host allocation, execution budgets and
provider availability do not become logical data dependence. Numerical
primitive interpretation premises remain attached to the actual helper
summary, including its binding, parameters and selected implementation.

Repeat carry uses a finite monotone fixed point. It includes the initial carry
for zero iterations, count/iterator dependence, captures and body transfer.
The repeat's symbolic result/stop references retain the body association.
Equal maxima, coincidentally equal values, or the initial carry alone do not
establish an invariant. Work exhaustion refuses instead of returning a partial
fixed point.

## Exact challenge delivery

Exact identity is separate from dependency. Origins are unknown, a formal
port, or an actual call path ending at a query. Only exact forwarding through
actual formals, restrictions and role assembly preserves a challenge identity.
Arithmetic reconstruction does not, even when it mentions the challenge.

A pending transfer has an incoming requirement (`Any`, `Empty`, or one exact
formal) and an outgoing state (`Preserved`, `Empty`, or an actual query).
`Preserved` denotes the symbolic incoming pending state, not emptiness.

- An observed query requires no pending challenge and creates a fresh one.
- A received prover message also requires no pending challenge.
- An outgoing verifier delivery consumes exactly the pending identity.
- An independently selected deterministic data exchange requires an empty
  pending state and observed operands; it is not a challenge delivery. The
  realized-candidate consumer obtains these exact operation associations from
  its checked realization owner. Names, prefixes and untrusted record fields
  cannot select them. Without that selection, an outgoing verifier exchange
  must be an exact challenge delivery.
- A helper may deliver a formal supplied by its caller, or return a query for
  delivery by a later helper. Local completion of a round is not required.
- Calls substitute origins and prefix query identities with their actual
  application occurrence. Shared callee identity does not equate draws.
- A repeat must preserve any incoming pending state unchanged, or be a closed
  `Empty` to `Empty` round. Consuming an incoming challenge only on the first
  iteration is outside the profile. A last-iteration query does not escape as
  one exact identity for the repeated family.

These are ordered transfer rules. Dependency joins cannot discharge them. The
top-level consumer must independently require an initially and finally empty
pending state and resolve its requested query/delivery selectors against the
actual structure. Source labels alone supply no cryptographic separation.

Queries retain their exact method, actual operands, result type and formal
service association. `draw`, `index` and `indices` have their distinct installed
service signatures. The source admission owner still decides admissible
request operands; this analysis does not enlarge that profile or reinterpret
a product draw as several scalar draws. Provider conformance and successful
request conditions are additional premises. Every queried service is traced
through exact aliases to a formal port for independent consumer selection.

## Ownership and limits

The caller supplies cumulative `facts::Work`. Interaction extraction, retained
availability associations, transfer, substitution, bit-set joins, identity
paths and cache queries are charged. The analysis permits at most 1,024 formal
or return ports per block, 2,048 retained site-bearing actions across summaries,
65,536 atoms per summary, depth 64, and 64 query families per composed subject.
A repeat counts a query family once and retains its dynamic coordinates; this
does not identify its samples. No iteration maximum is unrolled.

Failure is sticky until `clear()`, with owner, unsupported-semantics and capacity
refusals. Cache pointers are stable until clear, invalidation or destruction.
Clear **before** changing any inspected body, role, type, binding, symbol or
policy. Clearing drops occurrence selections; a changed realized subject needs
a new selection from its checked owner. Source and candidate snapshots require
distinct instances. All reads
of sibling helpers occur under the builtin-module analysis owner. This analysis
is not thread-safe and grants no mutation or serialized-report authority.
