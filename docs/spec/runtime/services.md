# Native reusable service references

This profile extends [closed mathematical protocols](../ir/protocols.md)
with owner-local reusable references and explicit, synchronous service queries.
It defines a native execution contract. The [mathematical source profile](../language/protocols.md#managed-services-and-rejection) compares emitted service ports, queries and aliases with its checked source. Native Lean checking remains separate.

## Common IR

`!protocol.service_ref<Contract>` is a reference to one managed service root.
Installed contracts are `random.bls12-381.fr/0`, `random.bn254.fr/0`,
`random.ristretto255.scalar/0` and `random.koala-bear.ext8-binomial3/0`.
These four RNG distributions/providers are the complete registered service
surface. Arbitrary user-defined request/reply families require a future extension.
Each has method `draw`, no arguments, and one result in its named field under
that field's default representation. A contract whose field has the catalog
fact `IndexRandomness` also has method `index`; currently this is only
`random.koala-bear.ext8-binomial3/0`. KoalaBear base has no installed random
service. The contract fixes the distribution signature; it does not authenticate
a root or prove an independence law. A reference is an entry input with exactly one owner. Several inputs may
refer to the same root. Copying a reference preserves identity and does not copy,
reset or fork its state. Dropping a reference does not retire its root.

The admitted operations are:

```mlir
%x = "protocol.query"(%rng) {method="draw", owner="Alice", site="challenge"}
  : (!protocol.service_ref<"random.bls12-381.fr/0">) -> !algebra.field<"bls12-381.fr">
%n = "data.index"() {value="32"} : () -> ui64
%i = "protocol.query"(%octic, %n) {method="index", owner="Alice", site="position"}
  : (!protocol.service_ref<"random.koala-bear.ext8-binomial3/0">, ui64) -> ui64
```

`draw` draws one field element. `index` draws one sample of UniformIndex(N),
whose ideal distribution is uniform on `[0, N)`. Its single data operand must be
defined by a `data.index` constant whose canonical decimal value N is a positive
u64; the domain is therefore fixed before sampling and cannot
be chosen by a received value or other runtime data. Each query changes the
root's state. Its result is available only to the owner. A query is an ordered
occurrence even when its reply is unused. It shares the conservative default
read/write effect resource with communication and guards, so CSE and DCE cannot
merge or remove draws.

### UniformIndex realization

The installed interactive sampler and native transcript suites admit only powers
of two from 1 through 2^63, rejecting other bounds before consuming their root.
An explicit construction handler may implement another positive u64 range;
admission checks its result range, not its claimed probability distribution.
The ordinary [sampling library](../../../libraries/zkc/README.md#bounded-sampling)
provides bounded threshold rejection with explicit exhaustion.

The installed power-of-two sampler obtains 64 provider bytes, reads the first eight as a
little-endian unsigned 64-bit word `w` and returns `w mod N`, equivalently the low
`log2(N)` bits of `w`. If `w` is uniform on `[0, 2^64)`, each result has exactly
`2^64 / N` preimages, so the result is exactly uniform; there is no rejection,
retry or exhaustion event. Whether the provider bytes are uniform is a premise of
that provider (operating-system entropy here, the transcript suite under a
[derived construction](../ir/construction.md#uniformindex-transitions)), not a
property a test establishes. Low bits of a field element are a different
distribution and do not realize this method; for an odd prime they are biased
even at a power-of-two N.

References are used directly by queries. They cannot be selected, restricted,
passed to mathematical helpers, exchanged, returned, or bound as statement data.
Static [protocol applications](../ir/composition.md) pass existing references with exact contracts and mapped owners. `draw` has no data arguments and exactly one field reply;
`index` has its static bound and exactly one index reply. Other distributions,
dynamic bounds,
reference results, ownership transfer,
asynchronous providers and other service contracts require explicit extensions.

## Operands fixed before sampling

A request's operands are the values it reads besides its service reference,
such as the `index` bound. The constant-bound rule above is the static instance
of this contract, which every request operand meets, including dynamic operands
that a future method or construction admits.

1. **Reconstruction.** Both roles compute the operand before the request from
   data both hold: bound public inputs, authenticated configuration, absorbed
   messages and earlier challenge answers. Admission checks that both
   computations are the same pure function of those data.
2. **Binding.** The operand is part of the request and therefore of its
   transcript query: the native construction absorbs it with the occurrence, and
   a provider's serialization covers it.
3. **Validity.** An index bound is at least one and a power of two where the
   method requires it; a block size lies between zero and its static maximum;
   window arithmetic stays in range and overflow is checked. An invalid operand
   stops with `refused` before the transcript state is consumed, at both roles.
4. **Limits.** Every dynamic operand has a static maximum, so executable
   checking, allocation and weighted budgets do not depend on runtime values.
5. **Provenance.** An operand that enters a certificate error, such as a gate
   difficulty, an index bound, a block size, a query count, a blowup, a folding
   arity or an extension degree, is also a bound statement input or
   authenticated configuration, or the validator checks it, before the request,
   against an authenticated bound on the side where the error grows: a minimum
   for a difficulty, a query count or an extension degree, and the static
   maximum for a size. A size the producer supplies stays expressible when the
   verifier checks it against an authenticated minimum and maximum. A bound
   read from the proof with no such check is refused; at zero difficulty or a
   single query it lets a false statement be accepted with probability close to
   one.
6. **Security parameters.** A certificate's error is a function of the request,
   operands included, and each oracle key is charged its worst case over the
   adversary's paths. When the adversary can influence an operand, the effective
   charge is the supremum of the error over the operand's admitted range. A
   production claim needs the operand restricted to an authenticated admissible
   range that supports the claimed bound; binding an attacker-selected parameter
   does not by itself establish a security level. A batch admitted at zero items
   inherits no production claim.

The [construction obligations](../ir/construction-obligations.md) state the
remaining conditions a challenge construction meets.

## Participant representation

Projection keeps ordinary participant SSA arguments data-only and installs a
separate `service_ports` interface. Each row contains a port name, contract name
and original input index in that role's complete input interface. Data arguments
occupy the remaining indices in order. Port names share the participant value
namespace and must be distinct from all data definitions.

`protocol.service_query` names one declared port, method and source site. Its
results are ordinary data SSA values. Projection ends a local calculation before
each query and starts another when its reply is needed. Every owned query is a
demand root; unused replies do not erase service work. Guards and messages retain
their order relative to these queries. Other participants do not execute the
owner's query or acquire its roots.

The derived `protocol.projection` metadata keeps common data input
indices separately from common service input indices. Statement indices still
refer to the original common input interface. This metadata is not an independent
certificate and is not exported in participant JSON.

### Native carrier

The current carrier is [the program format](../formats/program.md), `zkc.program/0`.
The root has five fields. Every participant record has an eighth field containing
service rows `[name, contract, input_index]`, where the index is a canonical
nonnegative decimal string. Participants without services use an empty list.
A query record is `["query", site, port, method, data_inputs, data_outputs]`.
An `index` record has one data input, the bound computed by the participant's
preceding local work, and one `index` output. The carrier does not repeat the
common IR's constant-bound rule; execution refuses an invalid bound before
consumption as described below.
Bounded participant loops may contain queries. Participant calls, static
parameters and family selectors remain outside this contract.

Native carriers enter through `admit_supplied`. Admission checks the closed
contract, method signature, port namespace, indices, query result types and the
installed backend's signature. Supplied admission grants no source correspondence.
Native proof execution additionally requires an admitted deployment and selected
construction policy. Independent Lean models do not provide Program execution correspondence.

## Registry and entry binding

The host issues typed roots through `ServiceRegistry::issue_random_for`;
`issue_random` is the BLS shorthand. A registry-issued reference retains its
contract and cannot be bound to a port of another field. All installed fields
use the same lease, owner, alias, budget, poisoning and cleanup rules.
The host binds authentic references to
exactly the entry's declared service ports. A reference contains registry-issued
authority; an integer or unmanaged affine capability cannot authenticate it.
The registry does not admit externally issued capabilities.

Each root has one owner and one current affine token, private to the registry.
Managed roots have explicit owner custody independent of session-scoped
`Domain` custody. Affine input alias checks apply separately.

Entry validates the full binding and atomically leases each distinct root once,
deduplicating aliases. A root may have only one live endpoint lease. Another
runner is refused even if it presents the same session string. Failed entry
leaves no acquired roots or active backend frames. A tentative lease can cause
brief contention while data-entry validation is in progress; validation failure
releases it and preserves the bindings for retry. A lease is not cloneable.

Normal return, stop, cancellation and runner destruction release the lease and
entry views. Completed draws remain in registry state. Successful entry bindings are cleared on exit; a host reusing the extracted
backend must bind its ports again. Healthy roots may be explicitly rebound by the host to a later session of the same owner; this is
sequential reuse, not state rollback. Cross-owner binding, foreign authorities,
retired roots and poisoned roots are refused. Root retirement is an explicit
host action permitted only without a lease and with known completion.

## Query transition and failure

Polling exposes `Action::Query` containing the cut, port, contract, method,
arguments and reply names/types. Polling alone has no service effect. The host
must execute that exact cut; stale or altered cuts are refused. The host's port
binding identifies the concrete root, which is never encoded into artifact text.

At admission, `Backend::service_support` advertises an independently authored
`ServiceSupport` with the complete method signature and aggregate conservative
reply-byte bound. The runner compares that signature with its declared service
contract. Metadata alone cannot authorize a live resource; port binding and
current lease checks still apply.

Before consumption, the runner checks its output count/retained-byte capacity
against the backend's conservative reply bound. The native backend also refuses
an `index` bound that is not a power of two (`query-bound`) before the registry
marks the root. A preflight refusal consumes nothing and does not poison the root. A trusted service backend must keep signatures and bounds stable,
validate requests before consumption, and preserve completed state on error.
It must poison the affected root when a reply fails validation or binding after
consumption, through `reject_service_reply`.

The native registry performs consumption and successor installation under one
mutex. It marks the root unavailable before consumption. Success installs the
successor token and exposes the reply. Ordinary consuming failures, including
budget exhaustion and entropy failure, preserve the authoritative generation,
draw count and remaining budget, and poison the root. Every alias then refuses
further execution. Reply validation failure after a successful consume also
poisons that root without undoing its completed state.

An unexpected unwind during consumption leaves completion unknown and poisons
the root. Observation then omits exact residual state, and retirement/rebinding
are refused. The unwind is caught inside the registry lock so other healthy
roots remain usable. Process abort, allocation abort and crash recovery have no
in-process residual-state guarantee.

Queries are synchronous and borrow the endpoint lease. Cancellation runs only
between completed actions; no cancellation window exists between consumption
and registry update. This is not an asynchronous cancellation contract. The
current mutex serializes transitions across roots within one registry; it is a
correctness mechanism, with no parallel performance claim.

## Evidence boundary

The generated-candidate checks exercise same-root aliases, independent roots,
query ordering, unused queries, actual native messages, guards, sequential reuse,
capacity refusal, failure poisoning and lease cleanup. A deterministic test tape
makes consumption visible; it does not establish a cryptographic randomness law.
The production adapter uses the existing native sampler. Its cryptographic
assumptions and any protocol security argument remain separate obligations.
The [preservation guide](../../compiler/verification.md) describes the
implemented common-to-participant checks and their evidence limits.


### Service input index spaces

The retained mathematical interface uses indices into the original common
signature. A participant's service-port record uses the ordinal in that role's
own advertised ingress interface, counting both ordinary data and services.
An earlier common input owned only by another role therefore changes the first
index without changing the second. The retained per-role maps connect those
interfaces; runtime participant admission uses the role-local ordinal.

## Queries in native iteration

The program contract supports borrowed port aliases inside
[structured iteration](../ir/iteration.md). The reference still originates
at entry, retains one owner/root/lease, and cannot be sent, selected or returned.
The loop frame inherits its service port map without acquiring another lease.
Zero trips perform no body query; each reached query advances the same root once.
Nested return releases frame state without releasing entry authority. Final stop,
return or cancellation retains completed service state and releases the entry
lease. All these rules use the same closed program carrier.

## Why separate ports

Entry-bound service references project to named ports and visible query cuts.
Since operations cannot produce or dynamically select references, ordinary value
flow would extend value and physical-type consumers without serving this
contract. A copyable reference type could also preserve token discipline; it
becomes useful when a concrete composition needs reference results or dynamic
selection. Hiding queries in ordinary local helpers would hide scheduler cuts.
