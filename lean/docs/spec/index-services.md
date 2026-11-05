# Typed scalar and block index services

The Structured service operation family is `ServiceOp`. Its constructors are
`draw field`, `sampleIndex contract`, and `sampleIndices contract`. An index is
ordinary `Nat` data after checked decoding; a block is one `List Nat` result of
one service operation. Neither operation reduces to a field draw or to another
number of service operations. Service identity remains nominal.

The original source descriptors are `sample_index owner contract` and
`sample_indices owner contract`. Their ordered SSA operands are respectively
`[service, bound]` and `[service, bound, count]`. Source admission requires
positive constant-u64 bound/count operands, exact service root and owner, exact
signature and method, and the separate `IndexRandomness` or
`IndexBlockRandomness` catalogue capability. Literal provenance survives
immutable application/repeat captures; an induction value, mutable carried
state, or arithmetic result does not acquire literal provenance. Original query
sites and constructed occurrence annotations are checked independently.

`ServiceExecution.serviceAction` checks formation before issuing a source
effect. A source service can stop or return an arbitrary carrier value. A scalar
reply outside the requested range, or a block with the wrong length or an
out-of-range entry, stops with `refused` before entering its continuation. This
adversarial interface imposes no honest distribution assumption.

`Construction.Request` is the strict request wire record. `valid` and
`operation` recognize exactly the three method/operands/result-sort combinations.
The index and block smart constructors store **evaluated values** `[bound]` and
`[bound, count]`, never SSA reference numbers. The whole request is part of
`Origin` and the transcript event/key. Method, order, bound, count, nominal
contract, source occurrence and ancestry cannot be discarded from that key.

For positive bounds the ideal raw scalar carrier is exactly `Fin bound` and the
block carrier is `Fin count → Fin bound`. The decoder produces the scalar value
or `List.ofFn` of the block values. Its laws give the exact count and range. To
keep the total oracle signature nonempty even at malformed zero-bound keys,
the actual definition uses `replyBound bound = max bound 1`. Zero-bound requests
are refused before effects; `replyBound_of_positive` proves the exact admitted
specialization. No unbounded uniform choice or `SampleableType Nat` is added.
`ServiceSampling` reuses the pinned VCVio finite and finite-function instances
and their uniformity proofs. Its `raw` family requires explicit samplers for
each nominal field and supplies finite inert carriers for unsupported keys.
Those optional ideal samplers do not interpret an adversarial source service.

The native scalar constructed operation has dynamic operands
`[transcript, bound-reference, coordinates]` and one origin parameter. Rendering
retains the bound's actual constant value in `indexChallenge`; execution checks
that the dynamic reference denotes that value. The native block operation has
operands `[transcript, coordinates]` and parameters `[origin, bound, count]`;
`blockChallenge` retains those static values. Its result is ordinary indices
data plus the new transcript. Coordinate lists are an internal runtime sort,
distinct from ordinary indices data although the native logical type spells
both `indices`. Local service operations retain ordinary bound/count references
and read their values separately from their source annotation.

The native scalar and block providers support power-of-two bounds through
`2^63`; the block count is at most `1048576`. `Request.nativeSupported` is their
separate constructed-provider predicate, checked before effects by the
constructed rule and execution kernel. Strict native-operation rendering also
checks these limits (the block parameters have their own composite schema). They do not narrow positive constant-u64 formation of all source or
private services. In particular the private fixture uses bound 3, and source
formation controls accept a count above the provider cap.

`Domain.requestValue` is the common effect/decoder kernel. `challengeRequest`
and `localRequest` retain distinct public-query and private-service effects.
Private services never append a public challenge. The source `Original` fold
uses the same kernel for scalar/block queries and typed producer receives. Its
delivery resolver reuses `SourceDelivery.checked`, including original def-use
and event order. Active occurrence frames are preserved across queries and
deliveries. Draw has exact specialization equations, including malformed-origin
refusal; it is not a compatibility name for an index interpretation.

The normalizer's generic service branch produces the existing `Form.query`.
`NormalForm.Soundness.query_rule` and `operation_sound` cover it through checked
`serviceAction`. `ServiceConnection` proves request sort/formation laws, bounded
decoded replies, field specialization, public/private routes, and the local
all-reply `Original.Simulation.challenge` rule for the actual constructed query
instruction, `Simulation.localService` for either role's unselected private
capability, and `receiveRequest_of_route` for exact query-before-message delivery. Its continuation premise concerns every decoded value and keeps
the caller's live-frame relation. `ConnectionRouting.ActionCovered` includes
typed scalar/block queries and producer delivery so an omitted route cannot
silently certify source refusal. These additions preserve the existing Oracle
placeholder branches.

`ServiceReading.request`, `challenge`, and `original` instantiate the existing
transcript `Bridge`, including its independent `ReadingTo` and `CoherentTo`
requirements. `source_index` and `source_block` read the actual checked source
service actions; `source_bridge` combines those readings with the independent
request-history coherence proof. Returned history advances by exactly one query event. Existing
handler, computation, query-log, cache and charged-cost laws can consume these
bridges without another FS engine or a new query-tree argument. Complete stops
and unread proof are retained by those existing laws; failure-state controls
also check the actual constructed handler.

`Tests.IndexServicesData` contains tiny fresh source and both constructed
endpoints for scalar, block, private-service and repeated-scalar roots. Regenerate
only this data with `checks/check_index_services.py --compiler PATH --output DIR
--update-data`. Without `--update-data` it checks exact regeneration and strict
malformed-export controls. Its manifest is structural capture evidence, not an
authenticated cryptographic source receipt. `Tests.IndexServices` checks source
admission, construction, association, literal formation, range/count refusal,
request identity, private ownership and loop ancestry. `Tests.IndexServicesExecution`
exercises the actual small endpoints with explicit deterministic service controls.
`Tests.IndexServicesPrivate` checks both roles' private capability handlers and
unread-proof preservation. `TestsSecurity.IndexServices` transports both source
forms through the existing exact experiment, preserves repeated-query logs and
instantiates the actual VCVio memoized-oracle cache-hit law.

`ConnectionServiceRequests.Service` supplies one finite typed request witness for
field, scalar-index and block-index queries. The existing alignment engine consumes
it for public queries, private services and exact query-before-message delivery.
`Tests.IndexServiceCertificates` proves `ConnectionAdmission.Required` for all four
actual tiny roots in both roles, including complete input ABI, live frames, output
layout and route coverage. The repeated roots contain one finite loop-body service
rule, independent of the runtime iteration count. The proposer also accepts tested
instruction/layout changes and refuses altered requests, bounds, counts, ancestry
and roles. The field certificates use the same engine.

Neither this model nor equality of decoded
marginals identifies native raw provider bytes: absorbed provider bytes can
affect later native transcript state and keys even when decoded indices agree.
Source-to-native realization, authenticated source receipts, numerical field
models, FRI protocol properties and full FRI security remain distinct obligations.
