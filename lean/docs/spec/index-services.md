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
sites retain source-relative identity; native constructed annotations have their
own separate checks.

`ServiceExecution.serviceAction` checks formation before issuing a source
effect. A source service can stop or return an arbitrary carrier value. A scalar
reply outside the requested range, or a block with the wrong length or an
out-of-range entry, stops with `refused` before entering its continuation. This
adversarial interface imposes no honest distribution assumption.

The source laws in
[`ServiceExecution.lean`](../../ir/Zkc/IR/Source/Structured/ServiceExecution.lean)
prove refusal of invalid inputs/replies and continuation on valid replies. The
field specialization is the unchanged field-query action. These are source
semantics laws; they do not by themselves install a probability distribution,
Fiat–Shamir transcript, native decoder or controller implementation.

The former normalization and constructed-operation connection, their generated
index-service snapshots and concrete security installations are retired. The
[common construction framework](source-construction.md) remains the proof path
for new installations. Actual-source association and complete realization are
open work, including the source-to-native connection for these service kinds.
Native provider limits and byte behavior remain specified by the
[native contracts](../../../docs/spec/contracts.md).
