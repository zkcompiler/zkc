# Native index block requests

[IR construction](../ir/construction.md#native-index-blocks) owns the semantics
of these shared request bytes. This is the current version `0` construction,
with one strict schema and no compatibility reader. Catalog presence does not
install a backend or establish a Fiat–Shamir theorem.

## Typed invocation

All three declarations have one static Transcript root argument `T` and require
`IndexBlockTranscript(T)`. The initial explicit installations are
`hash-chain.keccak256.koala-bear.ext8-binomial3.rejection31le/0` and
`hash-chain.keccak256.koala-bear.ext4-binomial3.rejection31le/0`; each also has
`IndexTranscript(T)`. Field sampling or scalar index support does not imply
block support.

| Contract | Inputs | Outputs | Invocation parameters |
|---|---|---|---|
| `transcript.native.indexed.indices` | transcript, coordinates:indices | indices, transcript | origin, N, Q |
| `transcript.native.indexed.indices.search` | transcript, coordinates:indices | indices, witness:index, transcript | origin, N, Q, b |
| `transcript.native.indexed.indices.gated` | transcript, witness:index, coordinates:indices | indices, transcript | origin, N, Q, b |

`NativeIndexBlock` validates the composite parameter list independently in each
native consumer. The first parameter is `origin` with structured query method
`indices`; subsequent parameters are `natural`, with canonical unsigned u64
decimal carrier. N is a power of two in [1,2^63], Q is in [1,2^20], b is in
[0,64]. The declaration requires exactly three or four parameters as above.
N is not an Extent. A reached result contains exactly Q indices in source order,
including duplicates. Configured output, element, memory and work ceilings
remain additional limits. Coordinates are actual outer-to-inner repeat indices,
not output samples.

The ungated operation has Sampling domain `IndexBlock` and History output 1.
The two gated operations only have History, at output 2 for search and output 1
for check. In particular search has no ideal sampling or public replay facet.

## Exact bytes

H is Keccak-256; s is the authenticated 32-byte chain state. Existing hash-chain
frame roles and canonical dynamic `zkc.native-origin/0` occurrence encoding apply.
All labels below are ASCII bytes without an implicit terminator.

```text
frame(tag,label,data) = tag:u8 || len(label):u64be || label
                        || len(data):u64be || data
absorb(s,label,data) = H("zkc.hash-chain.absorb/0\0" || s
                         || frame(1,label,data))
p1 = absorb(s,  "origin", occurrence)
p2 = absorb(p1, "bound", N:u64le)
p3 = absorb(p2, "count", Q:u64le)
witness_wire(w) = "ZKCV" || 0x00 || 0x1f || w:u64le
```

The witness is exactly 14 bytes, using `native.index/0`. Enclosing proof framing
is separate. For b>0:

```text
p4 = absorb(p3, "difficulty", b:u64le)
sw = absorb(p4, "gate-witness", witness_wire(w))
L  = 8 + 8*Q
r  = frame(2, "gated-indices", L:u64be)
Bk = H("zkc.hash-chain.request/0\0" || sw || r || k:u64be)
answer = (B0 || B1 || ...)[0:L]
next = H("zkc.hash-chain.absorb/0\0" || sw || r)
```

The gate passes when the first eight bytes interpreted as u64 little endian
have their low b bits zero. At b=64 check the whole word, without shifting by
64. Index j is `u64le(answer[8+8*j:16+8*j]) & (N-1)`. The eight-byte gate and Q
index windows never overlap. Prefix search uses the final L, even when it only
examines B0. The successor binds the request frame, not its answer bytes.

For b=0 require w=0 before state consumption. Skip difficulty and witness
absorption and the gate window; use p3, label `indices`, L=8*Q, and decode index j
at offset 8*j. The gated proof slot still carries canonical witness zero. These
bytes equal the ungated block equation for the same initial state and occurrence;
different authenticated deployments need not start at equal states.

## Search and reached failures

The prover searches a finite checked interval on an immutable private snapshot,
using the ordinary numerical Call. Its first passing nonce is replayed against
the authenticated live transcript. The verifier does not search. Honest search
limits are deployment resource policy, not proof security parameters. Search
exhaustion publishes nothing and consumes no logical draw. b=0 bypasses search.

Preserve reached ordering: VM operands and shared reservation; handler shape,
size and canonical-zero checks; frame/custody/generation/domain authentication
and debit affordability; complete result and raw request storage reservation;
prover prefix/search; live budget/generation/draw recheck; full authoritative
work precharge; atomic one-draw transition; request hashing; gate; publication.
No search receipt, equal digest or stale token substitutes for the live check.

A gate failure is `rejected:require`: after the atomic transition it retains the
request successor internally, generation+1/draws+1/budget-1, and returns no
values or successor handle. Initially the complete request is computed and
charged even on rejection. Earlier failures retain their original ordered stop
and accepted charges; cleanup does not restore consumed authority.

For digest input length n, charge floor(n/136)+1 permutation lanes. Put
P=floor((79+occurrence_length)/136)+1 and B=ceil((8+8Q)/32). Positive-difficulty
authoritative work is P+B+5 lanes. Search additionally pays P+3 fixed-prefix
lanes and two lanes per physical candidate, including padded lanes. Zero
difficulty costs P+ceil(8Q/32)+3. Search receipt counts do not include caller
prefix/replay and are not semantic security-query counts.

All retained result, nonce, request and freeze overlap share the same numerical
Call. Conservative public result allowance is 8Q+768 bytes, plus 512 for an
exported witness. Admit eight additional private nonce bytes internally without
raising public output ceilings or opening another Call. Accepted work is never
refunded. This does not define a global physical-work ledger.
