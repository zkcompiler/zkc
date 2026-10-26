# Selected finite data codecs

`Zkc.DataCodec.Codec` specifies an executable partial codec for one Lean value
type. It supplies a decidable `admitted` predicate, a spelling function `bytes`,
and an executable prefix parser. `encode` returns the spelling exactly on the
admitted domain and returns `none` otherwise. `decode` runs the parser and
accepts only when its unread suffix is empty. `none` is the single rejection
result; this model does not reproduce native error classes.

The two required parser laws quantify arbitrary byte strings and suffixes:

- An admitted value's spelling followed by any suffix parses to that value and
  exactly that suffix.
- Every successful parse yields an admitted value and decomposes its actual
  input into exactly that value's spelling followed by the returned suffix.

These laws prove encoding success on the admitted domain, decode after encode,
encode after every successful decode, fixed-codec injectivity and prefix
separation. Every nonempty suffix after an admitted spelling is refused by the
complete decoder. Canonicality is a theorem over all accepted raw bytes;
malformed inputs are not removed from the parser's domain by an honest-input
premise. There is no choice-based decoder or inverse search.

## Composition and limits

`Codec.pair` concatenates the two spellings in order and parses them in order.
It admits exactly pairs whose components are admitted. `Codec.unit` terminates
the existing `Carriers.ProductValue` interpretation with an empty spelling.

`Codec.sequence` writes an eight-byte little-endian element count followed by
the ordered element spellings. Its exclusive count bound is explicit and must
be at most `2^64`. The parser checks the bound before parsing that many
elements. Recursion is on the count, so zero-byte elements also work. Pair and
sequence composition prove both parser laws once; nested sequences reuse them.
Mathematical lists remain unbounded.

`Codec.boundedNat` uses the existing `Construction.le64` and `ofLe64`, checks
eight available bytes, an exclusive numerical bound and exact re-encoding.
`Codec.fin` packages a checked value in `Fin limit`; it refuses excessive
representatives rather than reducing them modulo the limit. Truncated lengths
and out-of-range words have general refusal theorems, for arbitrary suffixes.
`Codec.equiv` transports a codec along an explicit computable equivalence.

These are mathematical size and recursion bounds. They do not model native
allocation, machine arithmetic, stack limits or charged execution.

## Nominal payloads and the selected batch

`Zkc.DataCodec.PayloadCodec` selects one exact `Structured.Ty` and a codec for
its existing `Carriers.Value`. It wraps values in the dependent
`Construction.Domain.Payload`; it does not define a second recursive value
universe. Encoding first checks exact nominal type equality. Decoding packages
the selected type. Roundtrip, canonical acceptance and trailing-byte refusal
lift to payloads. Different products, constructors, fields, vectors and
sequences cannot be identified by equality of their host carrier types.

`ZkcExamples.Construction.BatchOpeningCodec` selects the data layout of the
construction bridge's `batch-opening.zkc` client:
`Sequence<Opening<koala-bear>>`, with the retained nominal product identity and
constructor, and scalar fields ordered `point`, then `value`. The fixed scalar
interpretation is `ZMod 2130706433`. The product uses the shared nested pair
interpretation, including its Unit terminator. The client exposes the matching
`ringModel Scalar Scalar` for structured helper interpretation; the unused
group carrier is also `Scalar`. Full catalogue capability admission is a
separate obligation. This codec admits at most sixteen
openings. Each scalar uses eight bytes; a record uses sixteen bytes and a
batch uses `8 + 16 * length` bytes, at most 264. An additional nested-sequence
client admits at most four such batches; it is a distinct message shape.

The selected context contains the exact schema, entry, message site, participant
positions, ordered field names, codec version and count limit. The selected
encode/decode functions check exact context equality. The caller must bind
that exact context out of band; no theorem here proves a deployment performs
the binding. A schema digest is not treated as injective. Fixed-schema value
bytes omit repeated type names. Reordered point/value data have different bytes
when the values differ, and reordering field names changes the context.

The selected `receiveBytes` decodes a payload, reads it at the exact batch
type, returns the delivered batch and decides whether every record has the
requested point and value. `delivered` proves this observation for every batch
within the size limit, including batches for which the decision is false.
`accepted_size` proves the complete accepted-byte bound from canonicality.

`BatchOpeningCodecTransport` supplies an interpreted wire interface whose send
and receive events retain the exact context, message site and peer. Its handler
encodes the actual typed sent value and decodes the actual raw reply, refusing
malformed bytes, other nominal types and service requests. `producer_bytes` and
`validator_bytes` prove exact process equations for the selected one-message
action skeletons. The validator equation quantifies every peer byte string;
`received_encoded`, `received_malformed` and `received_trailing` give its
successful and unsuccessful outcomes. This is a mathematical byte handler.

The source/constructed artifact connection must separately establish that the
actual producer sends this exact type with the selected site and peer, the
validator receives it, and the actual checked helper computes `checkBatch`.
That yields the artifact equations against the selected `producer` and
`validator` skeletons, after the appropriate output projection. The codec is not a
compiled-process or native-pipeline theorem and makes no commitment-security
claim. `Tests.DataCodec` exercises the positive layout and refusal boundaries.

## Native boundary

This is the distinct `zkc.interpreted-batch/0` format. It is not the installed
native [message framing](../../../docs/spec/formats/messages.md). In particular,
`crates/zkc-kernels/src/plonky3/mod.rs` encodes a KoalaBear scalar as four
canonical little-endian bytes; native messages add ZKCV framing, use u32
container framing and perform aggregate resource preflight. No correspondence
between that provider/decoder code and this eight-byte scalar codec is proved.
Existing Sumcheck byte meanings and native formats are unchanged.
