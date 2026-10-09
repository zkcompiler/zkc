# Structured native proof messages

This chapter defines complete typed messages and setup authorization for the
single [native proof contract](native-proofs.md). Flat messages, bounded repeats,
PCS and nested data all use the native proof policy, `zkc.native-origin`, `ZKCPRF01` proof
framing and `zkc.native-proof-inputs` invocation records.

## Complete types

`zkc.program` carries these values through the existing protocol, participant,
exec and physical profiles. Proof admission independently checks message,
input, key and control restrictions. Program admission alone grants no proof
deployment authority or transport support in another Host.

The complete logical message grammar is:

- `bool`, `index`, `indices`;
- scalar fields BLS12-381 Fr, BN254 Fr, Ristretto scalar, KoalaBear base and
  KoalaBear ext8; groups BLS12-381 G1, BN254 G1/G2/GT and Ristretto;
- field `vector` and sparse `matrix` in each installed scalar domain;
- `groups` in BLS12-381 G1, BN254 G1/G2 and Ristretto;
- `field_array<bls12-381.fr,N>`, including zero, with `N <= 1048576`;
- commitments and opening proofs of `multilinear.kzg.bls12-381/1`;
- root and path leaves for both installed KoalaBear Merkle row schemes;
- nominal finite variants whose **every alternative** has payloads in this grammar;
- `sequence<T>` with `T` recursively in this grammar. The
  [nested-data profile](nested-data.md) defines its storage and framing.

Only each type's installed default physical representation is admitted.
One-alternative variants are records. Existing variant formation, descriptor
identity, nesting and expansion bounds apply. Peer bytes supply no type
descriptor. A local copy permission, registered leaf codec or inactive payload
does not admit a container outside this grammar. Tables, arbitrary providers,
keys and affine resources cannot be nested as
messages. Existing standalone private table and key input constructors retain
their distinct contracts.

Copy/drop, total mathematics, local execution, protocol ports and wire permission
remain different judgments. Common `data` operations retain their total-payload
contract. Copyable non-total values such as PCS objects can be packaged and
eliminated using existing checked local variant operations. This profile does
not mark their operations pure, speculatable or eligible for mathematical
rewrites. Keys retain local custody even though they are immutable.

The type model permits finite nested records containing dynamic numeric leaves
and runtime-length sequences under the [nested-data contract](nested-data.md).
Sequence formation, elimination, ownership and execution bounds remain explicit;
a record of vectors is not an implicit sequence of records.

## Canonical value frames

All integers below are unsigned little-endian. All frames begin with ASCII
`ZKCV`, byte `1`, and one tag byte. Aggregate frames are:

| Tag | Expected type | Bytes after the header |
|---|---|---|
| 65 | Nominal variant | `alternative:u32`, then each active payload's `frame_length:u32` and complete frame, in declaration order |
| 66 | BLS scalar vector | `count:u32`, then exactly `count` canonical 32-byte scalars |
| 67 | BLS G1 vector | `count:u32`, then exactly `count` canonical compressed 48-byte subgroup points |
| 68 | Indices | `count:u32`, then exactly `count` unsigned 64-bit indices |

The expected descriptor determines alternative bounds and active payload count;
there is no additional payload-count field. Empty variants and collections use
the same framing rules. Every child frame has its own header. Existing scalar,
Boolean, group, index, field-array and PCS leaf frames retain their exact bytes.
Nested child frames and the outer frame must be consumed completely. Noncanonical
Boolean, field and group representations refuse. Canonical infinity is valid.
Additional leaf frames reuse the installed ZKCV encodings exactly:

| Type | Tag | Complete frame bytes |
|---|---:|---:|
| BN254 Fr | 40 | 38 |
| BN254 G1 | 46 | 38 |
| BN254 G2 | 48 | 70 |
| BN254 GT | 50 | 390 |
| KoalaBear base | 19 | 10 |
| KoalaBear ext8 | 26 | 38 |
| Ristretto scalar | 13 | 38 |
| Ristretto group | 16 | 38 |

Wrong width/header, noncanonical scalar and invalid group encoding retain the
`Length`, `Header`, `Scalar` and `Group` decode classes. Each scalar leaf counts
as one element and each group leaf as one group in aggregate accounting.

Bulk leaves have the following canonical layouts. `n` is the count read at byte
offset 6, except sparse matrices, whose nonzero count is at offset 14. Their
rows and columns occupy offsets 6 and 10. Each coordinate/count is `u32`.

| Leaf | Tags by domain | Complete frame bytes | Aggregate charge |
|---|---|---|---|
| Field vector | BLS 66, BN254 41, Ristretto 14, KoalaBear 20, ext8 27 | `10 + n*w`; scalar width `w=4` for KoalaBear, otherwise 32 | `n` elements |
| Source-group vector | BLS 67, BN254 G1 47, G2 49, Ristretto 17 | `10 + n*w`; point widths 48, 32, 64, 32 respectively | `n` groups |
| Sparse matrix | BLS 23, BN254 45, Ristretto 24, KoalaBear 25, ext8 30 | `18 + n*(8+w)`; each entry is row, column, canonical scalar | `n` elements |
| Merkle root | KoalaBear 33, ext8 35 | 38 | one element |
| Merkle path | KoalaBear 34, ext8 36 | `10 + 32*n`, at most 24 siblings | `n` elements |

Matrix entries must be in strictly increasing row/column order, in bounds and
nonzero; decoding never normalizes or merges entries. Merkle framing checks
neither authenticity nor the expected coordinate: `oracle.check` consumes the
actual root, caller-supplied width/height/index, row and path. Merkle leaves
require no KZG setup; their opening state remains local.

Descriptor codec identity is `zkc.native-data` for vectors, group vectors,
matrices, indices and recursive containers. Fixed scalar/group, PCS and Merkle
root/path leaves retain their installed ZKCV codec identities. Matching public ZKCV bytes do not equate descriptor codec identities:
the descriptor separately binds the exact type, representation and consumer.
Types are authenticated by the deployment/descriptor binding, not encoded again
into each value frame. The BLS vector/group native tags remain 66/67.

### Admission and resource bounds

Before payload construction, decoding scans the complete expected-type frame:
outer wire limit, header, active alternative, child bounds, exact leaf widths,
counts and setup metadata. It accumulates resource requirements over the entire
message, not independently per nested collection. Scalar/index elements and
fixed field-array elements count against the element ceiling; G1/G2/GT and Ristretto payload
points count against the group ceiling. The existing hard collection ceilings
still apply. Booleans do not consume the numeric element count.

The retained estimate includes descriptors, variant wrappers, payload slots and
leaf storage. Both encoding and decoding apply the same conservative peak bound
covering construction, two temporary PCS encoding buffers and later transcript re-encoding: if `R` is the retained
estimate and `W` the frame size, require `max(2R, R + 3W)` within the configured
value-byte budget. Type formation does not promise that every value fits the
default runtime budgets. Structured numeric counts conservatively use scalar
width even for indices. Aggregate ceilings apply to the complete new frame;
standalone leaf frames retain their existing limits. Checked arithmetic and fallible reservations preserve limit
outcomes. The native implementation additionally verifies actual retained size.
These are deterministic resource ceilings, not an exact allocator measurement.

An excessive declared collection count is a limit outcome even if its body is
truncated. A fixed leaf's incorrect width/header is a decode outcome before its
conservative allocation estimate. Canonical leaf validation follows structural
and aggregate preflight. Malformed data, resource limits and missing/incompatible
backend setup remain distinct error classes; no global precedence is promised
when several independently invalid conditions coexist.

### Application-authorized setups

If any selected entry or message type contains PCS data, including an inactive
alternative or empty sequence, the deployment requires at least one public
verifier-key input. Up to 64 such ports are admitted. Every key port, including
unused and terminal-only inputs, must be independently authorized by the host.

`NativeDeployment::admit` accepts application configuration with two
maps, indexed by original common-program input ports:

- `keys`: every public verifier-key port to its expected key ID;
- `inputs`: every other setup-bearing data input to a key port. This includes
  unused prover keys and aggregates containing commitments or proofs.

Coverage is exact; missing/extra ports, repeated serialized ports and references
to unknown key ports refuse with `native-proof-key-authority`. A configured
aggregate input uses one selected key recursively for all active PCS leaves.
Received aggregates may contain leaves from different authorized setups.
Path-specific authority within a host input is outside this profile.

The CLI selects this configuration with `--setups=PATH`. The bounded format is:

```text
["zkc.native-setup-authority",
 [["vk_port", "expected_key_id_hex"], ...],
 [["input_port", "vk_port"], ...]]
```

Ports are canonical decimal strings. The file is bounded to 64 KiB; key IDs are
32 bytes encoded as lowercase hex. A single key uses the same maps. Invocation
input records and prover-key file constructors retain their existing formats. Invocation data and
proof headers cannot supply this authority.

Before PCS decoding or entropy issuance, the host imports every public key under
its configured ID. Only byte-identical keys are deduplicated in the bounded
registry. Each direct key/PCS entry operand also carries the backend's port setup
constraint. Aggregate input leaves are checked recursively against their selected
key. Wrong input metadata refuses with `native-proof-input-setup`. Loading a
prover key checks the complete material fingerprint and selected verifier key.

For multiple authorized keys, decoding first bounds the fixed PCS header, uses
its key ID to locate already authorized material, and then checks exact width,
kind, arity, setup ID, key ID, subgroup and canonical encoding. The header can
select a registry member but cannot add one. A singleton checks length before
its header. An unknown key is an invalid header; incompatible
producer metadata reports `native-wire-setup-mismatch`. A received value under a
different authorized key may decode, but an actual `pcs.check` with the wrong
key operand stops with a backend key mismatch when shapes agree; an arity
check can refuse earlier when they differ. Neither returns a valid proof decision.
`pcs.equal` compares canonical values including setup identity, so values under
different setups compare false. Actual source operands remain authoritative.

The invocation root already binds each public key's complete canonical bytes at
its original port. The setup-authority maps govern host input acceptance; they
do not add root fields. These maps do not pin receives to a source site or bind
outputs to a setup slot.
A returned commitment or proof that has not passed an explicit key-consuming
check may belong to any authorized setup. Applications needing a specific output
setup must enforce that condition in their protocol; the Host supplies no output
setup-slot contract. Wrong input bindings and wrong terminal key/arity remain
distinct refusal boundaries.

## Transcript observation

Derived native proof construction uses one construction-only contract:

```text
transcript.native.indexed.observe.data<Suite, CompleteLogicalType>
  (transcript, payload, indices) -> transcript
```

Its static arguments are the suite and canonical complete logical type. The
installed implementation requires an installed native challenge suite, the closed
message grammar and exact default physical representations. The suites are the
existing BLS Merlin/Spongefish suites, Ristretto Merlin
`merlin3.ristretto255.scalar64le/1` and KoalaBear ext8 Merlin
`merlin3.koala-bear.ext8-binomial3.rejection31le/1`. The selected random-service
contract and draw result must match the suite's challenge field.

Complete-type observation absorbs bytes, so its payload domain need not equal
the challenge field. For example, a BN254 group frame can be observed under the
KoalaBear ext8 suite. Type identity, origin and exact canonical framing remain
bound. This does not install a BN254 challenge suite, change a sampler or claim
security for an arbitrary protocol using mixed domains. The semantic facets identify
the observation payload and affine history successor. The dedicated MLIR op is
`crypto.exec.indexed_transcript_observe_data`; physical selection uses the
existing bound-kernel path. This adds no source generic wildcard or runner action.

After an actual receive and successful canonical decoding, the observer absorbs
the full frame, including tags and lengths, under the existing origin/value
labels. It never flattens record leaves. Canonical-only decoding permits exact
re-encoding; formats that observe arbitrary original bytes require a separate
adapter preserving those bytes. Authored execution with an empty suite inserts
no observation or challenge.

Admission matches every declared message origin and complete payload type to
the actual observer helper, including reverse challenge delivery absent from
proof bytes. A shared contract name or matching event count is insufficient.
Forward proof messages also match their actual send/receive type and ordering.
The source checker separately checks construction correspondence.

## Scope

Separate participants execute through the general interpreter and existing
cryptographic kernels. A well-formed message does not establish the authored
relation. Ordered guards and terminal checks remain protocol obligations;
relation declarations, public configuration, application context and key
authorization keep their existing binding meanings. This profile establishes
neither native Lean correspondence nor cryptographic composition or external
proof-format compatibility.
