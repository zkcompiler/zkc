# Independent role backend adapters

`zkc-backends` connects the generic `zkc-runtime::interactive::Backend` to
the installed Arkworks, Dalek and Plonky3 providers through explicit nominal
bindings. Runtime source contracts and backend signatures are checked independently.
Each invocation is one mathematical operation; the crate does not implement a
prover/verifier protocol callback or own compiler/source correspondence.

## Implementation layout

`backend/` separates explicit host policy, common validation and native dispatch.
`bindings/` owns independently installed signatures; `domains.rs` owns nominal
associations. `kernels/` contains scalar/vector/curve and resource operations,
with Plonky3 helpers in `plonky3/`. `codec/` holds wire and host-input encoding
and decoding; `value.rs` retains the concrete carrier enum. `resource.rs`,
`setups.rs` and `transcript.rs` retain authority and state ownership.

The crate root keeps its public types and constructors. Every successful
operation returns through the common output validator after dispatch, including
external operations and resource units. `external/` and `external_kernels.rs`
retain the pinned construction adapters and persistent external-work budget.

## Plonky3 numerical domain

Explicit bindings also install `koala-bear` (prime 2130706433) through
`plonky3/<contract>`. Direct dependencies `p3-field` and `p3-koala-bear` are
pinned to `=0.5.1`; the lockfile fixes the complete Plonky3 dependency family to
0.5.1. Release provenance is upstream commit
`45e0ffe4d294816755522dd2cf7c38d6bcd701ce`, as recorded in the published crate's
`.cargo_vcs_info.json`.

| Kind | Physical representation | Codec | Wire tag |
|---|---|---|---|
| field | `plonky3.koala-bear/1` | `zkcv.field.koala-bear/1` | 19 |
| vector | `plonky3.koala-bear-vector/1` | `zkcv.vector.koala-bear/1` | 20 |
| polynomial | `plonky3.koala-bear-polynomial/1` | `zkcv.polynomial.koala-bear/1` | 21 |
| round | `plonky3.koala-bear-quadratic/1` | `zkcv.round.koala-bear/1` | 22 |
| matrix | `plonky3.koala-bear-sparse-coo/1` | `zkcv.matrix.koala-bear/1` | 25 |

Canonical bytes start with `ZKCV`, byte 1, and the tag. A field is one canonical
u32 little-endian coefficient, strictly below the prime. A round has exactly
three coefficients. Vectors and polynomials prefix their coefficients with a
u32 little-endian count. Polynomials use ascending coefficients with no trailing
zero; the zero polynomial is empty. Montgomery storage never appears on wire.
Lengths, count ceilings, and retained-output budgets are checked before allocation.
KoalaBear vectors charge four bytes per element plus the existing 256-byte
payload allowance; scalar and round values retain the existing 512-byte charge.

`Value::{KoalaBearField,KoalaBearVector,KoalaBearPolynomial,KoalaBearRound}` carry
the upstream `KoalaBear` type. `Value::koala_bear_vector` is a bounded host
constructor. Existing `field`, `vector`, `polynomial`, `round`, `wire`, and `host`
input tags select this domain from the admitted port type. Decimal and wire
input reject noncanonical representatives instead of reducing them.

The backend reuses the generic field/vector/univariate-polynomial kernels and
the quadratic round evaluator. An affine fold is composed as
`split`, `sub`, `scale`, `add`, giving `lo + r * (hi - lo)`. Product/dot accept
empty vectors, with dot returning zero; split refuses empty and odd lengths.
Inverse of zero returns `refused:zero-inverse`. This domain has no installed
table, RNG, nonce, transcript, group, or PCS operation and is not a BLS PCS
substitution or a small-field cryptographic security claim.

Use `NativeBackend::new(policy, entry, None)` with `entry.arity = None`
for numeric work without setup, or `with_setups` with an empty registry.
Shared bool/control bindings keep their existing names. Domain associations
are optional; installing this field requires no group or transcript identity.

For matched kernel measurements, `plonky3::{dot,mul_into}` are the exact
allocation-free arithmetic routines used by the Runtime dot and product kernels.
`PACKING_WIDTH` reports the upstream compile-time packing width, which can be
one in a portable build. These routines use `Field::Packing` and its safe packed
slice APIs, including scalar suffixes; they make no timing or speedup claim.
`plonky3::{encode_scalar,decode_scalar,parse_decimal}` expose the scalar codec.

## Octic extension

`KoalaBearExt8` is the pinned Plonky3 0.5.1
`BinomialExtensionField<KoalaBear, 8>` for `X^8-3`. Its nominal identity is
`koala-bear.ext8-binomial3`. Field, vector, polynomial, round and sparse matrix
carriers reuse the shared arithmetic kernels. `field.embed` explicitly converts
from KoalaBear; mixed operands refuse. Natural constants are embedded canonical
base representatives below `p`, never integers modulo `p^8`.

`plonky3::{encode_extension,decode_extension}` encode exactly eight ascending
canonical u32 LE coordinates. The native ZKCV tags are 26–30, specified in
[artifact format](../../docs/compiler/artifact-format.md#octic-koalabear-extension).
`Value::koala_bear_ext8_vector` and `Value::koala_bear_ext8_matrix` are bounded
host constructors; non-base CLI inputs use `wire` or `host`. Vector/polynomial
backing charges 32 bytes per element and sparse matrix backing 40 bytes per
entry, each plus 256 bytes. Scalar and round charges remain 512 bytes.
There is no associated RNG, transcript, group, oracle, FRI or PCS service.

## Host API

Immutable sparse matrices support products, transpose products, bilinear
evaluation and shape checks in all four installed scalar fields. They retain
one shared allocation across value clones. Logical `matrix:F` remains separate
from the first COO physical representation; exact dimensions are checked and
no implicit padding or truncation occurs. Canonical matrix inputs use
`["matrix", ["rows", "columns", [["row", "column", "coefficient"], ...]]]`.
Coordinates must be ordered and unique and coefficients nonzero. The
[artifact format](../../docs/compiler/artifact-format.md#explicit-vector-and-ristretto-domains)
owns the wire tags, bounds and representation names. A public matrix uses the
same canonical public-root binding as other public values; its availability
does not install a matrix commitment or a complete circuit prover.

- `NativeBackend::new(Policy, EntryPolicy, Option<VerifierKey>)` selects explicit
  bounds, entry bindings, public input policy and the receiving PCS key.
- `Value` is a typed enum: nominal fields/groups, bool, round, immutable Arc-backed
  table/point/key/commitment/proof/opening state, and opaque RNG/nonce tokens.
  Ark helper keys, tables and proofs retain their own immutable backing as well. No public
  commitment or proof variant retains a private table.
- `issue_rng(Domain, budget)` / `NativeBackend::issue_nonce(Domain, budget)`
  are host issuance. Domain binds owner, session, entry and an optional exact
  instance. An instance-restricted token cannot move into a differently named
  child; use an explicitly instance-unrestricted token if that is intended.
- `InputBindings::insert(name, value)` registers already issued handles, keys or
  private opening states for one role. `inputs_from_json(&EntryRole, bytes, &bindings)` returns values
  in admitted input-port order. It is read-only. `Runner::new` performs atomic
  actual alias, domain, shape and public-input admission again.
- `encode_value(value)` and `decode_typed_value(expected_physical_type, bytes)` carry public
  values only. The receiving Ark backend invokes its configured verifier key's
  exact bounded decoder for every commitment and proof. A decoder without that
  key refuses PCS bytes. Key fingerprints must come from authenticated host
  configuration, never from the same incoming bytes being authenticated.
- `observe(&Capability)` returns issued ID, current generation, logical draw
  debit, remaining budget and public stage. An old authentic handle can observe
  its own current counters, but cannot access secrets or obtain a new handle.

The runnable `cargo run -p zkc-backends --example role_inputs` demonstrates actual
JSON + issued capability + development key setup + supplied-participant execution.
It uses OS-seeded randomness with the default features. Full wire-input CLI,
packet transport, source correspondence and root workspace wiring remain with
the consuming application.

Example input (exact arrays; fields are canonical decimal strings):

```json
["zkc.inputs/1", [
  ["pk", ["host", "prover-key"]],
  ["table", ["table", ["2", "3", "5", "7"]]],
  ["claim", ["field", "279"]],
  ["rng", ["host", "challenge-source"]]
]]
```

Other value forms are `["point", [decimal, ...]]`, `["round", [a,b,c]]`,
`["bool", true]`, `["scalar", decimal]`, `["group", decimal]`, and
`["wire", lowerCaseHex]`. The expected admitted port selects the wire type.
There are no JSON key/opening-state imports, issuance requests, token IDs or
generations.
A private opening-state input uses `["host", "selected-original"]`, where the
host previously inserted `Value::OpeningState(Arc::new(committed_table))` from
`ProverKey::commit`. Neither `["opening_state", ...]` nor wire bytes can construct
one. A public commitment carries no private state or route to recover one.
Unknown/missing/duplicate ports, numeric fields, noncanonical decimals, malformed
arrays, unexpected types and unavailable host handles are refused. Input text
is bounded by min(1 MiB, max_wire_bytes); serde's default recursive depth limit
is enabled. Hosts must give each role only its authorized registry.

## Original custody and entry policy

`pcs.commit(pk, table) -> (commitment, opening_state)` calls the helper's
`ProverKey::commit` and returns a public commitment clone followed by
`Value::OpeningState(Arc<zkc_arkworks::CommittedTable>)`. The state retains its
immutable original table, key and commitment. `pcs.open(opening_state, point)
-> (field, proof)` calls that state's `open(point)` directly. No replacement
table, commitment or key can redirect a selected state's opening.

The state is an explicit, non-affine private value. Local functions and children
receive it through ordinary declared operands; immutable borrows and repeated
queries are allowed. An unpassed state is absent from the child's environment.
There is no backend map of originals, table-pointer identity lookup or state ID.
A host can explicitly pass an actual helper-issued state to another backend;
its configured verifier identity and entry policy still apply.

Original factors remain independently available as tables for Sumcheck; folding
allocates scratch without changing a previously committed state. Equal-content
tables may be committed separately. This implementation issues a fresh state for
each commit, even for the same table handle; caching is not logical equality.
A table or folded scratch cannot occupy an `opening_state` operand. Scratch may
be committed explicitly with an appropriate key to issue a different state.
No typed wrapper alone establishes cryptographic soundness or formal refinement.

The verifier backend needs only a selected verifier key and public received
commitment/point/value/proof. `pcs.check` returns false for a validly encoded false
claim; identity, shape and codec errors return refusal. `control.require(false)`
stops immediately with `rejected:require`, so no local suffix executes.

`EntryPolicy.arity` optionally pins one homogeneous entry shape for tables,
PCS keys, commitments, proofs and opening states. With no shape pin, each value
obeys its own bounded representation and each kernel checks its operands' shapes.
Opening-state rank/setup/key checks use `state.commitment().metadata()`.
Every supplied key/PCS object must
match one setup/key identity; PK/VK mismatch is refused even without a configured
receiving key. `with_parameters` optionally pins named public parameters chosen
by the host. No parameter name, including `n`, has implicit backend semantics.
Scratch in local/call/loop frames may have smaller arity; each kernel enforces its
own exact shape. Logical rank-zero tables/evaluation are supported; Ark PCS keys
require positive rank.

`PublicInputs::Exact` pins selected named public input values by full canonical
encoding. `LocalOnly` explicitly checks only local admission. The host chooses
which ports carry a shared public statement and supplies equal authenticated
pins to the roles. No callback infers a claim from a private table, learns the
other role's inputs, or treats equal parameter names as public-value agreement.
Private keys, opening states and capabilities cannot be public pins. Host
configuration and the source correspondence checker remain separate trust boundaries.

## Resources and failed state

A token contains private backend authority and per-slot issuance authority,
with a current generation. Numeric IDs are observations, not authority. Token
cloning duplicates only this handle. Tokens cannot be serialized or minted by
safe external Rust code. A backend has no Clone/reset/reseed API.

An entry rejects actual aliases, including two names containing the same token.
Every child view is restricted to its actual passed slots from the immediate
parent's allowed view; an unpassed ancestor slot stays inaccessible. A kernel
requires an explicit authentic operand, the current generation and domain, and
the active frame's permission. Calling with an ancestor frame while a child is
active fails. Slots merely existing in the backend store do not grant access.

A scalar `random.draw` advances generation and draw count before budget,
tape or backend output-limit failure in explicit bindings.
Its remaining budget decreases only if positive. Other scalar resource
transitions retain their existing operation-specific preflights and stages.

`random.vector(n)` validates the active frame, authentic live handle and domain,
reserves output storage, and checks the full draw budget before consuming.
It advances generation once, adds `n` draws and debits `n` budget atomically.
Length zero succeeds at zero budget and invalidates the old handle without
sampling. Insufficient total budget leaves all counters unchanged. Later tape
exhaustion keeps the full transition and any consumed tape prefix.

Failed authentication or view admission consumes nothing. No
failure rolls back completed state or refreshes an old handle. Every frame exit
removes that frame even if output validation fails; cancellation also unwinds
views. Unpassed slots are unchanged on successful or failed child execution.
Counters never wrap and no maximal-generation successor is returned.

The installed BLS vector and Ristretto group diagonal views are immutable,
depth-one values. Admission requires a local producer and at least one use;
every use must be the matching contraction's values operand in that same
function. Views cannot enter or leave functions or participants, be encoded,
or serve as contraction weights. Their full factor and backing storage remains
charged after each use. A diagonal value charges `768 + 64*n` bytes for BLS
or `768 + (32 + size_of::<RistrettoPoint>())*n` for Ristretto. This exceeds
the dense result's charge; optional compiler selection stays off by default.

Production RNG resources each have their own actual OS-seeded upstream
`RandomSource`; fresh IDs alone do not create random independence. Cryptographic
unpredictability/independence still assumes the OS entropy and upstream CSPRNG.
Under `test-utils` only, `issue_test_rng`, `issue_test_tape` and
`issue_test_nonce` are explicit deterministic fixtures. Never enable this feature
in the production consumer. The fixture seed/tape is not part of the wire format.

Native nonces have issued -> committed -> spent stages. `curve.commit` consumes
one issued nonce and computes all scaled bases atomically; `curve.response`
consumes its successor and returns the response field element. The curve kernels
use upstream Arkworks/Dalek groups. Stage logic is separate from RNG draws and
never permits an RNG token to act as a nonce.

## Bounds, loss and errors

Default policy: rank 16, 65536 table cells, 16 MiB wire values, 64 MiB retained
value/combined output, 1048576 setup cells, 4096 capability slots, and 64 nested
resource frames. `Policy` exposes all but the fixed frame ceiling; `ark_bounds()` passes the selected bounds to
Ark. The runtime adds its own execution fuel and cumulative retained-value caps.
The codec checks full expected size before encoding and bounds/exact lengths
before decoding/allocating vectors. Keys are counted conservatively at
`256 + 640*2^n` bytes, tables at `256+32*storage_capacity`, proofs at
`256+192*n`. Each opening state counts the full original table allocation
(including spare vector capacity), full key backing and 512 bytes for its
commitment/wrapper. The separately returned public commitment adds another 512
bytes. Shared key/table backing and wrapper allowances may therefore be charged
multiple times; these are harmless conservative upper bounds. Both commit
outputs are checked against output limits before calling the helper.

Opening states are retained by runtime values, not a backend store. There is no
`custody_count`, `custody_bytes`, `max_commitments` or `max_custody_bytes` API.
Per-value/combined-output limits and runtime live/cumulative retention and fuel
bound this work; no implicit permanent commitment-count policy is imposed.
No key setup occurs in a kernel. Ark's setup-cell bound is a work measure, not a peak-memory reservation;
PCS temporary scratch is not charged to the runtime output-byte counter. Heap
allocator aborts are not converted into recoverable allocation errors everywhere
in Rust/upstream Ark; explicit policy ceilings are not OS memory reservations.

`SCALAR_MODULUS_DECIMAL` exposes exact challenge cardinality p. Canonical ingress
never reduces modulo p. The upstream scalar sampler uses rejection sampling.
For an independent uniform challenge and a fixed nonzero degree-d polynomial,
the root bound is min(1,d/p). The two-factor quadratic round contribution is
conditionally at most 2/p, or 2n/p across n valid rounds by a union bound. This is
not the whole protocol's loss: adaptive opening/PCS assumptions, setup honesty,
transcript binding and independent challenge premises are not proved here. No
numerical PCS security estimate is invented. Ark MultilinearPC is **nonhiding**;
its development setup is not a ceremony. Verifier-key byte identity does not
prove honest setup generation. Persistent proving and verification key codecs are supplied by the
[Arkworks adapter](../zkc-arkworks/README.md). Importing key material does not
establish its setup provenance.

`classify_error(&BackendError)` returns `Rejected`, `Refused` or `Exhausted`.
Only exact `rejected:require` is rejection; `exhausted:*` identifies execution
budgets, allocation/size limits and unavailable entropy. `refused:*` covers
malformed values, keys, shapes, authority, aliases, stale tokens and
view violations. Unknown codes classify as Refused. The runtime currently stores
these as `StopKind::Backend`; the main driver must map them to its public Stop
classification. Encoding/packet errors are refused before receive advancement.
No error is silently sent to the peer or converted into a successful check.

## Validation and integration scope

Tests cover every advertised kernel, independent public-byte verification,
wrong-key/arity/truncated/trailing/noncanonical/oversized codecs, original versus
scratch substitution at type admission, separate equal-content states, repeated
openings and child operands, original/key/capacity retention, entry shape/key/
parameter/public-value mismatches, token forgery/aliases/stale generations/cross-backend/domain/view controls, nested calls
and loops, cancellation and failed cleanup, successful/failed multi-resource
frames, output/budget/tape failure after consumption, deterministic fixtures and
OS sampling, and real curve valid/invalid responses and nonce stages.

This suite uses supplied-participant admission; it does not certify source-to-
participant extraction or physical lowering. Adoption needs the MLIR and source
checker, actual transport, envelope and session checks, an independent reference
comparison and protocol acceptance evidence.

## Native providers and explicit types

`NativeBackend` has one binding dispatch path. `domains::INSTALLED` and
`domains::TRANSCRIPTS` describe current mathematical associations, storage and
upstream providers; they do not select source profiles. Private `bindings::catalogue` and
`bindings::vectors` tables support independently installed binding signatures.
The removed `Profile`, reference backend, additive-Fr group representation,
`Type::Scalar`, and profile-derived type/codec constructors have no replacement
compatibility mode. Boolean/control bindings keep their current `arkworks/`
implementation names and take no nominal arguments.

`NativeBackend::new(policy, entry, verifier)` is a direct host utility: key
operands are trusted host inputs, entry keys must agree, and an optional verifier
pins PCS bytes and values. `with_setups(policy, entry, registry)` additionally
requires prior authorization of every setup, including distinct per-port and
per-receive selections used by `/2` hosts. These are setup trust policies within
the same native backend, not source interpretation alternatives. `Setups::InputKeys`
is the internal name for the first policy; no participant format chooses it.
BLS issuance conveniences (`issue_rng`, `issue_nonce`, `issue_transcript`) have
fixed documented domains. Their `_for` counterparts select explicit current
field/transcript identities. Both feed the same capability store and state checks.

`Value::Curve(GroupPoint)` is a validated subgroup point.
`Value::groups(&points, &policy)` constructs bounded public G1 vectors. The new `Policy::max_groups` defaults to
4096, with an absolute 32768 element ceiling. Retained vectors are charged at
128 bytes per element plus 256 bytes. Existing per-value/output/wire limits also
apply. Group identity, zero scalars, empty bases and repeated bases are allowed.
A protocol needing nontrivial statements must check them explicitly.

The physical `arkworks/curve.*` kernels implement generator, add, scale, equal,
empty, append, at, get, length, commit and response. `curve.get` takes an exact
nominal group sequence and a u64 `index`; `curve.length` returns its actual
length as an `index`. Both are installed for BLS12-381 and Ristretto and take
no attributes. Out-of-range access refuses `group-index`, including `u64::MAX`;
the existing curve output preflight and retained-value charges apply.
`bool.not` and strict `bool.or` share `bool.and`'s domain-independent Boolean
binding and output charging. Neither skips evaluation or selects a resource.
`curve.at` accepts one canonical unsigned
u64 decimal index and refuses out-of-range positions. `curve.commit` consumes an
issued private nonce once, returns all k-scaled bases and its ready successor.
`curve.response(x,c,nonce)` consumes ready state and returns `k+c*x`; the nonce
is then spent. A wrong-stage attempt consumes and spends its authenticated input.
Stage observations keep the historical strings `issued`, `committed`, `spent`.
OS-seeded issuance is `NativeBackend::issue_nonce`; deterministic nonce issuance is
available only with `test-utils`. No nonce scalar export or full proof-verifier
callback exists. `pcs.equal` compares complete canonical public commitments,
including scheme/key metadata; pinned key mismatches remain errors.

Public G1 uses ordinary `ZKCV\x01`, tag 9, then 48 canonical compressed subgroup
bytes. The historical 32-byte additive-Fr payload under tag 9 is rejected;
there is no conversion from an exposed scalar into a curve point.
Public `groups` uses tag 10 followed by u32 LE count and exactly count*48 bytes.
Counts, complete sizes and policy ceilings are checked before vector allocation;
individual points use validating compressed decoding and canonical re-encoding.
Ingress never cofactor-clears points or reduces received scalar encodings.

`issue_transcript(domain, budget, canonical_root_bytes)` issues a nonserializable,
affine `Value::Transcript` with nominal `merlin3.bls12-381.fr64be/1` identity. Each slot holds its own
Merlin 3.0.0 state. It reuses resource seals, authority, generation, owner/domain,
actual frame views, alias checks and consume-before-failure accounting. Original
RNG slots remain separate. Slot issuance does not check source/construction
correspondence: the host supplies the canonical authorized root from the shared
construction contract. Local custody session is not transcript identity.

`arkworks/transcript.observe.TYPE` consumes transcript + ordinary canonical
public TYPE, returning its successor. Attributes are exactly
`[sourceProtocol, messageSite, schema, sourceSender, sourceReceiver]`.
`arkworks/transcript.challenge` consumes transcript, returning field + successor;
attributes are `[sourceProtocol, sourceLocalCallSite, sourceFunction,
sourceOperationSite, sourceRole]`. Source identifiers are explicit; generated
function/kernel names never supply them. Role attributes retain original formal
source role names, including when actual role mapping is nonidentity; actual
roles govern custody only. Calls and loops must pass the transcript
explicitly. Compiler/host construction admission must ensure runtime
`Origin.entry`, `.instance`, and `.path` retain original logical identities.

Initialization: Merlin `new(b"zkc.artifact/1")`, then append `b"binding"` with the
exact canonical root bytes. Observe appends `b"origin"` with canonical logical
origin bytes then `b"value"` with the **full ordinary public wire encoding**.
Challenge appends its origin then requests 64 bytes under `b"challenge"`, reducing
big endian modulo Fr. Zero is allowed; this is not an exactly uniform sampler.
Challenge delivery, when present in the source, is a separate observe operation.
Shape, attribute, codec and output ceilings are preflighted before consumption.
Budget exhaustion and failures after consumption retain advanced generations;
there is no reset, clone-state, rollback or hidden global transcript API.

The logical binary codec and origin helpers are public in
`zkc_runtime::logical`. Codec validity is separate from original-source
construction correspondence. These bounded functional tests do not prove a
Fiat-Shamir/security theorem or formally verify the backend. Arkworks arithmetic
and memory handling are not claimed to be side-channel hardened or to provide
complete secret zeroization. The artifact driver owns the public statement,
key and configuration authorization, proof framing and final acceptance.


The explicit BLS12-381 Fr installation also supports
`spongefish0.7.4.keccak.bls12-381.fr64be/1` through `issue_transcript_for` and
`spongefish/transcript.*` bindings. `domains::TRANSCRIPTS` records suite/provider/
challenge-domain facts separately from `domains::INSTALLED` arithmetic facts.
`Identity::transcript()` recognizes a selected suite; fields no longer select
one implicit transcript. The existing convenience `issue_transcript` retains
its documented Merlin behavior. Each issued state has the same fresh affine
custody and failure accounting. See the [construction contract](../../docs/compiler/artifact-format.md#second-construction-over-bls12-381-fr).

## Explicit public-operand MSM

The opt-in dense `dalek-vartime/curve.msm` has the same Ristretto mathematical
signature as `dalek/curve.msm` and additionally requires public scalars and
points. All constructors authorize no roles. A host may attach a bounded
`PublicRolePolicy` through `with_public_role_policy`; this is caller trust,
not automatic authorization of `V`. The backend checks each actual active role
before executing the variable-time kernel. Default MSM selection is unchanged.
The [implementation contract](../../docs/runtime/public-msm.md) states
the conditional law, resource/observation boundaries and artifact-derived grant.

## BN254 primitive domain

Arkworks `=0.6.0` installs `bn254.fr`, `bn254.g1`, and `bn254.g2`.
The scalar modulus is
`21888242871839275222246405745257275088548364400416034343698204186575808495617`.
Existing field, vector, sparse matrix, polynomial and curve operation shapes use
`arkworks/<contract>`. Each group has its own nominal identity and the common
scalar field. `pairing.check` has static argument `bn254.fr`, implementation
`arkworks/pairing.check`, inputs `groups:bn254.g1`, `groups:bn254.g2`, and a Boolean
output. Unequal vector lengths are refused; the empty pairing product is one.
`curve.neg` supplies negative pairing terms. No Groth16 operation is installed.

| Kind | Representation | ZKCV tag | Element wire width |
|---|---|---|---|
| field | `arkworks.bn254-fr/1` | 40 | 32 |
| vector | `arkworks.bn254-fr-vector/1` | 41 | 32 |
| polynomial | `arkworks.bn254-fr-polynomial/1` | 42 | 32 |
| round | `arkworks.bn254-fr-round/1` | 43 | 32 |
| matrix | `arkworks.bn254-fr-sparse-coo/1` | 45 | 40 per entry |
| G1 | `arkworks.bn254-g1/1` | 46 | 32 |
| G1 vector | `arkworks.bn254-g1-vector/1` | 47 | 32 |
| G2 | `arkworks.bn254-g2/1` | 48 | 64 |
| G2 vector | `arkworks.bn254-g2-vector/1` | 49 | 64 |

Codec names are `zkcv.<kind>.bn254.fr/1` for scalar containers and
`zkcv.<group-or-groups>.bn254.<g1-or-g2>/1` for points. Scalars are canonical
little-endian integers; points use compressed arkworks encodings. Decoding checks
curve membership, subgroup membership, exact length, and canonical re-encoding,
including infinity. Sequence counts, sparse COO ordering, polynomial normalization
and ZKCV envelopes follow the existing formats. Actual Rust point sizes determine
retained charges. Group/MSM/pairing and FFT scratch allocations are conservatively
bounded before entering upstream kernels. These variable-time library operations
do not establish a whole-runtime timing guarantee.

Coset operations use natural order `shift * omega^i`, the arkworks generator-5
root convention, and nonzero shifts. The field's two-adicity is 28; the existing
backend element/memory ceilings impose smaller operational limits. Interpolation
normalizes coefficient vectors; it does not assert a degree bound.

`rng:bn254.fr@host.resource/1` supports `random.draw` and `random.vector` with
OS-seeded CSPRNG state and arkworks rejection sampling. The resource mechanism
continues to enforce generation, domain and budget custody. Deterministic
`issue_test_bn254_tape` exists only with `test-utils`. There is no BN254 transcript,
nonce, PCS, multilinear table or diagonal representation.

### Host resource retirement

`NativeBackend::retire(&Capability)` revokes one issued slot outside every active
frame and returns its authoritative public counters. An authentic old generation
may retire its slot after failed consumption; it gains no renewed consume right.
Retirement frees live-slot capacity, never reuses issued IDs, and leaves unrelated
resources intact. Active frames refuse it with `refused:retire-during-frame`;
foreign, forged and retired handles retain the usual authority/seal/unissued
refusals. Controllers retain current persistent RNG handles across attempts and
retire only resources whose lifetime has ended. Recreating a backend is not a
state-preserving retry policy.

## External construction and representation adapters

`external` implements the pinned Monero hash-chain and OpenVM overwrite-duplex
transitions. Their authored `external.*` operations run through NativeBackend;
[the contract](../../docs/spec/realization/external-constructions.md) defines
state envelopes, exact call grouping, provider selection and ordered refusal. [Adapter documentation](src/external/README.md)
records source pins, licenses and replay commands. The independent internal
Merlin/Spongefish construction remains unchanged.

`representations` separates exact received Edwards bytes, decoded representatives
and checked prime-subgroup images. Only the latter admits scalar-module
rewrites. Its ordered evaluation domains retain axis labels; folds, permutations,
rotations and embeddings validate their source/target meaning. These are native
adapter APIs, not an installed Edwards PIR arithmetic suite or an optimization
pass. Compiler law-admission objects live in `Protocol/Representations.h` and
conditional mathematical laws in `Zkc.Algebra.Representations`.

`choices::Sampler` owns a provider and role/purpose namespaces across attempts.
The Monero nonzero-scalar policy rejects raw integers at least `15*l`, reduces,
then rejects zero. Logical requests, actual provider calls, completed raw draws
and accepted scalars are counted separately, with per-namespace logical/raw
limits. `OsSource` uses OS entropy; deterministic providers must be supplied
explicitly. The host retains this sampler across retries. Installing an authored
BP+ coin operation and complete native prover remains separate work.

`external::grinding::Search` keeps candidate-provider state and role/purpose
identity across bounded prefixes. Candidate and primitive-work limits are separate
from protocol-attempt limits and the live backend's external-work ceiling.
Search trials leave the live seed unchanged; successful selection still requires
one explicit live witness check. Zero difficulty performs no search. Search
limits and provider errors retain usage and stop permanently.

Native external kernels precharge `Work::units()` against a backend-wide default
ceiling of 16777216. `with_external_work_limit` selects a deployment ceiling;
`external_work_spent` reports actual consumed units. Each hash call, hashed byte,
permutation, observation and sample costs one unit. This is neither wall-clock
cost nor a security parameter. Validating/copying a state does not restore work.
