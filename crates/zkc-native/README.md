# zkc-native

`zkc-native` implements `zkc_runtime::vm::Backend` with independently
installed operation signatures and typed mathematical adapters. The runtime
owns program admission and execution; this crate owns concrete values, installed calls, codecs, capability state and
backend capacity checks. [zkc-kernels](../zkc-kernels/README.md) owns typed
arithmetic, transforms, commitments and curve primitives without VM authority.

## Host transport integration

`NativeBackend` implements `zkc-runtime::host::wire::{WireBackend, ProofBackend}`
in this crate. Installed message support, fixed native widths, conservative
encoding bounds, decode measurements, native codecs, borrowed raw bytes and
Boolean projection remain concrete native responsibilities. `NativeWireError`
is translated to runtime-owned `WireError` at this boundary; generic drivers and
reports have no native value or error dependency. Native application Hosts retain
deployment, setup and public-input authority in `zkc`.

## Construction and authority

Construct `NativeBackend::new(policy, entry, setups)` with an explicit
`SetupRegistry`. An empty registry is valid for computations without PCS keys.
Registry membership authorizes setup material; identifiers in input or proof
bytes cannot extend it. `EntryPolicy::new(domain, arity)` selects an execution
domain and optional homogeneous shape. Named `PortConstraint` values can narrow
individual input shapes and setup identities. PCS operations check their actual
key operands and commitment/proof metadata, including when multiple keys are
authorized. There is no implicit receive-site setup selector.

`resource.rs` owns fresh affine RNG, nonce and transcript capabilities, their
bounded counters, domain separation, generations and retirement. Local frames
receive explicit operand views. `random` owns advancing OS-seeded sources; mathematical kernels accept caller-owned RNGs. `services` binds the four registered random
sampling service contracts to Host-owned providers. It does not install arbitrary
request/reply service families. Attempts retain backend custody and completed
resource effects. `retire` revokes an issued slot outside active frames without
reusing its identity or refunding work.

`Backend::service_support` returns `ServiceSupport`: an independently authored
physical signature and `max_retained_bytes`, the conservative aggregate charge
for one reply tuple. Native service shapes are defined in `services.rs`, without
reusing the runtime's contract resolver. Admission compares the declarations;
query preflight and reply validation enforce the bound. These installation facts
do not authorize a root or replace live lease, generation and owner checks.

## Installed mathematics

The Arkworks, Dalek and Plonky3 providers retain their nominal field, vector,
polynomial, round, sparse matrix, group and pairing kernels where installed.
This includes BLS12-381, BN254, Ristretto255, KoalaBear and its degree-eight and
degree-four extensions, and the binary fields GF(2^64) and GF(2^192). Multilinear KZG, row-oracle operations, external Monero/OpenVM
primitives, sequences, variants, field arrays, fixed vectors and resource units
retain their own type and capacity checks. Domain installation does not imply
that every domain has every group, transcript or PCS operation.

`operations::poseidon2` installs the batched width-16 KoalaBear Poseidon2
permutation from `p3-koala-bear` 0.8.0's default parameters; it charges one
external-work permutation per state before computing. `zkc-kernels::plonky3::words` owns the
canonical and Montgomery four-byte coordinate words of the KoalaBear codecs.
Bit reversal of vectors and table rows is a positional kernel of every field
family. `merkle` installs row commitments backed by `zkc-kernels::plonky3::merkle`: an `Instance` names a
leaf hash, compression, element type and canonical digest encoding over a
Plonky3 `Mmcs`, and every carrier holds digests as fixed-width bytes. Its
Poseidon2 instances, over `koala-bear` rows and over quartic-extension rows
flattened to base coordinates, add pruned multi-openings; `merkle_differential`
compares roots, rows and pruned proofs with Plonky3's `MerkleTreeMmcs` and
`ExtensionMmcs` and with a reference model that makes each permutation call
explicit. The `poseidon2_permutation` test compares the permutation with the
upstream known answer, p3-poseidon2's generic round functions and an integer
implementation.

`native_contracts()` contributes resident `blst/fr`, `blst/g1` and `blst/g2`
scalar and bulk storage to the neutral VM. Canonical layouts remain Arkworks.
The compiler's [Target preferences](../../docs/compiler/representation.md#resident-providers)
select resident BLS12-381 G2 scaling and pairing checks automatically, with
checked conversions at canonical boundaries. Native executes those exact
bindings; provider selection adds no runtime optimizer.
Selected values stay in their provider representation across adjacent calls,
control flow and supported containers. Explicit flat conversion calls delimit
provider boundaries; there is no implicit container conversion.

Complete sequence and variant types retain every physical child, including
inactive alternatives. Resident field arrays and fixed vectors retain typed
scalar backing with exact extents. Sequence and dense operation families receive
one checked complete container parameter, without enumerating every length or
schema. Codec permission combines the installed frame owner with every child
permission; fixed vectors remain local-only. Immutable preparation eligibility
is checked separately from wire support.

Scalar/vector arithmetic uses a small provider family. Installation selects typed
scalar handlers from the backend's own port metadata. Scalar calls do not
construct bulk destinations or workspace; both paths retain their output checks.
Intrinsic value classification borrows installed metadata and compares exact
physical layouts, including catalog identity. Structured polynomial and matrix
operations extend the family only where supported; resident scalars do not
implement placeholder structured operations. Group algebra is separate from
Native value projection, policy and error translation. Resident MSM borrows the
typed provider buffers directly.

`backend/registry.rs` assembles exact implementation ownership. Duplicate owners
and alternatives of alternatives refuse. Alternative implementations inherit the
installed family resolver and must match their primary domain. Constant-time
Ristretto MSM, diagonal contractions, table layouts and the independently
implemented pairwise dot product remain selectable. Resident BLS12-381 MSM declares variable-time input positions independently
of the trusted admission catalog. It requires an explicit compatible execution
policy or an exact scoped timing grant; a role or provider name grants neither.
Computation checkpoints retain the immutable catalog/authorization-view identity;
changes to policy or exact grants require normal execution rather than replay.
Kernel timing premises do not establish a whole-runtime timing guarantee.

Each contract row lists its actual default implementation names. Custom families
list exact implementation/contract pairs. The inventory contains no inferred
provider-by-contract combinations; nominal arguments still need the owner's
signature checks. Runtime and backend rows remain independently authored.
`Backend::Operation` is `NativeOperation`, which implements
`vm::InstalledOperation`. `prepare_binding` returns this immutable handle with
its exact binding, independently resolved signature, handler and static work
classification. The VM instance prepares each distinct binding once when
loading its owned backend. Operations include effectful resource and transcript
calls as well as numerical kernels. Calls retain input, attribute,
resource, policy and output validation; a handle for another binding is refused.
Operation attributes and transcript occurrences stay invocation-specific.
Reached typed call payloads share the installed declaration and signature;
reuse still compares their complete content and exact attributes. Each VM
instance owns its preparation, including when instances share an admitted program.

`numerical` adapts policy and concrete result construction to the independent
`zkc-kernels::numerical` scope and `matrix::RowMajor` views under the
[native numerical-call contract](../../docs/spec/runtime/numerical.md).
Private initialized destinations and scratch share checked memory and work
limits. Exact field adapters and table storage owners supply interpretation;
the scope grants no resource authority or mutation of published inputs.
Dense matvec/split, BLS table fold, KoalaBear opening quotient and coefficient
batch coset evaluation exercise this path. `poly.coset_evaluate_batch` builds
one column-major result from coefficient blocks, with provider-owned transform
workspace; it has its own authored work/storage contract as specified in the
[polynomial contract](../../docs/spec/domains/polynomials.md). Other provider
allocations retain their existing owners and limits.

`numerical::expression` evaluates admitted Ring bodies in bounded chunks. Its
node-major workspace stays local to the reached call; prepared plans retain no
operand values. `zkc-kernels::vector` supplies destination-slice arithmetic shared
by these expressions and dense kernels, including provider-declared field packing
and scalar tails. Chunking changes neither the Kernel/VM contract nor the
minimum managed-memory allowance. CPU-specific packing follows build target
features; portable builds remain supported.

`curve.vector_scale` and `curve.scale_each` optionally batch-normalize projective
results for BLS12-381 and BN254 G1/G2 while retaining affine-base `mul_bigint`.
Native admits the kernel's workspace bound from public length and the numerical
scratch allowance. The typed kernel plan prepares bounded scratch and freezes
the algorithm before arithmetic; its reservation outlives the plan.
Insufficient scratch or failed scratch preparation selects direct scaling.
Existing output preflight and charges remain in place, with no added numerical
work charge. Dalek multiplication paths and their timing properties are unchanged;
Arkworks remains variable-time.

Sparse matrices remain immutable canonical COO. Forward and bilinear kernels
contract occupied rows; transpose scatters entries in stored order without a
second layout. Actual relation-row evaluation reuses node scratch within each
active segment and precomputes output positions. It preserves selected node
order, first input-fetch order, reached constant/embedding failures and existing
work charges; preparation performs no arithmetic or dormant evaluation.

Private custody checks visit active variant payloads and sequence elements in
declaration order without collecting a temporary leaf list. Each capability is
authenticated against the current store; traversal retains neither authority
nor a cached generation. Failed frame exits still clean up their views.

`Policy` ceilings count per-object arity, elements, bytes, setup work and live
resource slots. Setup work is `arity * 2^arity`. Sequence work counts
`3 * (1 + expanded operand nodes)` per call, including repeated shared backing.
External work adds hash calls, hashed bytes, permutations, observes and samples.
These separate metrics do not bound global peak memory or wall-clock time.

`Value` partitions its retained charge for the Runner's
[retained-value ledgers](../../docs/spec/runtime/capacity.md#retained-values-and-logical-work).
Each Arc-held vector, polynomial, path, root list, opening state, table, key,
proof and sparse matrix is one shared allocation. Sequences, variants,
opening-state lists and diagonal views report their own allocation and the
allocations they retain. Field arrays and fixed vectors share their element
allocation and charge their descriptor per binding. Inline scalars and
capabilities belong to their binding. Validation reuse is offered only for
capability-free values. Row openings, element and handle accessors and length
queries declare their operand read extents; other operations are charged their
full operands.

## Native inputs and wire

`encode_native_value` and `decode_native_value` are the single wire API. The
admitted physical type selects a closed `ZKCV` frame; decoding checks exact
length, canonical elements, nominal types, setup metadata and allocation limits.
BLS vectors and group vectors retain native tags 66 and 67. Local polynomials,
rounds, points, alternate table layouts, fixed vectors and private capabilities
have no native wire encoding. Their installed mathematical kernels remain usable
through typed local values. Default BLS tables are supported as native inputs.

`validate_native_input`, `native_input_retained_bytes` and the native measurement
helpers preflight typed inputs and recursive allocation. These checks do not
replace canonical decoding, setup authorization or invocation-wide capacity.
Shared backing is charged in full. Matrix kernels retain their local sparse
nonzero limit; native transport also enforces the current aggregate data limit.

Generated transcripts use only `transcript.native.indexed.observe.data`,
`transcript.native.indexed.challenge` and, for the octic Merlin and hash-chain
suites, `transcript.native.indexed.index`. Explicit templates and coordinates encode
`zkc.native-origin/0`; executor frame names do not enter these occurrences.
Generic observations accept the current native message-data grammar, including
supported cross-domain data. The observation binding accepts either no physical
arguments (default payload storage) or one complete selected payload type,
including all inactive child layouts. Expected Contracts and independently
authored installed metadata require the same logical schema and positive Native
codec support. Observation uses the existing canonical message encoder before
consuming the transcript; selected storage changes neither framing nor custody.
Merlin and Spongefish suites own their exact
framing and reduction; the [hash-chain suites](../../docs/spec/ir/construction.md#native-hash-chain-suites)
are zkc's own construction over Keccak-256 (`transcript.rs`). Authored `external.*` primitives remain separate; see
[their source pins and construction details](../zkc-kernels/src/interop/README.md).

## Validation

Run `cargo test -p zkc-native --all-features`. Tests cover native framing,
malformed values, setup authorization, capabilities, capacity, alternative
implementations and independent mathematical/cryptographic references.
`test-utils` exposes deterministic test entropy explicitly. These tests are
bounded execution evidence, not proof-system security or compiler correctness.
