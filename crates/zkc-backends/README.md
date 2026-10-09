# Native backend adapters

`zkc-backends` implements `zkc-runtime::interactive::Backend` with independently
installed operation signatures and native mathematical kernels. The runtime
owns program admission and execution; this crate owns values, cryptographic
operations, capability state and backend capacity checks.

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
receive explicit operand views. `services` binds the four registered random
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
This includes BLS12-381, BN254, Ristretto255, KoalaBear and its degree-eight
extension. Multilinear KZG, row-oracle operations, external Monero/OpenVM
primitives, sequences, variants, field arrays, fixed vectors and resource units
retain their own type and capacity checks. Domain installation does not imply
that every domain has every group, transcript or PCS operation.

`backend/registry.rs` assembles exact implementation ownership. Duplicate owners
and alternatives of alternatives refuse. Alternative implementations inherit the
installed family resolver and must match their primary domain. Constant-time
Ristretto MSM, diagonal contractions, table layouts and the independently
implemented pairwise dot product remain selectable. No variable-time MSM
public-operand authority is installed. Kernel-specific timing properties do not
establish a timing guarantee for the entire runtime.

Each contract row lists its actual default implementation names. Custom families
list exact implementation/contract pairs. The inventory contains no inferred
provider-by-contract combinations; nominal arguments still need the owner's
signature checks. Runtime and backend rows remain independently authored.

Private custody checks visit active variant payloads and sequence elements in
declaration order without collecting a temporary leaf list. Each capability is
authenticated against the current store; traversal retains neither authority
nor a cached generation. Failed frame exits still clean up their views.

`Policy` ceilings count per-object arity, elements, bytes, setup work and live
resource slots. Setup work is `arity * 2^arity`. Sequence work counts
`3 * (1 + expanded operand nodes)` per call, including repeated shared backing.
External work adds hash calls, hashed bytes, permutations, observes and samples.
These separate metrics do not bound global peak memory or wall-clock time.

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

Generated transcripts use only `transcript.native.indexed.observe.data` and
`transcript.native.indexed.challenge`. Explicit templates and coordinates encode
`zkc.native-origin`; executor frame names do not enter these occurrences.
Generic observations accept the current native message-data grammar, including
supported cross-domain data. Merlin and Spongefish suites own their exact
framing and reduction. Authored `external.*` primitives remain separate; see
[their source pins and construction details](src/external/README.md).

## Validation

Run `cargo test -p zkc-backends --all-features`. Tests cover native framing,
malformed values, setup authorization, capabilities, capacity, alternative
implementations and independent mathematical/cryptographic references.
`test-utils` exposes deterministic test entropy explicitly. These tests are
bounded execution evidence, not proof-system security or compiler correctness.
