# EVM verifier target

The EVM target compiles a selected proof Entry's checked verifier closure to
bytecode for a fork of its [target declaration](#target-declaration). It shares
source admission, mathematical realization, construction and closed Exec
formation with the CPU target. It does not execute `zkc.program/0` in EVM. The
prover remains a normal native proof Entry.

## Compilation boundary

The compiler checks the complete constructed protocol before selecting one
participant and its transitive executable symbols. Selection retains the full
checked construction source separately from the executable closure. Target
legality examines reachable operations and types, including nested helpers;
unsupported reachable code refuses compilation. Unused producer mathematics
does not make a supported verifier illegal. The target realizes no conditional
participant completion: a `protocol.finish_if` in the selected verifier refuses
with `evm.completion` before realization. Completions owned by other
participants do not enter the verifier closure.

Arithmetic consumes the installed domain catalog: prime fields with a modulus
of at most 256 bits and installed ascending binomial extensions of degree 2–8.
Extensions retain every coefficient modulo `X^degree - beta`. Multiplication
uses EVM `MULMOD`, including the full intermediate product; scalar inversion
uses ModExp and extension inversion uses bounded polynomial Euclid. Inverting
zero stops before a precompile call.

The target supports checked unsigned 64-bit indices, Booleans, field vectors,
local fixed collections, sequences and variants. Finite folds and collects use
the common callback ABI over elements, indices, ranges, strict zips and Cartesian
products. Admission precedes callbacks, including empty traversals. Product
order, initial state, borrowed scopes and reached failures remain significant.
Vector primitives cover construction, append, length, indexed access, split,
sum and equality; other installed vector operations require target support.

Proofs use either an authored empty transcript or a managed construction over
a transcript suite that the target realizes. The target selects the
realization by the suite's [transcript facts](../formats/contract-declarations.md#nominal-domains),
never by its spelling: the `hash-chain` family over `keccak256`, binding the
suite identity at initialization. The decoder is either `fr64be` over a prime
field with an installed native field codec and at most 256 bits, or `rejection31le` over a supported ascending
binomial extension whose base characteristic is below 2^31. The former reduces
all 64 big-endian request bytes modulo the declared characteristic. The latter
reads masked u32 little-endian candidates, rejects candidates at or above the
base characteristic, and retains accepted coordinates in ascending basis order
across at most sixteen 64-byte answers. Extension coefficients use the same
ascending basis as arithmetic and the native codec, in 32-byte physical cells. Those internal answers consume one
logical transcript transition. Arithmetic fields elsewhere in the verifier do
not select the challenge decoder.

Installed BLS Fr and KoalaBear quartic/octic Keccak hash-chain suites have these
facts. Other families, hashes or decoders refuse with `evm.construction`, naming
the fact the target does not realize. A program without a transcript has no
challenge field and no transcript helpers.

Managed scalar index requests and native index blocks use the suite's installed
capabilities and the [shared request contract](../formats/native-index-block.md).
Block order and duplicates are preserved. The EVM verifier checks a supplied
grinding witness; native proving owns the bounded search. For difficulty zero,
a nonzero witness refuses before transcript consumption. For positive
difficulty, the complete request and its atomic transition precede a failed
gate; no result or successor is published on that failure. The existing target
transition, element and memory ceilings and EVM gas remain separate from the
native numerical-work allowance. External services, curve operations, other
authentication schemes and full STARK deployment require further target support.

### Authenticated rows and univariate polynomials

`oracle.check` realizes the installed base, quartic and octic KoalaBear Keccak
row commitments. The exact root domain selects its installed `ValueField`,
Keccak scheme, 32-byte digest and native root/path codec facts. Poseidon roots
remain transportable but do not acquire Keccak authentication. The operation
consumes the existing complete root/path frames and the ordinary field-vector
layout. Common oracle realization continues to own anchors, immutable extents,
physical layout selection, history, packet deduplication and release order.
Each logical authentication occurrence executes, including repeated positions
whose physical response is shared.

The native leaf preimage is the NUL-terminated ASCII prefix
`zkc.oracle.keccak256.leaf/0`, u64 little-endian byte length of the native
element codec identity, that ASCII identity, u64 little-endian width and height,
then ascending canonical u32 little-endian field coordinates. The identities
are `koala-bear.canonical-u32le/0`,
`koala-bear.ext4-binomial3.ascending-u32le/0` and
`koala-bear.ext8-binomial3.ascending-u32le/0`; these differ from native frame
codec identities. Each node hashes the NUL-terminated ASCII prefix
`zkc.oracle.keccak256.node/0` followed by the left and right 32-byte digests.
Sibling orientation follows physical position bits from least significant
upwards. Non-power-of-two heights use the native cap-zero binary-tree path
depth, `ceil(log2(height))`; padded leaves are zero digests.

Shape admission precedes coordinate admission: width and height must be
positive, height at most `2^24`, and checked width times height at most `2^20`.
The product limit is a resource refusal. An out-of-range coordinate is a source
stop. Once admitted, wrong row width, wrong path depth or root mismatch returns
false. A common authenticated-query consumer requires that Boolean at its
existing source guard. Canonical decode errors remain decode refusals. The
opened row, path and temporary hash buffer retain their separate target limits;
the committed shape does not materialize a table in EVM. All temporary hash
storage is admitted before the first ordered hash.

`poly.domain_root` and `poly.domain_point` use the installed coset convention's
exact maximal root and base-subgroup order, inherited through `BaseField`.
They embed roots into extensions and multiply every shift coefficient by the
selected root power. Domain admission checks a positive power-of-two size and
the installed order, then the native `2^20` element cap, then nonzero shift,
then coordinate. These are source stops, including the native
`refused:coset-element-limit` mapping. Extension output allocation precedes
domain admission, preserving scalar-output preflight.

Source codes 10/11 identify oracle shape/coordinate failures; 12/13/14/15
identify coset size/zero-shift/coordinate/element-limit failures. Oracle element
exhaustion uses resource code 16. Row/path length and root mismatches return the
Boolean result and use no failure code.

Internal `poly::UnivariateType` values use the shared coefficient layout as an
immutable pointer/count pair. `poly.from_coefficients` trims trailing zero
field elements and copies the normalized prefix with checked allocation; the
zero polynomial has no coefficients. `poly.univariate_evaluate` uses Horner
evaluation with the existing installed field arithmetic. This internal layout
grants no public or proof wire ingress. `index.select` converts to standard
`arith.select` over the existing Boolean and index lanes.

Internal normalized polynomials are constructed only by the dedicated
normalizing operation; matching vector storage does not grant vector operations
the polynomial contract.

These operation implementations permit generic FRI verifier closure without
recognizing a protocol name. The focused Direct quartic Keccak fixtures in
`common/tests/evm/fixtures/` explicitly select their transcript and row scheme.
The `(LogSize=5, TerminalLog=0, Rounds=3, Queries=8)` fixtures are structural
controls. Scalar and product-block query policies are separate authored
applications. Their source implementations do not establish deployed closure,
production security or a FRI soundness theorem. Unchanged participant-loop,
transcript, proof, allocation, deployment-size and gas ceilings still apply.

Target MLIR combines exact standard Func, SCF and Arith operations with
separate ODS-defined EVM operations for checked arithmetic, collections, wire
access, scope, transfer and transcript transitions. Each operation checks its
operand and result lanes, logical type and applicable attributes. A string
opcode is not an operation contract. Fallible or ordered operations retain
observable effects even when their results are unused.

Preparation resolves the reachable symbols, callback contracts and supported
control flow. It does not build a second SSA instruction stream. MLIR dialect
conversion then rewrites the original executable regions, expanding logical
values into physical lanes through one type converter. One shared layout owner
defines logical signatures, scalar lanes, coefficient strides and aggregate
lane cells for conversion, operation checking, arithmetic and wire handling.
Full conversion and the final positive legality check reject residual
unsupported operations and types before Yul export. Index overflow, division by
zero and invalid shifts retain their failure behavior. Runtime scope and
transcript tickets preserve the selected closure's ownership checks. Yul
emission follows the typed operations; it does not recognize protocol names.

Transcript operations carry the shared typed native origin, including its
source occurrence, path and event. Export projects its existing native byte
encoding; it defines no target-local occurrence grammar. Unsupported origin
forms refuse compilation rather than losing their coordinates.

Prime scalars use one canonical word; extensions use immutable coefficient
buffers. Field vectors store coefficients inline, while sequences store their
elements' lane cells. Variants store a tag and only the active payload. This
representation conveys neither wire permission nor resource ownership.

Checked nominal `resource_unit` leaves occupy zero value lanes in local
signatures, outcomes, transfers and callback state. Logical slots and exact
nominal signatures are checked before erasure; enclosing record payloads keep
all their data lanes. Only the installed create/pass/consume bookkeeping
operations erase, retaining their active-scope checks and surrounding ordered
calls and source failures. Common closure admission still checks affine uses
and root succession. Unlike CPU execution's authenticated unit handles, the
closed EVM target exposes no unit handle or byte encoding. Units do not count
as managed transcript generations and cannot enter public or proof wire ports.
Other runtime capabilities still require their explicit target realization.

Pure expressions and ordered helper calls use the same supported arithmetic.
An explicit implementation constraint must be honored; a CPU provider selector
does not silently select an EVM realization. The invocation adapter selects the
Entry's checked Boolean acceptance output, including when other data results
precede it, and validates all returned managed transcript state.

Bound `control.require` uses ordered `evm.control.require`: false reports
`SourceStop(16)` for native backend `rejected:require`. It does not acquire a
protocol guard site or turn that backend failure into a normal false result.

Checked conditional numeric loops consume their leading Boolean through
`runtime.take_condition`. Lowering checks the live transfer ticket, returns the
Boolean lane and preserves that one ticket with the exact remaining payload.
It allocates no second ownership ticket and does not move or erase effects.
This does not enable conditional participant completion.

## Target declaration

`common/targets/evm.json`, format `zkc.evm-target/0`, is the one authored
source of the target's ABI, tool configuration, fork mapping, deployment
ceilings and revert classes. It stays outside the
[logical catalog](../formats/contract-declarations.md): it states no
operation, codec or suite fact. Its identity is `zkc.evm-target/0:` followed by
the lowercase SHA-256 of the file's exact bytes, so any change to it is a new
identity.

| Field | Content |
|---|---|
| `abi` | The verifier's Solidity `signature`, its four-byte `selector` and the standard ABI `json` |
| `solc` | The pinned compiler `version`, with its commit, and the standard-JSON `optimizer` settings |
| `forks` | Per fork: `name`, solc `evmVersion` (`solc`), engine `hardfork`, consensus `transaction_gas_cap` or null, `runtime_code_bytes`, `initcode_bytes` and the named consensus `rules` |
| `default_fork` | The fork selected when a caller names none |
| `validation_gas` | The per-transaction gas budget of validation runs on a fork without a `transaction_gas_cap` |
| `validation_gas_maximum` | The most gas any validation transaction requests, and the block gas limit of validation runs |
| `limits` | Per deployment ceiling: `name`, `minimum` and `maximum` |
| `reverts` | Per revert class: `class` and its four-byte ASCII `tag` |

The declared forks are `cancun`, `prague` and `osaka`; the default is `osaka`.
Osaka enforces the EIP-7825 transaction gas cap of 16,777,216 and the EIP-7883
ModExp pricing. The validation runner checks these fork facts against its pinned
engine; the target declaration owns the selected profile. Each
validator requires exactly these fields at every level and rejects repeated
keys, fractional numbers and non-ASCII bytes. Fork names, solc `evmVersion`
values and hardforks are unique, fork names are lowercase, and the default
names a fork. Every fork lists explicit, unique `EIP-N` rules, including
EIP-5656 because the emitted code copies memory with MCOPY; rules are not
inherited between forks. The selector is eight lowercase hexadecimal digits
equal to the first four bytes of the signature's Keccak-256, and the ABI JSON
declares exactly that function. Limit names are unique and each limit satisfies
1 ≤ `minimum` ≤ `maximum` < 2^64. Revert classes and tags are unique, and a tag
is four uppercase ASCII letters.

The compiler's configure step validates the declaration with
`common/targets/generate.py` and generates its fork, limit and revert tables,
so a declaration change changes the compiler's build identity. The Rust SDK
build validates the same file independently and generates the typed
`zkc::evm_target` module, which the SDK and CLI read for forks, solc settings,
the ABI and selector, and ceilings. Shared refusal cases in
`common/targets/evm-validation-cases.json` name the rule each validator must
report. The deployed-validation runner reads the declaration's forks and
validation gas maximum, and refuses to run when a fork's engine hardfork has a different transaction gas cap or
code size limits; the validation harness checks the declaration with
`generate.py` and reads every target fact from it. Every reader validates the
facts it uses; an artifact's self-stated numbers are not authority. The `zkc.evm-source/0` response names the
declaration by its identity in `declaration`, beside the selected `fork`, so a
reader with a different declaration refuses it.

## Invocation

The sole function is:

```solidity
function verify(bytes[] publicInputs, bytes context, bytes proof)
    external view returns (bool accepted);
```

The declared selector is `0xa488e1e4`. Public values follow descriptor port order and use
the existing [canonical value codecs](../realization/codecs.md). Context is an
opaque byte string. Proof uses the unchanged [native framed transport](../formats/proof.md).
The last two arguments have the same ABI type; their order remains significant.

The invocation boundary is emitted from one typed endpoint, built while the
complete constructed source and the selected candidate are available: the
selected participant's logical signature, the validator's original input and
output ports from the checked projection record, and the construction's checked
descriptor rows. Each public row must name the validator, the projected port
and the endpoint input's nominal type; its codec is the construction's. A
public row the target cannot lay out refuses with `evm.layout`. Yul emission
borrows this endpoint and neither reparses the original source nor derives a
codec again.

Wire sites require the complete native message type and an exact supported
installed codec. Supported leaves are Boolean, index, indices, bytes, the
installed BLS Fr, BN254 Fr, Ristretto scalar and Plonky3 field/vector codecs,
BLS Fr fixed arrays, and installed Keccak/Poseidon row-root and path envelopes.
Every byte fact of a leaf comes from the catalog's
[frame tags and codecs](../formats/contract-declarations.md#frame-tags-and-codecs):
the codec row's tag and element width, the aggregate frame's tag, and the
commitment row's digest and digest-word widths. A field coordinate has its
base field's codec width. A codec whose widths the target's layouts do not
realize refuses Yul export; its diagnostic carries the `evm.wire-type` code.
Sequences and variants compose these leaves. Root/path wire handling preserves
canonical envelopes; authentication is the separate typed operation above. Unsupported inactive arms
and empty-container element types still refuse compilation.

Each reached value is preflighted before materialization, sharing node, element,
depth and retained-memory accounting across its whole structure. Encoding writes
one canonical frame. Transcript observation covers that complete frame, including
container tags, lengths and payloads.

The target accepts one canonical ABI encoding: sequential tails, exact offsets,
zero padding and complete calldata consumption. Aliased or overlapping tails,
holes, offset arithmetic overflow and trailing bytes refuse. A general Solidity
ABI decoder may accept encodings outside this profile.

The proof header binds the exact native invocation root, including original
MLIR SHA-256 identity, construction descriptor, selected ports, canonical public
values and context. Immutable descriptor and origin bytes are copied directly
from deployment data; the invocation encoding remains identical to native. The
verifier checks the header before execution, then decodes each frame only at its
reached receive operation. It requires proof EOF before publishing either Boolean
result. A source stop
precedes a malformed frame that execution never reaches.

Keccak transcript transitions preserve primitive input bytes, results and order,
including final delivery observations with no later state reader. Emission uses
an opaque one-input `POP` sink where solc could otherwise delete a required
hash. Validation compares the actual deployed artifact's complete primitive
trace, not its textual Yul or a static opcode count.

## Outcomes and capacity

A successful call returns the canonical ABI Boolean. False is a completed
verification decision. Reverts have a four-byte declared class followed by one
32-byte code:

| Class | Bytes | Meaning |
|---|---|---|
| Source stop | `ZKCS` | Reached protocol or numerical failure |
| Decode refusal | `ZKCD` | Invalid ABI, public wire, proof header or reached frame |
| Target fault | `ZKCT` | Violated target ownership or internal representation contract |
| Resource refusal | `ZKCR` | Exceeded an immutable deployment ceiling, reached native operation allowance or the declared sampler limit |

EVM out-of-gas is a machine halt, separate from these structured outcomes. EVM
gas does not implement native VM instruction fuel.
The rejection sampler uses `ZKCR` code 15 after all sixteen answers fail to
complete the field value. Native index shape and canonical-zero-witness checks
use `ZKCS` code 5; a failed positive gate uses `ZKCS` code 0 after its complete
request. These target codes do not replace the native outcome identifiers.

Each deployment fixes one effective value per declared ceiling, within the
ceiling's declared minimum and maximum. The declaration alone states these
ranges; the defaults are the maxima, and compiler callers may lower a ceiling,
never raise it. The `zkc.evm-source/0` response carries the effective values,
which every reader checks against the declared ranges.

| Ceiling | What it bounds |
|---|---|
| `participant_loop_maximum` | The checked maximum of each participant loop. A larger one refuses compilation with `evm.participant-loop-maximum`, naming both maxima; transcript transitions remain the only bound across loops |
| `public_elements` | Collection elements per reached wire value, and the selected output elements of a local collect |
| `frame_bytes` | Bytes of one public or proof frame |
| `public_bytes` | Public wire bytes of one call |
| `context_bytes` | Context bytes of one call |
| `proof_bytes` | Proof bytes of one call |
| `calldata_bytes` | Calldata bytes of one call |
| `root_bytes` | Bytes of the invocation binding root |
| `memory_bytes` | Simultaneous retained and rounded temporary memory, including block preflight workspace; its declared minimum holds the fixed target state |
| `transcript_transitions` | Transcript transitions of one call |
| `path_siblings` | Digests of one Merkle path envelope, for byte and digest-word paths alike. One more refuses with its own resource code, after the element charge |

The `path_siblings` maximum equals the element ceiling that bounds a native
path's digests, so a deployment at its maxima accepts every path that native
accepts. Equal path ceilings do not make the admissible workloads equal: the
calldata, frame, root, memory and gas limits of an EVM call can still refuse a
proof that native accepts.

Finite local ranges retain the native bound of 1,048,576. Coordinate sequences
have at most 64 elements and origin templates fit a 4,096-byte workspace.
Callers cannot supply per-call budgets through the verifier ABI.

Validation runs request one transaction budget per fork, for deployment and
calls alike: the fork's consensus `transaction_gas_cap`, or the declaration's
`validation_gas` for a fork without one. `validation_gas` and every declared
`transaction_gas_cap` are at most `validation_gas_maximum`, so no default budget
exceeds it; the runner refuses an explicit request above it. Only the
deployed-validation runner and harness read `validation_gas` and its maximum. It is never a deployment ceiling, never reaches
compilation, and never overrides the selected fork's gas rules. A runtime at the
fork's code size ceiling deploys within the budget.

## Artifact and tool ownership

`zkc compile --target=evm` selects the same source proof Entry as native
compilation. The SDK's `evm` feature provides this target without a CPU runtime
or EVM engine dependency. Compilation requires an explicit installed solc path
and independent executable SHA-256 pin; no download or PATH substitution occurs.
The declaration pins the solc release and its standard-JSON settings.
`--evm-version` selects a declared fork, defaulting to the declared default. The
typed SDK equivalent is `evm::Options { fork, compile }`. Effective common
mathematical/oracle options flow through checked compilation and are bound into
source and artifact identity; CPU storage and physical-target selections refuse.
Exact standard-JSON settings are retained in `solc-input.json`. Reuse requires
the same fork and options.

### Source response

The compiler's EVM response, `zkc.evm-source/0`, has one producer, the library's
`encodeEvmCompilation`; the language driver passes it the selected Entry and
the project's identities and prints its result unchanged. It is one JSON object
with exactly these members:

| Member | Content |
|---|---|
| `format` | `zkc.evm-source/0` |
| `declaration` | The installed [target declaration](#target-declaration)'s identity |
| `fork` | The selected declared fork |
| `options` | The effective common-stage options, the same list and values a CPU `zkc.entry/0` package publishes for the same selection |
| `limits` | The deployment's effective ceilings, one per declared ceiling |
| `entry` | The selected source Entry |
| `capture`, `installation`, `original` | The authored capture, installation and original identities |
| `source_format` | `zkc.original-mlir/0` |
| `compiler` | The compiler toolchain identity |
| `policy` | The native proof policy; its entry symbol names the protocol, distinct from `entry` |
| `descriptor` | The native proof descriptor |
| `yul` | The target source |

The response carries no tool facts: the SDK takes the solc release and settings
and the verifier ABI from the declaration and writes `abi.json` from it. The
numerical expression mode is not an option of this target, because only CPU
physical selection reads it.

A `zkc.evm-artifact/0` directory contains:

| File | Content |
|---|---|
| `source.json` | Exact [source response](#source-response) |
| `verifier.yul` | Target source |
| `abi.json` | Verifier ABI of the target declaration |
| `solc-input.json` | Exact tool request and settings |
| `creation.bin` | Binary deployment bytecode |
| `runtime.bin` | Binary deployed bytecode |
| `manifest.json` | File hashes, compiler/tool identities and build key |

The manifest binds authored capture, installation and original identities
through the exact compiler response, as well as target settings and bytecode.
Source capture validates the complete current response and its deployment
ceilings against the declaration, and rejects duplicate or unknown JSON object
fields.
Import requires an independently retained hash of the exact manifest bytes.
Internal checksums alone do not authenticate a substituted directory. Reuse
requires an authenticated immutable artifact and the exact build key; compiler
and solc identity checks still run. Deployment initcode and runtime obey the
selected fork's declared EIP-3860 and EIP-170 size limits.

Publication stages a complete sibling directory and atomically renames it
without replacement. Existing destinations refuse. The current atomic directory
publisher requires Linux; unsupported platforms refuse explicitly.

See the [Sumcheck project](../../../examples/projects/sumcheck-keccak/README.md)
for commands and the [deployed validation adapter](../../../common/tests/evm/README.md)
for execution, mutation and trace controls. These tests establish bounded
agreement for their subjects, not a general target refinement theorem.

## Refusal codes

The compiler and the SDK each refuse with their own codes; a code names the
boundary that refused, and its detail is diagnostic text. A compiler refusal
reaches an SDK caller inside `source-compilation`, whose diagnostics carry the
compiler's code and detail.

The compiler's EVM target refuses, in pipeline order:

| Code | Refuses |
|---|---|
| `evm.options` | A `language-evm` invocation with a CPU or observation option: `--cpu-target=`, `--dump=` or `--release-storage` |
| `evm.fork` | `--evm-version=` on another command or given twice, or a fork name or selection that is not a declared fork |
| `evm.limits` | A deployment ceiling outside its declared minimum and maximum |
| `evm.source-limit` | An original over 16 MiB, empty, nested beyond the MLIR nesting limit or with a filename over 4,096 bytes, or a `zkc.evm-source/0` response over 16 MiB |
| `evm.source` | An original that does not parse or is not admitted at its stage; the detail is the captured diagnostics |
| `evm.entry` | A selected Entry that is not a checked proof Entry, a proof without exactly one native Boolean acceptance, or a lowered module without exactly one EVM entry function |
| `evm.construction` | An explicit construction, services, draws or gates without a transcript suite, a non-native proof format, or a transcript suite the target does not realize: not an installed hash-chain suite over Keccak-256 that binds its identity, has one of the supported decoder and challenge-field combinations |
| `evm.field` | A field without an exact installed prime modulus below 2^256, or an extension that is not a declared binomial extension of degree 2 to 8 over such a prime field |
| `evm.descriptor` | A common construction descriptor that is not the policy's `zkc.native-proof-descriptor/0` with a selection |
| `evm.closed-execution` | A constructed module the closed-execution pipeline refuses; the detail is the captured diagnostics |
| `evm.endpoint` | A checked endpoint that is not exactly one selected validator with one checked projection record, unconsumed inputs or affine results, a transcript capability other than the managed suite's, a public row that does not name the validator, port and type, outputs out of source order, or an acceptance that is not exactly one Boolean |
| `evm.layout` | A public input type without an EVM value layout: not complete Copy and Drop logical data, a vector object other than a commitment or proof, or no local EVM representation |
| `evm.completion` | A `protocol.finish_if` in the selected verifier |
| `evm.participant-loop-maximum` | A `protocol.loop` in the selected verifier whose checked maximum exceeds the deployment's `participant_loop_maximum` |
| `evm.lowering` | A reachable operation or type without an EVM realization; the joined `evm.diagnostics` names it with `[evm.unsupported-operation]` or `[evm.unsupported-type]` |
| `evm.control-flow` | A lowered function whose control flow cannot be structured, such as a statically infinite loop |
| `evm.target-legality` | An operation or type that remains outside the closed target after lowering or before export |
| `evm.yul` | A Yul export failure at the invocation boundary or in a target function; the joined `evm.diagnostics` carries the exporter's reason, `[evm.yul]` followed by the coded refusal: `evm.wire-type` for a message type without a supported wire frame, `evm.wire-operation` for a sequence, bytes or variant operation without a wire implementation, `evm.arithmetic` for a field or vector operation without an implementation; a static invocation root above `root_bytes` reports `[evm.root-limit]` |

`evm.diagnostics` is never a refusal of its own: it joins a lowering or export
refusal with every diagnostic captured so far.

The SDK refuses, by phase:

| Code | Refuses |
|---|---|
| `evm-option-unsupported` | A CPU-only option on an EVM build: `--cache`, `--dump`, `--report` or `--release-storage`, a profile that releases storage, or `evm::Options` that release storage |
| `evm-fork` | A fork spelling that is not a declared fork name, or a response `fork` that is not a string |
| `evm-solc-required`, `evm-solc-pin-required` | A command-line EVM build without `--solc` or without `--solc-sha256` |
| `evm-artifact-limit` | A compiler response, tool JSON or encoded file over 16 MiB |
| `evm-json` | A response or tool document that is not bounded JSON: invalid, a duplicate key, a non-natural number, or beyond the node or depth limit |
| `evm-source-format` | A response that is not an object with exactly the [source response](#source-response) members and formats, or with an empty `yul` or `entry` |
| `evm-target-declaration` | A response whose `declaration` is not the installed declaration's identity |
| `evm-source-options` | Response options that do not decode, release storage, or differ from the requested options or fork |
| `evm-source-limits` | Response `limits` that do not name exactly the declared ceilings, or a ceiling outside its declared range; at call encoding, a missing or out-of-range ceiling |
| `evm-source-identity` | A `capture`, `installation`, `original` or `compiler` that is not a SHA-256 digest, or public rows that do not name the validator and the policy's public ports in order |
| `evm-source-descriptor` | A descriptor or policy outside the exact shape the target realizes, or a selection that is not the normalized requested oracle selection |
| `evm-solc-path` | A solc path that cannot be canonicalized |
| `evm-solc-pin` | A pin that is not a SHA-256 digest, a snapshot whose digest differs from it, or a path that no longer names the snapshotted executable |
| `evm-solc-snapshot-unsupported` | A platform that cannot take an immutable executable snapshot |
| `evm-solc-limit` | A solc executable or output over 16 MiB |
| `evm-solc-io` | A snapshot, temporary directory or process failure |
| `evm-solc-timeout` | A solc run longer than 120 seconds |
| `evm-solc-failed` | A solc run that exits unsuccessfully |
| `evm-solc-version` | A solc whose `--version` output does not name the pinned release |
| `evm-solc-diagnostic` | A solc output with an error |
| `evm-solc-contract` | A solc output without exactly one `verifier.yul` contract |
| `evm-solc-bytecode` | Creation or deployed bytecode that is not hexadecimal |
| `evm-compiler-pin` | A compiler identity that is not a SHA-256 digest |
| `evm-cache-key` | A reused artifact whose build key is not the key of this source, compiler, solc and settings |
| `evm-artifact-pin` | An expected manifest pin that is not a digest, or a manifest whose SHA-256 differs from it |
| `evm-artifact-read` | An artifact directory or file that is unreadable, not a regular file, or over 16 MiB |
| `evm-artifact-directory` | An artifact directory that is a symbolic link |
| `evm-manifest` | A manifest with unknown or mistyped fields, an undeclared fork, another format or solc release, other than six files, or identities that are not digests |
| `evm-artifact-files` | A manifest without one of the six artifact files |
| `evm-artifact-identity` | An artifact file over 16 MiB or whose SHA-256 differs from its manifest entry |
| `evm-artifact-settings` | A manifest `evm_version` other than the source fork, or a `solc-input.json` other than the declared input |
| `evm-artifact-source` | A `verifier.yul` other than the source's Yul, or an `abi.json` other than the declared ABI |
| `evm-code-size` | Empty creation or runtime bytecode, or bytecode above the fork's initcode or runtime code ceiling |
| `evm-artifact-build-key` | A manifest build key other than the recomputed key |
| `evm-output-path` | A destination that cannot be made absolute or whose parent cannot be resolved |
| `evm-output-exists` | A destination where anything, including a dangling symbolic link, exists |
| `evm-output-stage` | A failure to stage the sibling directory or its files |
| `evm-output-publish` | A failure of the no-replace rename, including a destination that appears concurrently |
| `evm-atomic-publication-unsupported` | Publication on a platform without the atomic directory publisher |
| `evm-calldata-limit` | Public inputs, context or proof above their byte ceilings, calldata above `calldata_bytes`, or a size computation that overflows |

A [target declaration](#target-declaration) that breaks a rule refuses the build
instead: the generator and the SDK build each name the broken rule.
