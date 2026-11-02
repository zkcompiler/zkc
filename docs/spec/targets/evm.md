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
suite identity at initialization, with the `fr64be` decoder, whose challenge
field is a prime field of at most 256 bits. That realization reduces all 64
big-endian request bytes modulo the challenge field's declared characteristic,
independently of other arithmetic fields in the verifier. Of the installed
suites, `hash-chain.keccak256.bls12-381.fr64be/0` has these facts; a suite with
another family, hash or decoder refuses with `evm.construction`, naming the
fact the target does not realize. A program without a transcript has no
challenge field and no transcript helpers. External services, curve
operations, Merkle authentication and full FRI/STARK deployment require further
target support.

Legalized target MLIR uses standard Func, SCF and Arith operations with explicit
EVM word operations and ordered checked operations. Vector values become bounded
memory slices. One shared layout owner defines logical signatures, scalar lanes,
coefficient strides and aggregate lane cells for conversion, operation checking,
arithmetic and wire handling. The final conversion rejects all residual
unsupported operations and types. Index overflow, division by zero and invalid
shifts retain their failure behavior. Runtime scope and transcript tickets preserve the selected
closure's ownership checks. Yul emission follows these operations; it does not
recognize protocol names.

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
| `limits` | Per deployment ceiling: `name`, `minimum` and `maximum` |
| `reverts` | Per revert class: `class` and its four-byte ASCII `tag` |

The declared forks are `cancun` and `prague`; the default is `cancun`. Each
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
`zkc::evm_target` module. Shared refusal cases in
`common/targets/evm-validation-cases.json` name the rule each validator must
report. Every reader validates the facts it uses; an artifact's self-stated
numbers are not authority. The `zkc.evm-source/0` response names the
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

Wire sites require the complete native message type and an exact supported
installed codec. Supported leaves are Boolean, index, indices, bytes, the
installed BLS Fr, BN254 Fr, Ristretto scalar and Plonky3 field/vector codecs,
BLS Fr fixed arrays, and installed Keccak/Poseidon row-root and path envelopes.
Every byte fact of a leaf comes from the catalog's
[frame tags and codecs](../formats/contract-declarations.md#frame-tags-and-codecs):
the codec row's tag and element width, the aggregate frame's tag, and the
commitment row's digest and digest-word widths. A field coordinate has its
base field's codec width. A codec whose widths the target's layouts do not
realize refuses with `evm.wire-type`.
Sequences and variants compose these leaves. Root/path support preserves their
canonical envelopes; it performs no authentication. Unsupported inactive arms
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
| Resource refusal | `ZKCR` | Exceeded an immutable deployment ceiling |

EVM out-of-gas is a machine halt, separate from these structured outcomes. EVM
gas does not implement native VM instruction fuel.

The compiler fixes ceilings in each deployment, each within its declared
minimum and maximum. The declared maxima are 10 rounds, 1,024 collection elements per reached wire value, 65,536 bytes per frame
and proof, 131,072 public wire bytes, 4,096 context bytes, 262,144 calldata and binding-root bytes,
2,097,152 memory bytes and 64 transcript transitions. Compiler callers may
lower supported ceilings, never raise them. Finite local ranges retain the
native bound of 1,048,576; local collects apply the collection ceiling to
selected output elements after their callbacks. Coordinate sequences have at
most 64 elements and origin templates fit a 4,096-byte workspace. Callers cannot supply per-call
budgets through the verifier ABI. The practical validation gas ceiling is
20 million; it does not override the selected fork's gas rules.

## Artifact and tool ownership

`zkc compile --target=evm` selects the same source proof Entry as native
compilation. The SDK's `evm` feature provides this target without a CPU runtime
or EVM engine dependency. Compilation requires an explicit installed solc path
and independent executable SHA-256 pin; no download or PATH substitution occurs.
The declaration pins solc `0.8.38+commit.1835d247`. `--evm-version` selects a
declared fork, defaulting to the declared default. The typed SDK equivalent is
`evm::Options { fork, compile }`. Effective common mathematical/oracle options
flow through checked compilation and are bound into source and artifact identity;
CPU storage and physical-target selections refuse. Exact standard-JSON settings
are retained in `solc-input.json`. Reuse requires the same fork and options.

A `zkc.evm-artifact/0` directory contains:

| File | Content |
|---|---|
| `source.json` | Exact compiler response, checked source identities, target declaration identity, descriptor and ceilings |
| `verifier.yul` | Target source |
| `abi.json` | Verifier ABI |
| `solc-input.json` | Exact tool request and settings |
| `creation.bin` | Binary deployment bytecode |
| `runtime.bin` | Binary deployed bytecode |
| `manifest.json` | File hashes, compiler/tool identities and build key |

The manifest binds authored capture, installation and original identities
through the exact compiler response, as well as target settings and bytecode.
Source capture validates the complete current response, repeated metadata and
deployment ceilings, and rejects duplicate or unknown JSON object fields.
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
