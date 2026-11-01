# EVM verifier target

The EVM target compiles a selected proof Entry's checked verifier closure to
Cancun bytecode. It shares source admission, mathematical realization,
construction and closed Exec formation with the CPU target. It does not execute
`zkc.program/0` in EVM. The prover remains a normal native proof Entry.

## Compilation boundary

The compiler checks the complete constructed protocol before selecting one
participant and its transitive executable symbols. Selection retains the full
checked construction source separately from the executable closure. Target
legality examines reachable operations and types, including nested helpers;
unsupported reachable code refuses compilation. Unused producer mathematics
does not make a supported verifier illegal.

The initial profile uses BLS12-381 Fr, field vectors, checked unsigned 64-bit
indices, Boolean control and the managed
`hash-chain.keccak256.bls12-381.fr64be/0` construction. Field multiplication uses
EVM `MULMOD`, including the full intermediate product. A challenge reduces all
64 big-endian request bytes modulo Fr. Other fields, custom constructions,
external services and curve operations require further target support.

Legalized target MLIR uses standard Func, SCF and Arith operations with explicit
EVM word operations and ordered checked operations. Vector values become bounded
memory slices. Index overflow, division by zero and invalid shifts retain their
failure behavior. Runtime scope and transcript tickets preserve the selected
closure's ownership checks. Yul emission follows these operations; it does not
recognize protocol names.

Pure expressions and ordered helper calls use the same supported arithmetic.
An explicit implementation constraint must be honored; a CPU provider selector
does not silently select an EVM realization. The invocation adapter selects the
Entry's checked Boolean acceptance output, including when other data results
precede it, and validates all returned managed transcript state.

## Invocation

The sole function is:

```solidity
function verify(bytes[] publicInputs, bytes context, bytes proof)
    external view returns (bool accepted);
```

The selector is `0xa488e1e4`. Public values follow descriptor port order and use
the existing [canonical value codecs](../realization/codecs.md). Context is an
opaque byte string. Proof uses the unchanged [native framed transport](../formats/proof.md).
The last two arguments have the same ABI type; their order remains significant.

The target accepts one canonical ABI encoding: sequential tails, exact offsets,
zero padding and complete calldata consumption. Aliased or overlapping tails,
holes, offset arithmetic overflow and trailing bytes refuse. A general Solidity
ABI decoder may accept encodings outside this profile.

The proof header binds the exact native invocation root, including original
MLIR SHA-256 identity, construction descriptor, selected ports, canonical public
values and context. Immutable descriptor and origin bytes are copied directly
from deployment data; the invocation encoding remains identical to native. The
verifier checks the header before execution, then decodes each frame only at its
reached receive operation. It
requires proof EOF before publishing either Boolean result. A source stop
precedes a malformed frame that execution never reaches.

Keccak transcript transitions preserve primitive input bytes, results and order,
including final delivery observations with no later state reader. Emission uses
an opaque one-input `POP` sink where solc could otherwise delete a required
hash. Validation compares the actual deployed artifact's complete primitive
trace, not its textual Yul or a static opcode count.

## Outcomes and capacity

A successful call returns the canonical ABI Boolean. False is a completed
verification decision. Reverts have a four-byte class followed by one 32-byte
code:

| Class | Bytes | Meaning |
|---|---|---|
| Source stop | `ZKCS` | Reached protocol or numerical failure |
| Decode refusal | `ZKCD` | Invalid ABI, public wire, proof header or reached frame |
| Target fault | `ZKCT` | Violated target ownership or internal representation contract |
| Resource refusal | `ZKCR` | Exceeded an immutable deployment ceiling |

EVM out-of-gas is a machine halt, separate from these structured outcomes. EVM
gas does not implement native VM instruction fuel.

The compiler fixes ceilings in each deployment. The supported maxima are 10
rounds, 1,024 vector elements, 65,536 bytes per frame and proof, 131,072 public
wire bytes, 4,096 context bytes, 262,144 calldata and binding-root bytes,
2,097,152 memory bytes and 64 transcript transitions. Compiler callers may
lower supported ceilings, never raise them. Finite local ranges retain the
native bound of 1,048,576; coordinate sequences have at most 64 elements and
origin templates fit a 4,096-byte workspace. Callers cannot supply per-call
budgets through the verifier ABI. The practical validation gas ceiling is
20 million; it does not override Cancun gas rules.

## Artifact and tool ownership

`zkc compile --target=evm` selects the same source proof Entry as native
compilation. The SDK's `evm` feature provides this target without a CPU runtime
or EVM engine dependency. Compilation requires an explicit installed solc path
and independent executable SHA-256 pin; no download or PATH substitution occurs.
The target pins solc `0.8.38+commit.1835d247` and Cancun. Exact standard-JSON
settings are retained in `solc-input.json`.

A `zkc.evm-artifact/0` directory contains:

| File | Content |
|---|---|
| `source.json` | Exact compiler response, checked source identities, descriptor and ceilings |
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
and solc identity checks still run. Deployment initcode and runtime obey EIP-3860
and EIP-170 size limits.

Publication stages a complete sibling directory and atomically renames it
without replacement. Existing destinations refuse. The current atomic directory
publisher requires Linux; unsupported platforms refuse explicitly.

See the [Sumcheck project](../../../examples/projects/sumcheck-keccak/README.md)
for commands and the [deployed validation adapter](../../../common/tests/evm/README.md)
for execution, mutation and trace controls. These tests establish bounded
agreement for their subjects, not a general target refinement theorem.
