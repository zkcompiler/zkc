# BLS12-381 G1 Schnorr with Keccak

This ordinary project imports the generic `schnorr::Schnorr` library and selects
`bls12-381.g1` and the installed
`hash-chain.keccak256.bls12-381.fr64be/0` managed suite explicitly. Public `base`
and `point` remain arbitrary subgroup points; the compiler does not recognize
this protocol or replace its verification equation. The demonstration inputs
use the standard generator and the public witness 3, copied from the existing
Schnorr example. They are not secret or a production security profile.

With built native tools on `PATH`, run from this directory:

```sh
zkc check
zkc prove Proof
zkc verify Proof
```

Compile the verifier with the [declared Solidity release](../../../docs/spec/targets/evm.md#target-declaration)
and its independently obtained executable SHA-256:

```sh
zkc compile Proof --target=evm --solc=/absolute/path/to/solc \
  --solc-sha256=EXPECTED_BINARY_SHA256
```

Retain the reported artifact manifest pin independently. The SDK authenticates
that artifact with `evm::Artifact::capture` and prepares
`verify(bytes[],bytes,bytes)` calldata with `Artifact::calldata`: public frames in
descriptor order, application context, and the unchanged native proof. See the
[EVM contract](../../../docs/spec/targets/evm.md) for deployment and failure rules.

The generated native framed proof is the intended input to this EVM
compiler/SDK path. That target profile requires Prague or Osaka and strict
native compressed G1 frames (48-byte payloads), with canonical 32-byte
little-endian Fr frames. The internal EIP-2537 representation is separate:
128-byte padded affine points and big-endian 32-byte scalars. The target adds
no nonidentity guard; base-order/randomness premises of a Schnorr security
argument remain separate from an equation result.

The maintained [`curve_closure.py` consumer check](../../../common/tests/evm/README.md#ordinary-bls-g1-schnorr-consumer)
compiles this exact source and its library, produces and verifies real native
proofs, and checks the same proof bytes twice per deployed Prague/Osaka
contract. It covers varied bases/secrets, identity/sign cases, false equations,
malformed proofs, exact outcomes and complete managed hash frontiers, retaining
artifact identities, gas and memory measurements. A passive physical observer
also checks the complete source-derived ModExp/ADD/MSM input/output sequence,
statuses and hash frontiers on both calls, including empty-return subgroup
failure and identity admission. The all-finite case has 15 physical calls and
12 hashes. Diagnostic mutations must fail that oracle with the same Boolean.
Run it with prepared tools
from the repository root; it does not run the CLI commands above or authenticate
an SDK-captured artifact. Proofs may be reused with fresh native verification
through the documented `--retained-native` option. This is bounded primitive
correspondence evidence; complete call-ABI tracing, gas theorems, formal
correspondence and Schnorr security remain separate. G2, pairing and other curve adapters
remain unsupported by this EVM addition.
