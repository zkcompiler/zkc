# Sumcheck with a Keccak transcript

This project uses the maintained Sumcheck library over BLS12-381's scalar field,
with at most ten rounds. The same explicit proof declaration supports native
proof production and compilation of its verifier to EVM. It includes the terminal
multilinear evaluation against the public table; it is not only a round-message
checker. The separate [Sumcheck project](../sumcheck/) retains its Merlin
construction and formal claims. Those claims do not transfer to this deployment.

The supplied public input map is ready for native proving and verification:

```sh
zkc prove Proof --project=examples/projects/sumcheck-keccak/zkc.toml
zkc verify Proof --project=examples/projects/sumcheck-keccak/zkc.toml
```

The public table has a power-of-two length, `rounds` is its base-two logarithm,
and `claim` is its sum in the selected field. The supplied sixteen elements
1 through 16 use four rounds and claim 136. Use 1,024 elements for ten rounds.

Compile the EVM verifier using an explicitly installed and pinned Solidity
0.8.38 compiler:

```sh
zkc compile Proof --project=examples/projects/sumcheck-keccak/zkc.toml \
  --target=evm --solc=/absolute/path/to/solc --solc-sha256=EXPECTED_BINARY_SHA256
```

The fresh output directory contains Yul, ABI, creation and runtime bytecode,
exact compiler metadata/settings and a manifest. Retain the reported manifest
SHA-256 independently. The contract's `verify(bytes[],bytes,bytes)` arguments are
canonical public ZKCV frames in descriptor order, context bytes and the unchanged
native proof. Cancun is the default; use `--evm-version=prague` to select Prague.
See the [EVM contract](../../../docs/spec/targets/evm.md)
for limits and failure behavior, and the [deployed checks](../../../common/tests/evm/README.md)
for the independent native/EVM comparison.

## Executable quick start

Run these literal commands from this project directory with `zkc` and
`zkc-compile` on `PATH`. The test suite runs this block in a separate consumer
tree using only declared package dependencies.

```sh zkc-example
zkc check
zkc prove Proof
zkc verify Proof
```

Inputs: inputs/example.Proof/public.json; this public-table example has no
private witness. Generated packages and proofs are written under `build/`.

Profile: Four rounds over the supplied public table, with the complete terminal
evaluation and the selected Keccak transcript. The native quick start needs no
Solidity compiler; the EVM compilation command above selects its tool explicitly.
