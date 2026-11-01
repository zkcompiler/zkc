# Sumcheck with a Keccak transcript

This project uses the maintained Sumcheck library over BLS12-381's scalar field,
with at most ten rounds. The same explicit proof declaration supports native
proof production and compilation of its verifier to EVM. It includes the terminal
multilinear evaluation against the public table; it is not only a round-message
checker. The separate [Sumcheck project](../sumcheck/) retains its Merlin
construction and formal claims. Those claims do not transfer to this deployment.

Prepare and fill the ordinary public inputs before proving:

```sh
zkc prepare Proof --project=examples/projects/sumcheck-keccak/zkc.toml
zkc prove Proof --project=examples/projects/sumcheck-keccak/zkc.toml
```

The public table has a power-of-two length, `rounds` is its base-two logarithm,
and `claim` is its sum in the selected field. For example, the sixteen elements
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
native proof. Its target is Cancun. See the [EVM contract](../../../docs/spec/targets/evm.md)
for limits and failure behavior, and the [deployed checks](../../../common/tests/evm/README.md)
for the independent native/EVM comparison.
