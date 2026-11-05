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
compiler of the release the
[target declaration](../../../docs/spec/targets/evm.md#target-declaration)
names:

```sh
zkc compile Proof --project=examples/projects/sumcheck-keccak/zkc.toml \
  --target=evm --solc=/absolute/path/to/solc --solc-sha256=EXPECTED_BINARY_SHA256
```

The fresh output directory contains Yul, ABI, creation and runtime bytecode,
exact compiler metadata/settings and a manifest. Retain the reported manifest
SHA-256 independently. The contract's `verify(bytes[],bytes,bytes)` arguments are
canonical public ZKCV frames in descriptor order, context bytes and the unchanged
native proof. `--evm-version` selects one of the declared forks; without it,
the declared default applies.

To restrict a deployment to sixteen public elements and sixteen transcript
transitions (the supplied four-round invocation), create a partial selection
and publish to a fresh directory:

```sh
printf '%s\n' '{"public_elements":16,"transcript_transitions":16}' > limits.json
zkc compile Proof --project=examples/projects/sumcheck-keccak/zkc.toml \
  --target=evm --evm-limits=limits.json --output=build/verifier-lower.evm \
  --solc=/absolute/path/to/solc --solc-sha256=EXPECTED_BINARY_SHA256 --json
```

Omitted ceilings use the installed declaration's maxima. Exact names and ranges
come from that declaration; unknown names, duplicate keys, noninteger and
out-of-range values refuse before compiler execution. The JSON report's
`evm_limits` and the artifact's `source.json` retain the complete effective
selection. These limits are fixed in the deployment and bound into its artifact
identity and reuse key. A lower transcript ceiling does not change native VM
fuel, native proving capacity or EVM gas.
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
