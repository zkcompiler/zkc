# Accumulator-machine proof

This example proves a small machine execution using the ordinary source
STARK/FRI libraries. The [external adapter](../../../compiler/adapters/accumulator-machine/README.md)
defines a five-instruction machine, executes it, and supplies a relation Bundle
with a CPU table, a configured program table and optional memory table. The
frontend binds that Bundle's derived relation interface; VM instructions do
not become compiler cases.

`Run` exposes the interactive LogUp protocol. `ProofLogUp` and `ProofProduct`
apply the same Fiat–Shamir construction to LogUp and grand-product reductions
respectively. Both use the [three-table library profile](../../../libraries/air/README.md#whole-bundle-argument):
base-field trace commitment, extension-field auxiliary and quotient commitments,
OOD checks, DEEP composition and a shared FRI instance. The compiler sees
native vector maps and imported record expressions throughout.

## Run

From the repository root, with the compiler and CLI already built:

```sh
python3 examples/projects/accumulator-machine/prepare.py \
  compiler/adapters/accumulator-machine/fixtures/store-load/run.json \
  build/machine-requests

zkc compile --compiler=build/compiler/zkc-compile \
  --module=accumulator_machine=examples/projects/accumulator-machine/main.zkc \
  --module=air_bundle=libraries/air/bundle.zkc \
  --module=air_interaction=libraries/air/interaction.zkc \
  --module=air_stark=libraries/air/stark.zkc \
  --module=air_table=libraries/air/table.zkc \
  --module=air_polynomial=libraries/air/polynomial.zkc \
  --module=fri=libraries/fri/lib.zkc \
  --asset=machine=relation-bundle-json=compiler/adapters/accumulator-machine/fixtures/bundle.json \
  --entry=accumulator_machine::ProofLogUp --output=build/machine.entry

zkc prove build/machine.entry PACKAGE_SHA256 \
  build/machine-requests/prover.json build/machine.proof
zkc verify build/machine.entry PACKAGE_SHA256 \
  build/machine-requests/verifier.json build/machine.proof
```

Use the `package_sha256` printed by compilation in place of `PACKAGE_SHA256`.
Choose `ProofProduct` at compilation for the other reduction. The request
format is the same. The maintained tests run these commands with isolated tools
and reports. `prepare.py --memory-clocks 16 --memory-present` exercises a longer,
present memory schedule, including a run with no memory instruction.

## Statement and evidence

The verifier binds initial/final accumulator values, table presence and
heights, program instructions, memory schedule, coset shift and profile counts.
The CPU state, program usage counts and memory cell columns are prover inputs.
The target relation requires table assertions, Boolean interaction counts and
both program and memory multiset equalities. A proof Entry's target label states
that intended relation; it does not certify the security of its protocol.

The example admits at most 32 rows per table, uses a 64-point coset, eight
queries, eight OOD attempts and two interaction channels. These are execution
test parameters, not a production security selection. Commitments are nonhiding.
It demonstrates a complete selected machine proof path; the machine is not an
Ethereum ISA or the deployed OpenVM. Relation comparison with upstream VM
components is a separate adapter boundary.
