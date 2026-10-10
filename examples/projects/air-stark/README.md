# Imported AIR through STARK and FRI

This client proves the recurrence AIR exported by the
[Plonky3 adapter](../../../compiler/adapters/plonky3/README.md), using ordinary
[protocol libraries](../../../libraries/air/README.md). The relation, read
offsets, assertion scopes and degree facts come from the captured Bundle.
The prover input is the actual base-field trace; configuration and boundary
values are public. The verifier receives commitments, polynomial-opening claims
and authenticated rows. It does not receive the full trace.

The example selects eight trace rows, 32 evaluation points, eight queries and
eight out-of-domain sampling attempts. These are testing parameters, with no
production security claim. The construction is nonhiding and uses zkc's proof
format, independently of upstream proof formats.

From the repository root, with the built `zkc` and `zkc-compile` on `PATH`:

```sh
zkc compile --compiler=zkc-compile \
  --project=examples/projects/air-stark/zkc.toml \
  air_stark_example::Proof --output=air-stark.zkpkg
```

Prepare public and witness inputs from the retained upstream run, then prove
and verify using the `Package SHA-256` shown by compilation (`package_sha256` with `--json`):

```sh
python3 examples/projects/air-stark/prepare.py build/air-stark
zkc prove --package=air-stark.zkpkg --sha256="$PACKAGE_SHA256" \
  --public=build/air-stark/public.json --witness=build/air-stark/witness.json \
  --output=build/air-stark/proof.bin
zkc verify --package=air-stark.zkpkg --sha256="$PACKAGE_SHA256" \
  --public=build/air-stark/public.json --proof=build/air-stark/proof.bin
```

`Run` is the interactive Entry. `Proof` applies the installed Merlin transcript
suite to the same protocol. See the [proof Host](../../../docs/runtime/README.md)
for result files and execution limits. The
[executable tests](../../../tests/protocol/test_air_stark.py) exercise these
inputs, independent producer/consumer invocations and rejection cases.
Fixture values come from the adapter's direct AIR execution.

The example names a constraints target and restricts the Bundle to one table
and no interaction channels. Compiler construction checks do not certify its
cryptographic soundness; the library documentation records the remaining
mathematical and cryptographic obligations.
