# Compiled relation consumers

`composition.pir` loads two rank-one relations and one AIR. It invokes three
ordinary subprotocols and returns their residual vectors. The first rank-one
view uses immutable matrix inputs checked against content digests; the second
specializes its coefficients into local code. The AIR view evaluates finite
first-row and transition constraints. These are diagnostic arithmetic consumers,
not three cryptographic proof protocols.

From the repository root after `just build`:

```sh
build/compiler/zkc-compile protocol-resolve examples/relations/composition.pir > /tmp/relations.json
build/compiler/zkc-compile protocol-materialize /tmp/relations.json > /tmp/relations-source.json
build/compiler/zkc-compile protocol-compile /tmp/relations-source.json > /tmp/relations-plan.json
uv run --no-sync --locked pytest -q tests/protocol/test_relation_authoring.py
```

The check runs the actual native endpoints and the independent Lean interpreter
with two compatible relation contents, genuine subprotocol calls, changed public
values/witnesses/traces, missing inputs and same-shape crossed matrix data.
It compares arithmetic with explicit integer expectations. Resolved contents
survive removal of the original dependency file.

For a complete cryptographic consumer, see
[`groth16.pir`](../protocols/groth16.pir) and its
[fixture generator](../../tests/groth16/README.md). That source's `circuit.r1cs`
dependency is supplied explicitly by the `groth16-artifact` host; the verifier
can reuse checked compiler output without loading that R1CS or proving key.
