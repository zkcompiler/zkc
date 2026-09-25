# Stateful local endpoint

The prover sends `(2, 5)` and receives challenge `3`, returning to `ready` with
challenge `6` still available. This finite example demonstrates stateful phase
admission and private input ownership; it has no cryptographic security claim.

After [building the tools](../../compiler/README.md), from the repository root:

```sh
build/compiler/zkc-compile import examples/endpoint/source.json > /tmp/endpoint-source.mlir
build/compiler/zkc-opt /tmp/endpoint-source.mlir \
  --pass-pipeline='builtin.module(lower-pir-to-plan)' > /tmp/endpoint-plan.mlir
build/compiler/zkc-compile export /tmp/endpoint-plan.mlir > /tmp/endpoint-plan.json
target/release/zkc run examples/endpoint/source.json /tmp/endpoint-plan.json \
  examples/endpoint/inputs.json formal/.lake/build/bin/table-protocol \
  --endpoint table-endpoint/1 examples/endpoint/certificate.json
formal/.lake/build/bin/table-protocol run-entry examples/endpoint/source.json \
  /tmp/endpoint-plan.json examples/endpoint/inputs.json table-endpoint/1 \
  examples/endpoint/certificate.json examples/endpoint/entry.json
```

Both runs produce:

```json
{"status":"executed","outcome":["returned",3],"state":["prover","ready",[0,0,0,[[2,5]],[6]]],"events":[["sent",2,5],["drawn",3]]}
```

The native CLI obtains the requested entry from the actual supplied binding.
The reference runner separately checks the entry file against invocation state.
For an owned in-process endpoint, reusing `Completed` bindings preserves the
phase and provider. A stale admitted entry cannot bind; re-admit a source from
the retained phase instead. These files initialize a trusted local example;
editing/reloading a phase is not a verified persistence or recovery protocol.
