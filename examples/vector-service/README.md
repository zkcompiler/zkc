# Adaptive vector requests

The first request asks for three entries. Seed two produces `[2,2,2]`, whose
sum determines the second request's length: six. Seed four produces six fours;
the final send consumes seed five and returns false successfully. The program
returns the second vector. Its final state is `[3,[6]]`, with events
`[["request",3],["request",6],["send",6]]`.

From the repository root, after building `compiler/` with tests enabled:

```sh
cargo build --release --example vector-service
(cd formal && lake build vector-service)
build/compiler/examples/service/zkc-service-compile compile \
  examples/vector-service/source.json > /tmp/vector-plan.json
target/release/examples/vector-service examples/vector-service/source.json \
  /tmp/vector-plan.json examples/vector-service/inputs.json \
  formal/.lake/build/bin/vector-service
formal/.lake/build/bin/vector-service run examples/vector-service/source.json \
  /tmp/vector-plan.json examples/vector-service/inputs.json
```

Both tools report the complete result, state and events. The
[library guide](../../docs/compiler/libraries.md) explains the interface and
its limits. This deterministic example tests dependent replies and consumer
installation; it is not a cryptographic protocol.
