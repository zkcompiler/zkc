# Artifact host fixtures

`dleq.json` and `committed-two-factor.json` are explicit protocol sources. Their
matching `.construction.json` files select the tested construction policies.
Tests retain port bindings, operation order, sites and hostile-admission controls;
compiler outputs are regenerated through the configured compiler.

Generate development keys and invocation inputs from the repository root:

```sh
cargo run --locked --release -p zkc-tools --example artifact_fixture -- OUTPUT_DIR
```

The [unbound DLEQ fixture](unbound-dleq/README.md) exercises missing statement
binding. Its proof is a rejection control, not an accepted artifact.
