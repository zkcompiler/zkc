# Interface consumer fixtures

`fri-interface.json` is actual compiler output from the maintained FRI project,
including its seven retained Protocols, Commit/Query state schemas, exact
placement/component maps and required common-input inventories. The producer
checks the independently parsed original and source correspondence before
publishing it. This is a native interface receipt, not FRI proof execution or
formal coverage. Private state fields remain private in the emitted schema.

[The interface fixture script](../../../../../../../scripts/regenerate-interface-fixtures.py)
regenerates it with `zkc-compile language-interface`, together with the other
compiler-produced interface fixtures, from a named compiler build, and
recomputes the digest table below:

```sh
python3 scripts/regenerate-interface-fixtures.py build/compiler
```

Its embedded original and compiler identities bind different inputs and are not
source proofs. The compiler identity records the producing build. The Rust
reader takes it as a fixture parameter: the consumer tests check the same
structure with a substituted identity, so a compiler edit that changes only
that identity needs no regeneration.

`recursive-interface.json` is an independently authored current-schema positive
specimen for shared reader integration. It has nested ordered role substitution,
two distinct holders, one receiver, an ordinary verifier-local child, and a
private zero-storage child. The Rust reader checks its exact component coordinates
and the mutation tests use the same schema. The C++ owner must pair it with an
admitted native candidate and run the independent reader; that integration is a
separate outstanding gate. Its nominal digest placeholders bind fixture names,
not an authenticated source declaration.

The recursive specimen explicitly retains `common_input_requirements: []`
for every Protocol. This establishes strict SDK schema consumption, not newly
derived source coverage or fresh compiler/native pairing.

## Current fixture SHA-256

These hashes cover the exact retained compiler output from the command above.
The authored recursive specimen is not compiler output and has no row.

| File | SHA-256 |
|---|---|
| `fri-interface.json` | `3aa34332ee4907be2661b1a0733dc53aa08821158c7d11a7a07353b11a77637e` |
