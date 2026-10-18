# GKR

The [Entry](main.zkc) applies the [GKR library](../../../libraries/gkr/README.md)
over BLS12-381 Fr with at most four layers of at most `2^4` gates. `Proof`
selects the installed Merlin construction; `Interactive` retains the original
exchange.

The inputs describe a circuit of two layers of two gates on inputs `3, 5`:

| Layer | Gate 0 | Gate 1 |
|---|---|---|
| 1 | `3 + 5 = 8` | `3 * 5 = 15` |
| 0 (outputs) | `8 * 15 = 120` | `15 + 15 = 30` |

Its stacked wiring tables have one selector bit: block 0 holds the output
layer's `add` and `mul` tables over `(z, x, y)`, block 1 those of layer 1.

From the repository root, with built tools on `PATH`:

```sh
zkc prove --project=examples/projects/gkr/zkc.toml
zkc verify --project=examples/projects/gkr/zkc.toml
```

Both read the public inputs from the selected Entry's input directory; there is
no witness. Use `zkc run` from this project to execute `example::Interactive`
with both participant maps.

The [protocol tests](../../../common/tests/protocol/test_gkr.py) build their
statements with an independent circuit reference. They accept a padded
three-layer circuit with unwired gates and a nonzero unused selector block, and
reject a wrong output, a nonzero claim at an unwired output gate, a changed
proof message, and a prover that evaluates the circuit on different inputs with
the same outputs, which passes every layer check and fails V's final input
evaluation. These are bounded implementation controls.
