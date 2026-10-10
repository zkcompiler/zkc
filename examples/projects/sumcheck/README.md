# Public-table Sumcheck

The [library](../../../libraries/sumcheck/lib.zkc) implements repeated multilinear
Sumcheck using ordinary vector kernels, messages and bounded protocol repetition.
The [Entry](main.zkc) selects BLS12-381 Fr, at most two rounds, and the installed
Merlin construction. `Interactive` retains the original exchange.

The public vector contains `[1, 2, 3, 4]`, and the claimed sum is 10. Each round
sends the sums of the two halves. V checks their sum against its current claim,
draws a challenge, and updates the claim. P folds its table with the delivered
challenge. V separately folds its own public table, then checks that exactly one
entry remains and equals the final claim. Table halves define the variable order;
this example uses the contiguous-half convention.

This is a public polynomial example. V evaluates its public table directly;
there is no commitment, hidden terminal evaluator or zero-knowledge claim. It
exercises a complete terminal decision without requiring a PCS setup.

From the repository root, with built tools on `PATH`:

```sh
zkc prove --project=examples/projects/sumcheck/zkc.toml
zkc verify --project=examples/projects/sumcheck/zkc.toml
```

Both invocations read the public table, claim and round count from the selected
Entry's input directory. This public
example needs no witness file. The [Entry guide](../../../docs/runtime/entries.md)
explains input encodings and limits. Use `zkc run` from this project to select
`example::Interactive`, read both participant maps and run with a fresh session.

The source and CLI tests check both successful execution and changed claims,
insufficient rounds, actual transcript messages and proof truncation. These are
bounded implementation controls, not an executable-path soundness theorem.
