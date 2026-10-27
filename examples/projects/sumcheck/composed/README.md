# Composed Sumcheck

[TwoSums](protocol.zkc) calls the library's `Reduce` twice and checks each
returned pending claim against its corresponding public table. This is ordinary
protocol composition; neither the compiler nor the runtime knows TwoSums.
[Entries](main.zkc) select a field and a construction separately.

From this directory, with built tools on `PATH`:

```sh
zkc prove
zkc verify
```

The single proof Entry uses the supplied public inputs. `Interactive` runs the
complete protocol. `Reduction` is a reusable protocol whose `variables` input
describes P's original table and whose `rounds` input may select a shorter
prefix. It returns P's ordinary residual data and V's sealed pending claim.
A parent must consume that claim in another reduction or a terminal; the
partial protocol is not an Entry result.

A reduction returns an obligation, not acceptance. `check` folds the verifier's
own table in MSB-first coordinate order and requires exactly one matching value.
Using the wrong table or leaving a nontrivial residual dimension cannot satisfy
this complete client. The example makes no hiding or security-theorem claim.

## Executable quick start

Run these literal commands from this project directory with `zkc` and
`zkc-compile` on `PATH` (Python 3 for generated inputs). The test suite runs
this block in a separate consumer tree using only declared package dependencies.

```sh zkc-example
zkc check
zkc prove Proof
zkc verify Proof
```

Inputs: inputs/example.Proof/public.json; there is no private table witness.

Profile: Two public tables are reduced separately, with each terminal evaluation checked.

Expected negative control: Changing one table or claim while retaining a proof refuses verification.

Generated packages, proofs and result documents are written under `build/`
inside this project. Existing input maps remain source inputs.
