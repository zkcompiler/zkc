# Schnorr source project

[main.zkc](main.zkc) imports the generic [Schnorr library](../../../libraries/protocols/sigma/schnorr/lib.zkc)
and chooses BLS12-381 G1 and the installed Merlin transcript suite. `Proof` is
noninteractive; `Interactive` uses the same protocol with actual messages and
managed random services. No application-specific executor is involved.

The [walkthrough](../../../docs/getting-started.md) runs `Proof`. To select a joint
interactive run from the repository root, with built tools on `PATH`:

```sh
zkc run --project=examples/projects/schnorr/zkc.toml
```

The command selects the unique run function, reads its named arguments and writes
`build/zkc/example.Interactive.results.json` beside the manifest. The returned
`V.accepted` is the verifier's decision; a completed run can return false.
The inputs use the public demonstration witness 3. Scalars are decimal strings; group values contain canonical element bytes.

The relation and target retain the statement/witness association for analysis.
They add no implicit guard or knowledge theorem. The executed verifier equation,
source comparison, native admission and separate proof acceptance are distinct
checks. Native Lean correspondence and a security theorem for this executable
construction remain separate work.

The [Spongefish variant](spongefish/README.md) uses the same generic protocol
with an application-selected transcript and raw external proof encoding.

## Executable quick start

Run these literal commands from this project directory with `zkc` and
`zkc-compile` on `PATH` (Python 3 for generated inputs). The test suite runs
this block in a separate consumer tree using only declared package dependencies.

```sh zkc-example
zkc check
zkc run Interactive
zkc prove Proof
zkc verify Proof
```

Inputs: inputs/example.Proof/{public,witness}.json and inputs/example.Interactive/arguments.json.

Profile: BLS12-381 G1; the demonstration witness is public knowledge.

Expected negative control: Changing the public point while retaining a proof refuses verification.

Generated packages, proofs and result documents are written under `build/`
inside this project. Existing input maps remain source inputs.
