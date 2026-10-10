# Schnorr source project

[main.zkc](main.zkc) imports the generic [Schnorr library](../../../libraries/schnorr/lib.zkc)
and chooses BLS12-381 G1 and the installed Merlin transcript suite. `Proof` is
noninteractive; `Interactive` uses the same protocol with actual messages and
managed random services. No application-specific executor is involved.

The [walkthrough](../../../docs/getting-started.md) runs `Proof`. To select a joint
interactive run from the repository root, with built tools on `PATH`:

```sh
zkc run example::Interactive --project=examples/projects/schnorr/zkc.toml \
  --session=schnorr \
  --input=P=examples/projects/schnorr/inputs/example.Interactive/P.json \
  --input=V=examples/projects/schnorr/inputs/example.Interactive/V.json \
  --results=results.json
```

The returned `V.accepted` is the verifier's decision; a completed run can return false.
The inputs use the public demonstration witness 3. Scalars are decimal strings; group values contain canonical element bytes.

The relation and target retain the statement/witness association for analysis.
They add no implicit guard or knowledge theorem. The executed verifier equation,
source comparison, native admission and separate proof acceptance are distinct
checks. Native Lean correspondence and a security theorem for this executable
construction remain separate work.
