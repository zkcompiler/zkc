# Schnorr source project

[main.zkc](main.zkc) imports the generic [Schnorr library](../../libraries/schnorr/lib.zkc)
and chooses BLS12-381 G1 and the installed Merlin transcript suite. `Proof` is
noninteractive; `Interactive` uses the same protocol with actual messages and
managed random services. No application-specific executor is involved.

The [walkthrough](../../../docs/getting-started.md) runs `Proof`. To select a joint
interactive run from the repository root, with built tools on `PATH`:

```sh
zkc compile --module=schnorr=examples/libraries/schnorr/lib.zkc \
  --module=example=examples/projects/schnorr/main.zkc \
  --entry=example::Interactive --output=schnorr.entry
zkc run schnorr.entry EXPECTED_SHA256 examples/projects/schnorr/interactive.json \
  --results=results.json
```

Use the `package_sha256` from trusted compilation for `EXPECTED_SHA256`. The
returned `V.accepted` is the verifier's decision; a completed run can return false.
The inputs use the public demonstration witness 3. Group and scalar strings
include the complete canonical native wire frame.

The relation and target retain the statement/witness association for analysis.
They add no implicit guard or knowledge theorem. The executed verifier equation,
source comparison, native admission and separate proof acceptance are distinct
checks. Native Lean correspondence and a security theorem for this executable
construction remain separate work.
