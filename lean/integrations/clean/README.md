# Clean finite AIR adapter

This isolated optional package retains the useful Clean-to-native relation
boundary while protocol verification evolves separately. It pins Clean and
shared dependencies in its owning manifests. From this directory, `lake build`
checks all adapter and control modules, including their transitive axioms.

`ZkcClean.Flatten` proves its executable flattening equals upstream operation
flattening. `Export` refuses lookups, channel interactions and out-of-range
variables. `Expression`, `Relation` and `Specification` prove that admitted
exports preserve expressions, constraints and the selected component
specification under its actual assumptions. `Native` connects the finite AIR
model to native ring expressions. This is not a cryptographic AIR soundness theorem.

`TestsClean.Control` emits `common/tests/fixtures/clean/air-control.json` at the
repository root. `just test-lean-clean` compares that producer byte-for-byte
with the maintained fixture. The native suite then checks fixed honest, invalid
and mutated rows independently. Lookup refusal includes an upstream nested
addition circuit. Channel refusal is universal over the public operation type;
it avoids importing an unrelated upstream VM proof that fails on the selected
Mathlib. [Dependency rationale](../../docs/dependencies.md) records that boundary.

The native decoders, KoalaBear/extension providers and compiler are not proved
correct by these finite comparisons. Formal [support](../../docs/support.md)
states the retained claims.
