# Formal

Run `just test-interactive` from the repository root to check the emitted Sumcheck verifier and the GKR layer application. The source controls exercise zero, one and ten Sumcheck rounds, the four-coordinate GKR reduction, and changes to the evaluator, residual, guard and lexical specification arguments. The command compares both client implementations and replays the interactive formal library and its mathematical controls with the compiler's kernel audit.

Run `just test-written-knowledge` for the source-issued Schnorr and Chaum–Pedersen theorem over the admitted verifier, extractor and relation, the permitted forks, the mutation counterexamples and kernel replay of both generated modules and their project import closures. The interactive audit also covers the common process judgments and world observations. The [written knowledge guide](../../docs/written-knowledge.md) describes the generic Lean property, the generated target and the model assumptions.

## Package and model

Run `lake build` and `lake test` from this directory to build the public formal library and its controls, then replay and audit them. The compiler package has its own dependency graph. This package pins Mathlib and VCVio in its Lake configuration and manifest. Local proof replay uses the built Lean and pinned library modules, traverses proof dependencies for axioms, and accepts `propext`, `Quot.sound`, and `Classical.choice`. The compiler audit uses its original two-axiom policy.

The arithmetic interpretation supplies a field, an additive commutative group and its scalar action. Its nonzero scalar carrier includes a proof that the decoded value is nonzero. Its total model of the vocabulary assigns defaults to other rows. A consumer relies only on the row equations it proves for its operations. The characteristic-five example exercises the literals and operations used by the fork. A nonzero source literal divisible by five cannot preserve both its scalar residue and nonzero validity in this model. The refined literal has a valid fallback value in that case. A faithful interpretation of all source literals requires a compatible characteristic. The formal process comparison transfers predicates on supported executions across two interpretations when the operations match and every allowed concrete reply has a corresponding abstract reply.

The [historical package](../historical-formal/README.md) preserves the arithmetic construction, concrete curve premises, cross-model proofs and receipt checks for the earlier Core API.
