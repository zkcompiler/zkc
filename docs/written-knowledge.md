# Written knowledge for three-message group protocols

`zkc-knowledge` takes a scheme entry and generates a Lean module for its written knowledge clause. Two source programs exercise the same compiler and formal library.

| Scheme | Public statement | Shared first message | Written relation on the extracted scalar |
| --- | --- | --- | --- |
| `Proof` in [schnorr_example.zkc](../examples/schnorr_example.zkc) | base and point | one point | `point == base * scalar` |
| `SameLogProof` in [chaum_pedersen.zkc](../examples/chaum_pedersen.zkc) | `g, h, u, v` | two points sent as one tuple | `u == g * x and v == h * x` |

The Schnorr clause selects `DLog` and `response_difference`. The Chaum–Pedersen clause selects `SameLog` and `extract`. Each name resolves to an executable source declaration. The clauses, the relation operands, the extractors and the verifier guards all affect the generated result.

## Generate and check

From the repository root, run

```sh
(cd lean/compiler && lake -q exe zkc-knowledge ../../examples/schnorr_example.zkc ../.. Proof) > /tmp/WrittenSchnorr.lean
(cd lean/formal && lake -q lean /tmp/WrittenSchnorr.lean)
(cd lean/compiler && lake -q exe zkc-knowledge ../../examples/chaum_pedersen.zkc ../.. SameLogProof) > /tmp/WrittenSameLog.lean
(cd lean/formal && lake -q lean /tmp/WrittenSameLog.lean)
```

Pass `--target-only` before the input path to generate the admission facts, executable relation and extractor, verifier and proposition for a companion. `WrittenKnowledge.obligation` quantifies over a public statement, a shared commitment and two branches. If the actual projected verifier returns on both transcripts at the given call path, and their challenges differ, the selected extractor must return a witness that satisfies the selected relation. Each transcript contains the precise Core operation, its occurrence and its typed reply.

`replayCheck` executes the projected verifier against exactly those inputs. The process theorem `replay_iff` proves that a successful replay is equivalent to a complete returning trace, including consumption of every input. It needs no group laws. A companion can import the target, prove `obligation`, and use `of_obligation` to obtain `admittedObligation` for the actual admission result. The target-only module imports the source semantics. The optional built-in certificate also imports the group proof strategy and produces the same result as `certified_admitted`. The module also proves `admitted_exists` and records source spans in `sourceLocations`.

## How the shared proof works

1. **Source and admission.** The frontend resolves the scheme, relation and extractor. It checks their deployed types, binds public operands in the written order, and resolves the names of the three observed instructions. The emitter prints the stored program and its typed body. The kernel checks that erasure gives that stored program and that the independently run admission returns that body. A typed first message can carry a product, while a private prover port contributes no verifier input.
2. **Verifier equations.** A formal-library tactic reads the stored instructions, tracks visible values and tuple components and proposes the conjunction of all verifier guards. The singleton-root theorem connects the installed verifier to the projection of its typed body. The proof then uses rules for a pure step, an interaction with its typed reply, a guard followed by an arbitrary continuation, and return. Lean checks each proposed calculation against the actual projection. For Schnorr the resulting theorem exposes one equation. For Chaum–Pedersen it exposes both equations, in source order.
3. **One extracted witness.** For each pair of matching equations on the two branches, `extract_difference` cancels the shared commitment and divides by the nonzero challenge gap. In Chaum–Pedersen both equations use the same two challenges and responses, hence the same scalar. Lean's `Std.WP.vcgen` checks the selected extractor's guard and division and the returned scalar against the entire written relation. The proof constructor uses the equations and source declarations for each input program.

The target supports the exported straight-line, two-role, three-message G1/scalar fragment with a nonempty list of public group inputs, one private scalar witness, a group point or tuple of points as commitment and a scalar challenge and response. The automatic algebraic proof interprets the three verifier rows for group scaling, addition and equality, along with Core tuple operations. An unsupported row in the automatic strategy leaves the companion target available. `WK-PROOF` identifies residual proof failures by source location. Source parsing, resolution and translation are trusted compiler operations. The written theorem is conditional on the declared row interpretations and group-action laws. Production-curve instantiation, probabilities, zero knowledge and security after Fiat–Shamir are separate obligations.

## Evidence

Run `just test-written-knowledge`. It elaborates both source-issued certificates and audits their axioms. It also checks the same Chaum–Pedersen certificate after exchanging the order of the two guards. The finite two-element field and group provide concrete returning branches. Removing the second Chaum–Pedersen guard leaves the original relation and extractor intact. With public inputs `(1,1,1,0)`, commitment `(0,0)`, and challenge/response pairs `(0,0)` and `(1,1)`, the changed verifier returns on both permitted branches. No scalar satisfies both relation equations. The suite proves the negation of the claim for the admitted mutant, checks rejection by the original verifier, and exercises diagnostics and changes to the Schnorr relation, extractor and verifier.

The [source exporter](../lean/compiler/Zkc/Frontend/Written/Export.lean), [process semantics](../lean/formal/Zkc/Formal/Written/Execution.lean), [group verifier replay](../lean/formal/Zkc/Formal/Written/GroupReplay.lean), [step rules](../lean/formal/Zkc/Formal/Written/Steps.lean) and [extraction lemma](../lean/formal/Zkc/Formal/Written/Extraction.lean) implement these boundaries.
