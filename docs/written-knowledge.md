# Written Schnorr knowledge

The command `zkc-knowledge` exports the written knowledge clause of a selected scheme to a Lean module. The example entry is `Proof` in [schnorr_example.zkc](../examples/schnorr_example.zkc). Its [protocol module](../examples/schnorr.zkc) supplies all three inputs to the proof.

```text
spec for Schnorr:
    knowledge DLog(base, point) by response_difference
```

`DLog` is a source relation with two public group elements and one scalar witness. Its body tests `point == base * scalar`. The source function `response_difference` takes the public statement and two leaves of `Schnorr<G>::Runs<2>`. It guards the challenge difference against zero and divides the difference of the responses by that difference. `SpecialSoundness` is a Lean library definition parameterized by an acceptance predicate, a relation and the successful return of an extractor.

## Generate and check

From the repository root, run

```sh
(cd lean/compiler && lake -q exe zkc-knowledge ../../examples/schnorr_example.zkc ../.. Proof) > /tmp/WrittenSchnorr.lean
(cd lean/formal && lake -q lean /tmp/WrittenSchnorr.lean)
```

The first command selects the source instance and emits Lean. The second elaborates the exported declarations and checks their proofs. The module lists the file and span of the clause, relation, extractor and three named sites in `WrittenKnowledge.sourceLocations`.

Pass `--target-only` before the input path to emit the same admitted program, executable relation, extractor and `WrittenKnowledge.obligation`. The module also exports the checked decision and its equivalence to a returning run. Authors can place that file in a Lean package that depends on `zkc_formal` and import it from a companion. The type of `obligation` specifies the goal even when the supplied proof strategy fails. Applying `of_obligation` to a companion proof transfers it to the actual admission result. A failed built-in proof reports `WK-PROOF` with source locations.

## What the theorem says

Fix the selected verifier role, a public statement, a call path and a commitment. Suppose the emitted verifier returns once for `(challenge₁, response₁)` and once for `(challenge₂, response₂)`, with distinct challenges. Then the selected extractor returns `some w` and the selected relation on that same statement and `w` returns `some true`. The statement quantifies over the replies to the verifier. An adversary may supply either response.

`certified_admitted` gives this result for an entry of the typed program actually returned by Core admission. `admitted_exists` proves that admission succeeds on the exported package. The theorem assumes a Core model, interpretations of the verifier's three group rows, and elementary scalar and group-action laws. These laws describe subtraction, cancellation, scaling and inversion of a nonzero scalar. The conclusion is an interactive, two-transcript extraction result. Probabilities, a model of the production curve, and security after Fiat–Shamir require additional theorems.

## How the proof is constructed

1. The frontend resolves the protocol instance and the declaration IDs after `knowledge` and `by`. It checks the deployed types, the public operands in their written order and the two-leaf run type at that instance. Named event occurrences from the typed body identify the commitment, challenge and response instructions. A local binder may be renamed under a stable `#[site(name)]`.
2. The exporter prints the stored program and the typed body from the source emission. Lean checks the typed body's erasure against the stored program, proves admission succeeds and identifies the result using Core's readback theorem. Parsing, name resolution and lowering the source to these terms are trusted frontend operations.
3. The formal library defines a returning transcript over the actual role process. Each exchange retains the operation, occurrence and typed reply. A replay uses common rules for local computation, a reply, the final guard and return. Lean checks each proposed intermediate value and proves that this process returns exactly when the decision read from its Core operands succeeds.
4. Lean's `Std.WP.vcgen` classifies both outcomes of that decision. For Schnorr, acceptance gives one group equation per transcript. The reusable `extract_difference` lemma cancels the common commitment and uses the nonzero challenge gap. A second `vcgen` pass on the source extractor checks its explicit guard and division domain, and proves the returned witness satisfies the written relation.

The transcript and special-soundness definitions do not depend on Schnorr. The acceptance rules concern Core operations. The group equations and deterministic algebra are the inputs specific to this proof strategy. The current exporter covers straight-line two-role, three-message forks at the G1/scalar specialization, two public group inputs, one private scalar, one terminal verifier guard and one written knowledge clause. Extending the supported source bodies or transcript shape requires extending the exporter. A new Lean property can reuse these formal definitions; selecting arbitrary third-party properties from source needs a further source interface.

## Reproduce the evidence

Run `just test-written-knowledge`. It generates the theorem from the repository example and checks its axiom dependencies. It also elaborates returning branches in a concrete two-element field and group model, shows that their replies are permitted, and computes the recovered witness. The same fork supplies counterexamples after replacing the selected extractor by zero or negating the relation. A third counterexample supplies a bad response to a weakened verifier. Other controls swap the public operands, rename a binder under a stable site, edit an unrelated simulator and exercise source diagnostics. The two-element model demonstrates an inhabited instance. The main proof quantifies over every model satisfying its hypotheses.

The common property and algebra are in [Extraction.lean](../lean/formal/Zkc/Formal/Written/Extraction.lean), the process rules in [Steps.lean](../lean/formal/Zkc/Formal/Written/Steps.lean), and the source-to-theorem connection in [Export.lean](../lean/compiler/Zkc/Frontend/Written/Export.lean).
