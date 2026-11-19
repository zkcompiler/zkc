# Formal

Run `just test-interactive` from the repository root to check the emitted Sumcheck verifier and the GKR layer application. The source controls exercise zero, one and ten Sumcheck rounds, the four-coordinate GKR reduction, and changes to the evaluator, residual, guard and lexical specification arguments. The command compares both client implementations and replays the interactive formal library and its mathematical controls with the compiler's kernel audit.

Run `just test-written-knowledge` for the source-issued Schnorr and Chaum–Pedersen theorem over the admitted verifier, extractor and relation, the permitted forks, the mutation counterexamples and kernel replay of both generated modules, the helper-factored Schnorr companion and their project import closures. The interactive audit also covers the common process judgments and world observations. The [written knowledge guide](../../docs/written-knowledge.md) describes the generic Lean property, the generated target and the model assumptions.

For a selected admitted protocol and inputs, `admitted_replacement_reads` fixes world-read authority from the honest role projections before substituting a strategy. It covers the principal, owner or listeners, operation kind, occurrence, owner input signature and result type. A substitute owner can supply different values of the same input types. A service contract must separately establish any required payload predicate. The source control maps a private child coin to the caller's second role and rejects an attempt by the first role to listen. [Authority and reachability](Zkc/Formal/WorldObservation.lean) · [Source control](checks/WorldObservation.lean)

## Constructed Schnorr verifier

From `lean/formal`, run the source and service regression with the project toolchain
and Python 3.

```sh
lake lean checks/ConstructedSchnorr.lean
```

`ConstructedVerifier.acceptance` defines the probability that the selected constructed
verifier returns. Its parameters include the Core model, nominal encodings, residue
interpretation, identity provider, verifier inputs, initial cache, prover message policy
and distribution of a fresh 64-byte reply. A missing identity fails setup. A missing message
or a Core stop gives a nonaccepting outcome. VCVio's list cache keys replies by the entire
ordered transcript and squeeze label and retains the first binding. The prover policy
chooses the commitment and response and decides which query information its state retains.
The only online oracle query in this experiment is the verifier's squeeze. A security game
with an adversary's own query budget, oracle programming or extraction needs further
semantics and proofs. [Experiment](Zkc/Tools/Formal/ConstructedVerifier.lean)

The regression compiles the authored `Proof` scheme and its `derived_view` goal. It runs
the admitted guard in the executable characteristic-two model. Its two point encodings are
the compressed infinity and generator, and its scalar encodings are zero and one. One run
calls the repository's reference Merlin implementation on the actual emitted frames and
checks all 64 reply bytes against an independently generated schedule vector. Additional
controls change the source guard, suite binding, initial transcript, typed receive handler,
identity, public input, response and cache. The checked event is a verifier return under
the supplied service. The authored zero-knowledge goal still needs its simulator and proof.
[Regression](checks/ConstructedSchnorr.lean) · [Merlin adapter](checks/constructed_merlin.py)

## Package and model

Run `lake build` and `lake test` from this directory to build the public formal library and its controls, then replay and audit them. The compiler package has its own dependency graph. This package pins Mathlib and VCVio in its Lake configuration and manifest. Local proof replay uses the built Lean and pinned library modules, traverses proof dependencies for axioms, and accepts `propext`, `Quot.sound`, and `Classical.choice`. The compiler audit uses its original two-axiom policy.

The arithmetic interpretation supplies a field, an additive commutative group and its scalar action. Its nonzero scalar carrier includes a proof that the decoded value is nonzero. Its total model of the vocabulary assigns defaults to other rows. A consumer relies only on the row equations it proves for its operations. The characteristic-five example exercises the literals and operations used by the fork. A nonzero source literal divisible by five cannot preserve both its scalar residue and nonzero validity in this model. The refined literal has a valid fallback value in that case. A faithful interpretation of all source literals requires a compatible characteristic. The formal process comparison transfers predicates on supported executions across two interpretations when the operations match and every allowed concrete reply has a corresponding abstract reply.

For a repeated written charge, compile an assembly with `Written.admitSource` and pass its result to `chargeSumcheck` with the round count and source draw name. The resulting certificate exposes `primeBound` on the admitted root under the BLS12-381 scalar field interpretation. The service can update strategy state after every fresh uniform reply. The GKR component uses the same source lookup, address check and probability bridge at its selected layer call, with a certificate for the executed gate members and explicit model and polynomial hypotheses. Direct named draws accept closed rational arithmetic over literals and static size terms, including powers with an integer exponent. Applications and attempts need their own occurrence selection. The fixed-table check resolves the positions clause of the spot-check example with its extractor marked executable and separately proves the independent-sampling bound in VCVio. Issuing that bound on an admitted oracle verifier still requires oracle send and opening semantics. Run `just test-written-charge` for examples and mutation controls. [Source client](Zkc/Tools/Formal/DrawCharge.lean) · [Source checks](checks/WrittenCharge.lean)

### Source round proofs

The round reader follows the sent value and public challenge to the member operations in each admitted block. It checks the verifier projection, result binders and continuation. For a sequence of length `n`, the first member supplies its collision law at depth `n - 1`, and the last at zero. A depth is the number of rounds still to run after that member. Homogeneous pair and gate libraries can reuse one implementation across the sequence. [Round composition](Zkc/Formal/Interactive/RoundFamily.lean)

The [two-round Sumcheck example](../../examples/shifted_sumcheck.zkc) carries the first round's partial sum plus one. The next boundary consumes that representation. The issuer reads the intermediate representation from the selected boundary and proves the incoming and outgoing equations on the actual members. At both public endpoints the scalar represents the ordinary table value. The supported affine evaluator admits either order of the two multiplication operands under the pure field row equations. Table relation readback interprets either order of equality between the public claim and the identity sum over its table. `ChargedSumcheck.primeBoundOfRelation` bounds acceptance when the selected source equality fails. [Source members](../../examples/support/shifted_pairs.zkc) · [Table verifier](Zkc/Formal/Interactive/SourceSumcheck.lean)

For GKR, `chargeLayer` checks the homogeneous gate primitive. `chargeGateFamily` takes the expected primitive as a function of remaining depth. Each occurrence checks the actual row and signature in the selected callee. Its layer bound takes the primitive interpretation and honest quadratic equations at the depths that execute. Run `lake lean checks/SourceRoundLaws.lean` from this package for the two-round Sumcheck, exchanged source callees, expression and guard mutations, and four depth-specialized GKR primitives. [Source regression](checks/SourceRoundLaws.lean)


The independent consumers compile the original ten-round Sumcheck and four-coordinate GKR fixtures. They check verifier role 1 with the source field's uniform challenge. A false cube sum bounds the probability of a root return by `10 × (1 / Fr.order)`. Under the supplied gate evaluation, equality and quadratic laws, a false layer claim bounds the probability that the returned scalar agrees with the summand on the newly returned coordinates by `4 × (2 / Fr.order)`. The tests check the exact written fees and reject substituted propositions, events and same-typed subjects. The focused charge audit replays the issuance module and its project imports. [Independent consumers](checks/ChargeConsumers.lean) · [Kernel replay](checks/ReplayCharge.lean) · [Audit controls](checks/AuditCharge.lean)

### Named written Sumcheck soundness

`issueSumcheckGoal assembly "written_sound"` retains the successful admission of that assembly
and goal alongside the certificate on the admitted root.
In the Sumcheck example the request selects the written stage and a fixed statement in the
plain model. The selector reads the table dimension, deciding role, relation operands,
applied reduction and draw from source. For ten rounds its accumulated charge is
`10 / Fr::Order`. An explicit ceiling must cover that charge by exact rational comparison.
A request without a ceiling reports the accumulated charge. Constructed-stage and
random-oracle requests require a different theorem. [Written goal](../../examples/sumcheck_example.zkc)

`CertifiedSumcheckGoal.falseAcceptance` bounds the probability that the admitted verifier
returns on a public table and a claim different from its cube sum. The experiment uses the
BLS12-381 scalar field and fresh uniform challenges. The other replies and the strategy
state can depend on previous challenges. Run `lake lean checks/SumcheckGoal.lean` here for
the source requests, refusals and an independent consumer that supplies the verifier's input
ports and return event. [Issuer and theorem](Zkc/Tools/Formal/SumcheckGoal.lean) · [Consumer](checks/SumcheckGoal.lean)

The [historical package](../historical-formal/README.md) preserves the arithmetic construction, concrete curve premises, cross-model proofs and receipt checks for the earlier Core API.
