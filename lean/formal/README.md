# Formal

Run `just test-interactive` from the repository root to check the emitted Sumcheck verifier and the GKR layer application. The source controls exercise zero, one and ten Sumcheck rounds, the four-coordinate GKR reduction, and changes to the evaluator, residual, guard and lexical specification arguments. The command compares both client implementations and replays the interactive formal library and its mathematical controls with the compiler's kernel audit.

The receipt suite documented below uses the Core interfaces and fixtures from
[the previous Lean compiler at `10ed903fc`](https://github.com/zkcompiler/zkc/tree/10ed903fc22d3f20b22ff2d1bbf607a740ef0718). Run its commands at that revision.
See [status](../../docs/status.md).

## Historical receipt suite

Statements about admitted programs, over the meaning that Core gives them, and their proofs.
The package requires the package `zkc_compiler` (`../compiler`) and nothing else: its library
imports only the core, and its tests import checks of the core's tests and read the core's
fixtures; nothing requires it.

A statement about a protocol is proved in two parts that this package keeps apart.

1. **The mathematics**, in the model of an arithmetic. `Zkc.Formal.Arithmetic` is a
   commutative ring of scalars with a module of points over it. `provider A binding`
   (`Zkc.Formal.Abstract.Provider`) is a model in Core's sense: the carrier of a nominal type
   of a package is the scalars or the points of `A`, and a row is the operation of the
   arithmetic that the binding names. A proof in this model uses the laws of the arithmetic
   and holds for every arithmetic.
2. **The relation to the model that runs.** `Zkc.Formal.Relation` relates two models of one
   program. `program_related` is the relation theorem: when a relation of the carriers is
   respected by the rows that a program uses, the two meanings of every function and of every
   protocol, for every side, are related: they perform the same effects at the same sites with
   related values, stop alike, and return related values. `everyRun_related` carries a
   statement about every run from the first model to the second. The theorem is stated for
   the operations that a decidable test of the program accepts (`Program.relatable`); it
   covers a row, a call, `if`, a guard, a literal of a type that Core fixes, `at`, `exchange`,
   `draw`, `sample` and `apply`, and not yet `match`, a loop, an operation that Core owns, a
   literal of a nominal type, `repeat`, `choose` and a function without a body.

`Zkc.Formal.Bls12381` is the arithmetic that runs: the residues modulo the order of the scalar
field and the points of the group G1, as the model of the vocabulary computes them on data.
`bindingOf` reads the binding of a package from the names of its rows, so no author writes
one. `respected` proves, once per row of the vocabulary and for every package, that a row that
fits respects the relation; at a package the kernel evaluates which rows fit. The laws of the
curve are not proved here: they are the named hypotheses `Vocabulary.GroupClosedUnderMultiples`
(of Core) and `Bls12381.CurveLaws`, with an executable check.

`Zkc.Formal.Steps` proves a statement that every run of a region returns along the region,
one operation at a time: an operation that returns is passed by an equation for it, and a draw
or a sample by a statement for every reply. A call is passed by a law of the callee, stated
for the table of functions, so the body of the callee is not read again where it is called.
`evaluate_bound` (`Zkc.Tools.Formal.Evaluate`) keeps the environment of a long body a list of
values.

A receipt (`Zkc.Formal.Receipt`) is what a theorem about a subject states, as data: its
conclusion, the values it ranges over and the conditions on them; the hypotheses it takes and
the axioms its proof uses; and the executable checks of those hypotheses, each with what was
evaluated and whether it held. `statement_of%` (`Zkc.Tools.Formal.Receipt`) reads the statement
from the theorem and refuses a theorem whose proof uses an axiom other than Lean's three.
`lake exe zkc-formal-receipts` prints the receipts of the statements below as JSON, with the
digest of each text that a subject was read from; `lake test` runs it and fails when a check
does not hold.

The statements at packages are in `Zkc.Tests.Formal`, beside Core's statements at the same
packages. `Zkc.Tests.Formal.Schnorr` proves completeness of the scheme `Proof = Schnorr<G1>`
that the frontend emits for the worked program `schnorr_example`, in the model that runs: for
every base that is a point of the group and every scalar, the constructed prover's program
returns a proof and the constructed verifier's program returns on it. What its author writes
is the equation of the verifier's check in an arithmetic and the statement; the binding, the
rows that fit and the test of the relation theorem are evaluated by the kernel.

`Zkc.Tests.Formal.Sumcheck` is about a package of `Sumcheck<Fr, 10>`, whose loop is written out
as ten rounds: the package that an earlier state of the frontend emitted for the worked program
`sumcheck_example`; the present frontend emits a different one. It links the package with its
body in pieces of one round, proves the laws of the library functions `sums`, `low`, `high`
and `fix_first` from their bodies at the ten sizes, one statement per function, proves the
statement of a round at its piece with the laws of the functions it calls as hypotheses, and
composes the ten: in the model of any arithmetic, when the claims are the sum of the table,
the verifier's ten checks pass. It does not reach the instructions after the tenth round or
the model that runs.

The historical receipt suite used `lake build`, `lake test` and `lake exe zkc-formal-audit`. Its old frontend and Core imports await migration on this branch. The historical audit
(`Zkc.Tools.Audit` of the compiler's package) checks that a module of `Zkc.Formal` imports only
modules of the core and of the formal library, besides Lean's prelude; and, for every declaration
of `Zkc.Formal` and of its tests `Zkc.Tests.Formal`, its axioms, `@[extern]` and
`@[implemented_by]`, and that the kernel accepts it when it is replayed from the built files,
together with every module that it imports outside Lean's libraries (of the core, of the tests of
the core and of the tools), on an environment that takes only Lean's libraries as built.

## Interactive security

The Core process runs against a stateful service with finite, possibly incomplete reply mass. A rejected path or a missing reply contributes zero acceptance mass. The source clients recover the actual function and protocol members from the emitted, admitted program. At the reduction site they compare the lexical arguments in the checked source event and the emitted attachment. The Sumcheck joint client requires the external symbol `Zkc.Polynomial.extension` applied to the caller's table input. The GKR source client requires `Zkc.Circuit.summand` applied to the expected circuit, inputs, layer and point. A change to the external declaration alone invalidates the source association while preserving the standalone execution result. These checks identify the source binding. Its mathematical interpretation and the connection to a written `proves` clause require further evidence.

`TableVerifier.Certified.soundValid` takes the Core validity of the flat input table and a false claim about its list sum. Its cube form `Certified.soundFrom` bounds the probability of accepting an incorrect Boolean-cube sum by the number of rounds divided by the challenge-set size. It checks the boundary guard, the caller's table evaluator and the returned point in order. Its challenge law bounds each reached post-message draw by the uniform law on a nonempty set of distinct field points. The peer may depend on its history. Project scalar and vector interpretations are explicit parameters.

`SourceCompleteness.Certificate.everyValid` covers the joint program on a correctly summed table of the declared length. It follows the honest prover's messages and restrictions through the same terminal evaluator. `Certificate.probability_one` requires full reply mass at reached service calls. The source checks include changed private messages and restrictions.

`ReductionRound.AtSite.gate_soundFrom` applies the same reduction theorem at GKR's emitted `Reduce` call inside the layer loop. Its four degree-two rounds bound the probability of a correction by eight divided by the challenge-set size, conditional on the gate and current-layer interpretations. The bound evaluates the selected role instruction with supplied operands and service state. Lifting it to a run of the enclosing GKR verifier requires a proof connecting a reached loop environment to those operands and to the continuation. An end-to-end GKR or Fiat–Shamir theorem requires further composition.

Run `just test-interactive` from the repository root. The audit replays the interactive library and its mathematical controls and permits `propext` and `Quot.sound`. The source association clients run separately in the source checks. Their lookups in frontend state also depend on `Classical.choice`.
