# Formal

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

`Zkc.Tests.Formal.Sumcheck` is about the package that the frontend emits for
`Sumcheck<Fr, 10>`, whose loop is written out as ten rounds. It links the package with its
body in pieces of one round, proves the laws of the library functions `sums`, `low`, `high`
and `fix_first` from their bodies at the ten sizes, one statement per function, proves the
statement of a round at its piece with the laws of the functions it calls as hypotheses, and
composes the ten: in the model of any arithmetic, when the claims are the sum of the table,
the verifier's ten checks pass. It does not reach the instructions after the tenth round or
the model that runs.

Run `lake build`, `lake test` and `lake exe zkc-formal-audit` from this directory. The audit
(`Zkc.Tools.Audit` of the compiler's package) checks that a module of `Zkc.Formal` imports only
modules of the core and of the formal library, besides Lean's prelude, and the axioms,
`@[extern]` and `@[implemented_by]` of its declarations.
