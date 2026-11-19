import Zkc.Tests.Formal.Schnorr
import Zkc.Tests.Formal.Sumcheck
import Zkc.Tools.Formal.Receipt

/-! The receipts of the statements at packages.

Each receipt is read from its theorem (`statement_of%`), names the texts that its subject was
read from, and lists the executable checks of the hypotheses that the theorem leaves open. The
tool `zkc-formal-receipts` prints them as JSON, with the digest of each text and the result of
each check.
-/

set_option autoImplicit false

namespace Zkc.Formal

open Zkc.Core Zkc.Core.Concrete

/-- Multiples of multiples of the generator are of the group: the executable check of
`Vocabulary.GroupClosedUnderMultiples` at those points. -/
def multiplesInGroup : Bool :=
  [1, 7, Bls12381.order - 2].all fun first =>
    [0, 2, 5, Bls12381.order - 1, Bls12381.order + 3].all fun second =>
      Vocabulary.inGroup (scalePoint (scalePoint generator first) second)

/-- Completeness of the scheme `Proof = Schnorr<G1>` in the model that runs. -/
def schnorrComplete : Receipt where
  subject := "the scheme `Proof = Schnorr<G1>` of the program `schnorr_example`"
  texts := ["schnorr-frontend-scheme.json", "schnorr-frontend-scheme.declaration.json"]
  proved := statement_of% Schnorr.complete
  checks := [
    ⟨"Zkc.Formal.Bls12381.CurveLaws",
      "the three laws at the multiples 1, 7 and order - 2 of the generator, at every pair of eight scalars on both sides of the order",
      fun _ => Schnorr.curveLawsHold⟩,
    ⟨"Zkc.Core.Vocabulary.GroupClosedUnderMultiples",
      "five multiples, on both sides of the order, of the multiples 1, 7 and order - 2 of the generator",
      fun _ => multiplesInGroup⟩]

/-- Ten rounds of the protocol `Reduce` of `Sumcheck<Fr, 10>` keep the claim, in the model of
any arithmetic. -/
def sumcheckRounds : Receipt where
  subject := "the protocol `Reduce` of `Sumcheck<Fr, 10>` of the program `sumcheck_example`"
  texts := ["sumcheck-ten-rounds.json"]
  proved := statement_of% Sumcheck.reduce_keeps
  checks := []

/-- The receipts, with the texts of each in the order of its list. -/
def receipts : List Receipt := [schnorrComplete, sumcheckRounds]

/-! ## Checks of the receipts -/

-- What the statement of Schnorr leaves open is read from the theorem: its three hypotheses
-- about the curve, by their names, and no other.
#guard schnorrComplete.proved.hypotheses ==
  ["Zkc.Core.Vocabulary.GroupClosedUnderMultiples", "Zkc.Formal.Bls12381.CurveLaws",
    "Zkc.Core.Vocabulary.PointCompression"]

-- Its condition on the values it ranges over is that the base is a point of the group.
#guard schnorrComplete.proved.conditions == ["Zkc.Core.Vocabulary.inGroup base.toPoint = Bool.true"]

#guard schnorrComplete.proved.ranges ==
  ["base : Zkc.Core.Concrete.Datum", "witness : Zkc.Core.Concrete.Datum"]

-- Every check of a hypothesis is of a hypothesis that the theorem takes.
#guard schnorrComplete.checks.all fun check =>
  schnorrComplete.proved.hypotheses.contains check.hypothesis

-- The statement of the rounds of Sumcheck takes no hypothesis: it is of every arithmetic.
#guard sumcheckRounds.proved.hypotheses == []

#guard receipts.all fun receipt =>
  receipt.proved.axioms.all fun used => ["propext", "Classical.choice", "Quot.sound"].contains used

namespace ReceiptControl

open Lean Elab Command in
/-- Elaborate commands and keep nothing of them: the control below needs a proposition without
a proof, and no module of the package may store an axiom. -/
elab "#discarded " commands:command+ : command =>
  withoutModifyingEnv do
    for command in commands do
      elabCommand command

-- A theorem whose proof uses another axiom has no statement, so no receipt is made of it.
/--
error: the proof of `Zkc.Formal.ReceiptControl.fromAxiom` uses the axiom `Zkc.Formal.ReceiptControl.unproved`
-/
#guard_msgs in
#discarded
  axiom unproved : 1 = 2
  theorem fromAxiom : 1 = 2 := unproved
  example : Statement := statement_of% fromAxiom

end ReceiptControl

end Zkc.Formal
