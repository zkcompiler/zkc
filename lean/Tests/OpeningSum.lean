import Zkc.Protocols.OpeningSum

/-! Control-flow and binding checks for the generic opening consumer.
The arithmetic test provider is not a cryptographic commitment scheme.
-/

namespace Tests.OpeningSum
open Zkc.Protocols.OpeningSum

def testCheck : Check Nat Nat Unit := fun commitment point opening =>
  decide (opening.value = commitment + point)

def subject : Statement Nat Nat := ⟨10, 2, 7, 29⟩

def run (left right : Nat) :=
  (program.denote (meaning testCheck) (environment subject)).run
    (replay (⟨left, ()⟩ : Opening Nat Unit) ⟨right, ()⟩) 0

example : run 12 17 = ⟨.returned true, 2, [(10, 2), (10, 7)]⟩ := by rfl

/-- Failing the first opening exposes no second request. -/
example : run 13 17 = ⟨.stopped .reject, 1, [(10, 2)]⟩ := by rfl

example : run 12 18 = ⟨.stopped .reject, 2, [(10, 2), (10, 7)]⟩ := by rfl

/-- Swapping responses cannot pass at distinct points despite preserving the sum. -/
example : (run 17 12).outcome = .stopped .reject := by rfl

example :
    (program.denote (meaning testCheck) (environment {subject with claim := 30})).run
      (replay (⟨12, ()⟩ : Opening Nat Unit) ⟨17, ()⟩) 0 =
        ⟨.returned false, 2, [(10, 2), (10, 7)]⟩ := by rfl

#print axioms Zkc.Protocols.OpeningSum.program_denote
#print axioms Zkc.Protocols.OpeningSum.accepted_false_implies_bad
end Tests.OpeningSum
