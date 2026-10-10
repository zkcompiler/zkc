import Tests.Sumcheck
import Zkc.Protocols.Sumcheck.Optimization

/-! Review follow-ups: an adaptive dishonest callback and characteristic two. -/

set_option autoImplicit false

namespace Tests.SumcheckAdversary

open PIR Zkc.Polynomial Zkc.Protocols.Sumcheck Tests.Sumcheck
open Zkc.Protocols.AlgebraicRounds (Message)

abbrev ProverState := Nat × F

def message (claim : F) : Message F := ⟨6 * claim, 2 * claim, claim⟩
def send (state : ProverState) : Message F × ProverState := (message state.2, state)
def react (state : ProverState) (r : F) : ProverState := (state.1 + 1, (message state.2).evaluate r)
def statement : Quadratic F 2 := .node zeroPolynomial zeroPolynomial zeroPolynomial

/-- The second message depends on the actual first challenge. -/
example : (Execution.run send react statement 1 (0, 1) [0, 2]).outcome = .returned true := by decide
example : (Execution.run send react statement 1 (0, 1) [0, 2]).state = ((2, 0), []) := by decide
example : (Execution.run send react statement 1 (0, 1) [0, 2]).events =
    [.message ⟨6, 2, 1⟩, .challenge 0, .message ⟨1, 5, 6⟩, .challenge 2] := by decide
example : (Optimization.run send react statement 1 (0, 1) [0, 2]).events =
    [.message ⟨6, 2, 1⟩, .challenge 0, .message ⟨1, 5, 6⟩, .challenge 2] := by decide
example : (Optimization.run send react statement 1 (0, 1) [0, 2]).state = ((2, 0), []) := by decide
example : (Optimization.run send react statement 1 (0, 1) [0, 0]).outcome = .returned false := by decide
example : (Optimization.run send react statement 1 (0, 1) [2, 0]).events =
    [.message ⟨6, 2, 1⟩, .challenge 2, .message ⟨0, 0, 0⟩, .challenge 0] := by decide

namespace Binary

abbrev F := ZMod 2
def polynomial : Quadratic F 1 := .node (.constant 0) (.constant 0) (.constant 0)
def nonzeroMessage : Message F := ⟨0, 1, 1⟩
def send (_ : Unit) : Message F × Unit := (nonzeroMessage, ())
def react (_ : Unit) (_ : F) : Unit := ()

/-- Coefficient inequality alone is not the soundness proof's root premise. -/
example : nonzeroMessage ≠ (⟨0, 0, 0⟩ : Message F) := by decide
example : nonzeroMessage.evaluate 0 = 0 ∧ nonzeroMessage.evaluate 1 = 0 := by decide
example : nonzeroMessage.boundary = polynomial.booleanSum := by decide
example : (Execution.run send react polynomial 0 () [1]).outcome = .returned true := by decide
example : (Execution.run send react polynomial 1 () [1]).outcome = .stopped .reject := by decide
example : (Execution.run send react polynomial 1 () [1]).state.2 = [1] := by decide

end Binary
end Tests.SumcheckAdversary
