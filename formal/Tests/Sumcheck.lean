import Zkc.Protocols.Sumcheck.Security
import Mathlib.Algebra.Field.ZMod

/-! Source-bound tests, including a tight ordinary-soundness example. -/

set_option autoImplicit false

namespace Tests.Sumcheck

open PIR Zkc.Polynomial Zkc.Protocols.Sumcheck
open Zkc.Protocols.AlgebraicRounds (Message)

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev F := ZMod 7

def zeroPolynomial : Quadratic F 1 := .node (.constant 0) (.constant 0) (.constant 0)

/-- `(r-2)(r-3)` over `ZMod 7` has boundary sum 1 and exactly two roots. -/
def falseMessage : Message F := ⟨6, 2, 1⟩
def dishonestSend (_ : Unit) : Message F × Unit := (falseMessage, ())
def react (_ : Unit) (_ : F) : Unit := ()

example : falseMessage.boundary = 1 := by decide
example : zeroPolynomial.booleanSum = 0 := by decide
theorem tight_soundness_example : Security.sourceAcceptance dishonestSend react zeroPolynomial 1 () = (2 : ℚ) / 7 := by
  simp only [Security.sourceAcceptance, Zkc.Probability.UniformTape.average]
  change (∑ r : F, (if (Execution.run dishonestSend react zeroPolynomial 1 () [r]).outcome =
    .returned true then (1 : ℚ) else 0)) / 7 = 2 / 7
  rw [show (Finset.univ : Finset F) = {0, 1, 2, 3, 4, 5, 6} by decide]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  simp (disch := decide) only [if_pos, if_neg]
  norm_num
example : (Execution.run dishonestSend react zeroPolynomial 1 () [2]).outcome = .returned true := by decide
example : (Execution.run dishonestSend react zeroPolynomial 1 () [3]).outcome = .returned true := by decide
example : (Execution.run dishonestSend react zeroPolynomial 1 () [0]).outcome = .returned false := by decide

/-- Honest completeness includes nonzero square terms in both coordinates. -/
def squarePolynomial : Quadratic F 2 :=
  .node (.node (.constant 1) (.constant 0) (.constant 2))
    (.node (.constant 3) (.constant 4) (.constant 0))
    (.node (.constant 5) (.constant 0) (.constant 6))

example : (Execution.run Security.honestSend Security.honestReact
    squarePolynomial squarePolynomial.booleanSum ⟨2, squarePolynomial⟩ [2, 4]).outcome =
      .returned true := by decide

/-- A failed message check consumes no challenge, and preserves the visible prefix. -/
def wrongBoundary (_ : Unit) : Message F × Unit := (⟨0, 0, 0⟩, ())
example : (Execution.run wrongBoundary react zeroPolynomial 1 () [2, 3]).outcome = .stopped .reject := by decide
example : (Execution.run wrongBoundary react zeroPolynomial 1 () [2, 3]).state.2 = [2, 3] := by decide
example : (Execution.run wrongBoundary react zeroPolynomial 1 () [2, 3]).events =
    [.message ⟨0, 0, 0⟩, .reject] := by decide

/-- No terminal acceptance is manufactured when the provider runs out of coins. -/
example : (Execution.run dishonestSend react zeroPolynomial 1 () []).outcome = .stopped .exhausted := by decide
example : (Execution.run dishonestSend react zeroPolynomial 1 () []).events = [.message falseMessage] := by decide

/-- Extra provider coins remain unconsumed; terminal coordinates are the actual draws. -/
example : (Execution.run dishonestSend react zeroPolynomial 1 () [2, 6]).state.2 = [6] := by decide

/-- A forged terminal point cannot exploit the total coordinate lookup's fallback. -/
example : Source.terminal zeroPolynomial ⟨0, []⟩ = false := by decide
example : Source.terminal zeroPolynomial ⟨0, [1, 2]⟩ = false := by decide

/-- Zero rounds still check the actual constant statement. -/
example : (Execution.run dishonestSend react (.constant (3 : F)) 4 () []).outcome = .returned false := by decide
example : (Execution.run dishonestSend react (.constant (3 : F)) 3 () []).outcome = .returned true := by decide

end Tests.Sumcheck
