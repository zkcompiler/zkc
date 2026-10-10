import Tests.Sumcheck
import Zkc.Protocols.Sumcheck.Optimization

/-! The whole verifier consumes a checked arithmetic plan. -/

set_option autoImplicit false

namespace Tests.SumcheckOptimization

open PIR Zkc.Source Zkc.Compiler Zkc.Protocols.Sumcheck Tests.Sumcheck

example : Optimization.evaluate falseMessage (2 : F) = .returned 0 := by decide

example : (Optimization.run dishonestSend react zeroPolynomial 1 () [2]).outcome = .returned true := by decide
example : (Optimization.run dishonestSend react zeroPolynomial 1 () [0]).outcome = .returned false := by decide
example : (Optimization.run dishonestSend react zeroPolynomial 1 () []).outcome = .stopped .exhausted := by decide
example : (Optimization.run wrongBoundary react zeroPolynomial 1 () [2, 3]).state.2 = [2, 3] := by decide
example : (Optimization.run Security.honestSend Security.honestReact
    squarePolynomial squarePolynomial.booleanSum ⟨2, squarePolynomial⟩ [2, 4]).outcome =
      .returned true := by decide

example : Optimization.acceptance dishonestSend react zeroPolynomial 1 () = (2 : ℚ) / 7 := by
  rw [Optimization.acceptance_exact]
  exact tight_soundness_example

/-- This candidate multiplies by the saved coefficient instead of the challenge. -/
def wrong : RawProgram Arithmetic.Ty Arithmetic.Op :=
  .letOp .multiply [2, 3] (.letOp .add [2, 0]
    (.letOp .multiply [0, 4] (.letOp .add [3, 0] (.ret 0))))

example : (checkTransformation
    (Arithmetic.Horner.rule (fun x : F => .done x) Optimization.noHandler
      Optimization.arguments .scalar) Optimization.evaluationSource () wrong).isSome = false := by rfl

/-- A previously checked candidate is not admitted for a changed child source. -/
example : (checkTransformation
    (Arithmetic.Horner.rule (fun x : F => .done x) Optimization.noHandler
      Optimization.arguments .scalar) (.ret .here) () Optimization.candidate).isSome = false := by rfl

end Tests.SumcheckOptimization
