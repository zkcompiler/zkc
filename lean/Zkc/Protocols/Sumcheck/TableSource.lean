import Zkc.Polynomial.TableExpression
import Zkc.Protocols.Sumcheck.Optimization

/-! Actual ordered table inputs to the checked degree-two Sumcheck verifier.

The source statement precedes coefficient compilation. Success connects every
field-point evaluation and the complete run to that statement. Unsupported
factor arity refuses before any prover interaction or coin consumption. The
probability result uses the existing independent uniform finite-field tape.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.TableSource

open PIR Zkc.Polynomial Zkc.Probability
open AlgebraicRounds (Message)
open TableExpression (Expression inputTables)

variable {F J S : Type} {n : Nat}

section Execution
variable [CommRing F] [DecidableEq F]

def run (values : J → Fin (2 ^ n) → F) (source : Expression F J)
    (send : S → Message F × S) (react : S → F → S)
    (claim : F) (prover : S) (coins : List F) :
    PIR.Execution (S × List F) (AlgebraicRounds.Construction.Event F) Bool :=
  match TableExpression.compile (inputTables values) source with
  | none => ⟨.stopped .refused, (prover, coins), []⟩
  | some p => Optimization.run send react p claim prover coins

theorem run_compiled (values : J → Fin (2 ^ n) → F) (source : Expression F J)
    (p : Quadratic F n) (accepted : TableExpression.compile (inputTables values) source = some p)
    (send : S → Message F × S) (react : S → F → S)
    (claim : F) (prover : S) (coins : List F) :
    run values source send react claim prover coins = Optimization.run send react p claim prover coins := by
  simp only [run, accepted]

/-- Complete outcome, state and event-prefix equality, including short tapes. -/
theorem run_exact (values : J → Fin (2 ^ n) → F) (source : Expression F J)
    (p : Quadratic F n) (accepted : TableExpression.compile (inputTables values) source = some p)
    (send : S → Message F × S) (react : S → F → S)
    (claim : F) (prover : S) (coins : List F) :
    run values source send react claim prover coins = Execution.run send react p claim prover coins := by
  rw [run_compiled values source p accepted, Optimization.run_exact]

theorem refused (values : J → Fin (2 ^ n) → F) (source : Expression F J)
    (unsupported : TableExpression.compile (inputTables values) source = none)
    (send : S → Message F × S) (react : S → F → S)
    (claim : F) (prover : S) (coins : List F) :
    run values source send react claim prover coins = ⟨.stopped .refused, (prover, coins), []⟩ := by
  simp only [run, unsupported]

theorem accepted_iff (values : J → Fin (2 ^ n) → F) (source : Expression F J)
    (p : Quadratic F n) (accepted : TableExpression.compile (inputTables values) source = some p)
    (send : S → Message F × S) (react : S → F → S)
    (claim : F) (prover : S) (coins : AdaptiveTape.Tape F n) :
    (run values source send react claim prover (tapeList n coins)).outcome = .returned true ↔
      finalClaim (Execution.strategy send react n prover) claim coins =
        some (TableExpression.eval (inputTables values) (tapePoint n coins) source) := by
  rw [run_exact values source p accepted, Execution.accepted_iff, verify_iff_final,
    TableExpression.compile_eval (inputTables values) source p accepted]

end Execution

section Probability
variable [Field F] [Fintype F] [DecidableEq F]

def acceptance (values : J → Fin (2 ^ n) → F) (source : Expression F J)
    (send : S → Message F × S) (react : S → F → S) (claim : F) (prover : S) : ℚ :=
  UniformTape.average n (fun coins =>
    if (run values source send react claim prover (tapeList n coins)).outcome = .returned true
      then 1 else 0)

theorem acceptance_exact (values : J → Fin (2 ^ n) → F) (source : Expression F J)
    (p : Quadratic F n) (accepted : TableExpression.compile (inputTables values) source = some p)
    (send : S → Message F × S) (react : S → F → S) (claim : F) (prover : S) :
    acceptance values source send react claim prover = Optimization.acceptance send react p claim prover := by
  simp only [acceptance, Optimization.acceptance, run_compiled values source p accepted]

/-- The false-statement premise refers to the source tables and occurrences. -/
theorem soundness (values : J → Fin (2 ^ n) → F) (source : Expression F J)
    (p : Quadratic F n) (accepted : TableExpression.compile (inputTables values) source = some p)
    (send : S → Message F × S) (react : S → F → S) (claim : F) (prover : S)
    (falseClaim : claim ≠ TableExpression.sum (inputTables values) source) :
    acceptance values source send react claim prover ≤ (2 * (n : ℚ)) / Fintype.card F := by
  rw [acceptance_exact values source p accepted]
  apply Optimization.soundness
  rwa [TableExpression.compile_sum (inputTables values) source p accepted]

theorem perfect_completeness (values : J → Fin (2 ^ n) → F) (source : Expression F J)
    (p : Quadratic F n) (accepted : TableExpression.compile (inputTables values) source = some p) :
    acceptance values source Security.honestSend Security.honestReact
      (TableExpression.sum (inputTables values) source) ⟨n, p⟩ = 1 := by
  rw [acceptance_exact values source p accepted,
    ← TableExpression.compile_sum (inputTables values) source p accepted]
  exact Optimization.perfect_completeness p

end Probability
end Zkc.Protocols.Sumcheck.TableSource
