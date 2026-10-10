import Zkc.Protocols.Sumcheck.Committed.Execution

/-! The committed terminal implies the maintained direct-source acceptance
on the same adaptive round strategy and the same tape, except on an actual
false accepted opening. No PCS correctness premise is hidden in the runner.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Committed

open Zkc.Polynomial Zkc.Probability
open AdaptiveTape (Tape)

variable {F S : Type} {n : Nat} {scheme : Scheme F n}
variable [CommRing F] [DecidableEq F]

theorem Terminal.accepts_iff (terminal : Terminal scheme) (statement : Statement scheme) :
    terminal.accepts statement = true ↔
      ∃ right, terminal.right = some right ∧
        leftCheck statement terminal.query terminal.left = true ∧
        rightCheck statement terminal.query right = true ∧
        terminal.query.claim = terminal.left.value * right.value := by
  cases result : terminal.right <;> simp [Terminal.accepts, result]

theorem Terminal.accepted_correct_value (terminal : Terminal scheme) (statement : Statement scheme)
    (accepted : terminal.accepts statement = true) (correct : terminal.correctOpenings statement) :
    terminal.query.claim = statement.polynomial.eval terminal.query.point := by
  obtain ⟨right, reached, _, _, product⟩ := (terminal.accepts_iff statement).mp accepted
  rw [product, correct.1, correct.2 right reached, Statement.polynomial_eval]

theorem Terminal.accepted_not_bad_correct (terminal : Terminal scheme) (statement : Statement scheme)
    (accepted : terminal.accepts statement = true) (notBad : ¬ terminal.badOpening statement) :
    terminal.correctOpenings statement := by
  obtain ⟨right, reached, leftPass, rightPass, _⟩ := (terminal.accepts_iff statement).mp accepted
  constructor
  · by_contra wrong
    exact notBad ⟨leftPass, Or.inl wrong⟩
  · intro other found
    have same : other = right := Option.some.inj (found.symm.trans reached)
    subst other
    by_contra wrong
    exact notBad ⟨leftPass, Or.inr ⟨right, reached, rightPass, wrong⟩⟩

/-- The deterministic connection uses the actual reached point and claim
derived from Source.rounds. The polynomial is the fixed product of extensions. -/
theorem accepted_correct_source (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) (coins : Tape F n)
    (accepted : Accepted statement adversary claim prover coins)
    (correct : CorrectReachedOpenings statement adversary claim prover coins) :
    (Execution.run adversary.send adversary.react statement.polynomial claim prover
      (tapeList n coins)).outcome = .returned true := by
  obtain ⟨terminal, reached, passed⟩ := accepted
  obtain ⟨point, residual⟩ := reached_query statement adversary claim prover coins terminal reached
  have value := terminal.accepted_correct_value statement passed (correct terminal reached)
  rw [point] at value
  rw [Execution.accepted_iff, verify_iff_final, residual, value]

/-- A pointwise event inclusion, stronger than the probability bound. Bad
opening means a checked false value, independently of terminal product equality. -/
theorem accepted_source_or_bad (statement : Statement scheme) (adversary : Adversary scheme S)
    (claim : F) (prover : S) (coins : Tape F n)
    (accepted : Accepted statement adversary claim prover coins) :
    (Execution.run adversary.send adversary.react statement.polynomial claim prover
      (tapeList n coins)).outcome = .returned true ∨
    BadOpening statement adversary claim prover coins := by
  classical
  by_cases bad : BadOpening statement adversary claim prover coins
  · exact Or.inr bad
  · apply Or.inl
    apply accepted_correct_source statement adversary claim prover coins accepted
    obtain ⟨terminal, reached, passed⟩ := accepted
    intro other found
    have same : other = terminal := Option.some.inj (found.symm.trans reached)
    subst other
    exact terminal.accepted_not_bad_correct statement passed (fun wrong => bad ⟨terminal, reached, wrong⟩)

end Zkc.Protocols.Sumcheck.Committed
