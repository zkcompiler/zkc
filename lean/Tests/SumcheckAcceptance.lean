import Zkc.Protocols.Sumcheck.Acceptance
import Mathlib.Data.ZMod.Basic

namespace Tests.SumcheckAcceptance

open Zkc.Polynomial Zkc.Protocols.Sumcheck

def polynomial : Quadratic (ZMod 5) 1 :=
  .node (.constant 1) (.constant 2) (.constant 0)

def input (r : ZMod 5) := Acceptance.honestInput polynomial (r, ())

theorem every_field_challenge (r : ZMod 5) :
    Acceptance.check Security.honestSend Security.honestReact (input r) = true :=
  Acceptance.honest_complete polynomial (r, ())

/-- At r = 2 the residual is zero in Z/5Z; it is not an opening of the original
two-entry Boolean table. Direct polynomial evaluation covers the full field. -/
theorem non_boolean_residual :
    Acceptance.constraints Security.honestSend Security.honestReact (input 2) () 0 := by
  unfold Acceptance.constraints
  decide +kernel

theorem wrong_original_object_rejected :
    let wrong := { input 2 with polynomial := Quadratic.node (.constant 2) (.constant 0) (.constant 0) }
    Acceptance.check Security.honestSend Security.honestReact wrong = false := by
  decide +kernel

/-- Retaining the round result while changing its query point is invalid. -/
theorem wrong_point_rejected :
    ¬ Acceptance.constraints Security.honestSend Security.honestReact (input 3) () 0 := by
  unfold Acceptance.constraints
  decide +kernel

theorem wrong_residual_rejected :
    ¬ Acceptance.constraints Security.honestSend Security.honestReact (input 2) () 1 := by
  unfold Acceptance.constraints
  decide +kernel

/-- Per-input adequacy remains true even for a false claim that happens to
pass at a chosen challenge. Existentially closing that challenge changes the
outer statement; it cannot replace the interactive experiment's challenge law. -/
theorem existential_challenge_does_not_prove_sum :
    let zero : Quadratic (ZMod 7) 1 := .node (.constant 0) (.constant 0) (.constant 0)
    let cheating := Strategy.send (Zkc.Protocols.AlgebraicRounds.Message.mk 0 1 0)
      (fun _ => Strategy.done)
    (∃ r : ZMod 7, verify zero 1 cheating (r, ()) = true) ∧ zero.booleanSum ≠ 1 := by
  dsimp
  constructor
  · exact ⟨0, by decide +kernel⟩
  · decide +kernel

end Tests.SumcheckAcceptance
