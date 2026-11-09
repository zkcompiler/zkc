module

public import ProtocolProof.Semantics.Access
public import PolyFun.PFunctor.Free.WP.Charge

/-! The Process resource meaning agrees exactly with the existing upstream charge fold. -/

public section
open PIR PFunctor

namespace ProtocolProof.Internal

private theorem iSup_outcome_zero {A : Type} (cost : A → ENNReal) :
    (⨆ outcome : Outcome A, match outcome with
      | .returned value => cost value
      | .stopped _ => 0) = ⨆ value, cost value := by
  apply le_antisymm
  · apply iSup_le
    intro outcome
    cases outcome with
    | returned value => exact le_iSup cost value
    | stopped _ => exact zero_le
  · apply iSup_le
    intro value
    exact le_iSup_of_le (.returned value) le_rfl

/-- Stop-aware encoding preserves the fixed worst-case weighted abstract-call meaning. -/
theorem bound_eq_charge {I : Signature} {A : Type} (cost : OperationCost I)
    (program : Process I A) :
    cost.bound program =
      FreeM.wpFold (OpSpec.charge (P := effects I) cost.weight) (encode program) (fun _ ↦ 0) := by
  induction program with
  | done _ => rfl
  | halt _ => rfl
  | call operation next ih =>
      simp only [OperationCost.bound, encode, FreeM.wpFold_liftBind, OpSpec.charge_apply]
      congr 1
      rw [← iSup_outcome_zero (fun value ↦ cost.bound (next value))]
      congr 1
      funext outcome
      cases outcome with
      | returned value => exact ih value
      | stopped _ => rfl

end ProtocolProof.Internal
