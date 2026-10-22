import ZkcSecurity.Claims.ChargeMonotonicity
import ZkcSecurity.Claims.Soundness

/-! Small kernel controls isolate both monotonicity directions. A budget at
smaller validator prices cannot certify a request with larger prices. -/

set_option autoImplicit false
namespace TestsSecurity.ClaimChargeControls
open OracleComp OracleSpec ZkcSecurity.FiatShamir ZkcSecurity.Claims

private abbrev spec := Unit →ₒ Unit
private def prover : OracleComp spec Unit := spec.query () >>= fun _ => pure ()

private theorem budget (price : ENNReal) : WorstCaseCostBound prover ⟨fun _ => price⟩ price := by
  rw [prover, worstCaseCostBound_query_bind_iff]
  intro reply result member
  have same : result = ((), Multiplicative.ofAdd (0 : ENNReal)) := by
    simpa [costDist, instrumentedRun] using member
  subst result
  simp

example : WorstCaseCostBound prover ⟨fun _ => (1 : ENNReal)⟩ 2 :=
  worstCaseCostBound_mono_charge _ _ (fun _ => by norm_num) prover 2 (budget 2)

example : ¬ WorstCaseCostBound prover ⟨fun _ => (2 : ENNReal)⟩ 1 := by
  intro bounded
  rw [prover, worstCaseCostBound_query_bind_iff] at bounded
  have impossible := bounded () ((), Multiplicative.ofAdd (0 : ENNReal)) (by simp [costDist, instrumentedRun])
  norm_num at impossible

private abbrev signature : PIR.Signature := ⟨Unit, fun _ => Unit⟩
private def absorb : Typed.Interface signature Unit Unit (fun _ => Unit) :=
  fun _ => .query () (fun _ => some ())
private def validator : PIR.Process signature Bool := .call () (fun _ => .done false)

example : Typed.ChargedCostBound absorb (fun _ _ => 1) validator [] 1 :=
  ⟨0, by norm_num, fun _ => trivial⟩

example : ¬ Typed.ChargedCostBound absorb (fun _ _ => 2) validator [] 1 := by
  rintro ⟨remaining, cost, _⟩
  have impossible : (2 : ENNReal) ≤ 1 := (le_add_right le_rfl).trans cost
  norm_num at impossible

example : ¬ (∀ (_history : List Unit) (_event : Unit), (2 : ENNReal) ≤ 1) := by
  intro dominates
  have impossible := dominates [] ()
  norm_num at impossible

-- No proof can be manufactured from a cost proof at the wrong prices.
#check_failure (show Typed.ChargedCostBound absorb (fun _ _ => 2) validator [] 1 from
  (show Typed.ChargedCostBound absorb (fun _ _ => 1) validator [] 1 from
    ⟨0, by norm_num, fun _ => trivial⟩))

end TestsSecurity.ClaimChargeControls
