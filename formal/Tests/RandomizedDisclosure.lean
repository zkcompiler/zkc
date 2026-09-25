import Zkc.Probability.Disclosure
import Mathlib.Probability.Distributions.Uniform

/-! Normalized joint-release controls: marginal privacy is insufficient. -/

set_option autoImplicit false

namespace Tests.RandomizedDisclosure

open Zkc.Probability.Disclosure

noncomputable def coin : PMF Bool := PMF.uniformOfFintype Bool
noncomputable def release (secret : Bool) : PMF (Bool × Bool) :=
  coin.map (fun r => (r, xor secret r))

theorem marginals (secret : Bool) :
    (release secret).map Prod.fst = coin ∧
      (release secret).map Prod.snd = coin := by
  constructor <;> apply PMF.ext <;> intro b <;> cases secret <;> cases b <;>
    simp [release, coin, PMF.map_comp, PMF.map_apply, tsum_fintype]

theorem joint_leaks : release false ≠ release true := by
  intro same
  have mass := congrArg (fun p : PMF (Bool × Bool) => p (false, false)) same
  simp [release, coin, PMF.map_apply, tsum_fintype] at mass

/-- Hiding the first mask channel repairs this example using a non-identity
coupling: the same observable bit is obtained from opposite private coins. -/
theorem masked_joint :
    coin.map (fun r => ((), r)) = coin.map (fun r => ((), !r)) := by
  let joint := coin.map (fun r => (r, !r))
  have left : joint.map Prod.fst = coin := by
    rw [PMF.map_comp]
    exact PMF.map_id coin
  have right : joint.map Prod.snd = coin := by
    apply PMF.ext
    intro b
    cases b <;> simp [joint, coin, PMF.map_comp, PMF.map_apply, tsum_fintype]
  apply joint_release coin coin joint left right (fun _ => ()) (fun _ => ())
    id Bool.not
  · intros; rfl
  · intro xy h
    obtain ⟨r, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp h
    cases same
    simp

end Tests.RandomizedDisclosure
