module

public import ZkcFormal.ProcessJudgment
public import Mathlib.Algebra.Order.Ring.NNRat

@[expose] public section
set_option autoImplicit false

/-!
The judgment with fees: a process is judged within a budget when, at every effect, a fee chosen
before the reply pays for the replies that are excluded there, and every other permitted reply is
judged within what is left. The budget is a nonnegative rational. This file is apart from
`ProcessJudgment.lean` because it is the one judgment that needs an ordered field.
-/

namespace Zkc.Core
variable {S : Sig} {H A : Type}

/-- A site policy bounds the excluded replies at a fee chosen before the reply. Every permitted
reply outside the excluded set inherits what is left of the budget. A fee is a nonnegative
rational and fees add along a path. What a fee bounds belongs to the policy: for a draw, the
probability of the excluded set under the law of the draw. -/
def ProcessJudgment.charged (allowed : ∀ op, S.Reply op → Prop)
    (small : (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop) : ProcessJudgment S (ℚ≥0 → Prop) where
  node op next budget := ∃ fee bad, fee ≤ budget ∧ small op fee bad ∧
    ∀ v, allowed op v → ¬bad v → next v (budget - fee)

/-- A judgment with fees within a budget holds within a larger one, when what is asked at the
end does not read what is left of the budget. -/
theorem Process.charged_of_le (allowed : ∀ op, S.Reply op → Prop)
    (small : (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop) (p : Process S H A)
    (done : A → Prop) (halt : H → Prop) :
    ∀ {budget larger : ℚ≥0}, budget ≤ larger →
      p.interpret (.charged allowed small) (fun a _ => done a) (fun e _ => halt e) budget →
      p.interpret (.charged allowed small) (fun a _ => done a) (fun e _ => halt e) larger := by
  induction p with
  | done | halt => exact fun _ h => h
  | call op k ih =>
    rintro budget larger le ⟨fee, bad, bound, ok, next⟩
    exact ⟨fee, bad, bound.trans le, ok, fun v valid kept =>
      ih v (tsub_le_tsub_right le fee) (next v valid kept)⟩

theorem Process.every_of_zero_charge (allowed : ∀ op, S.Reply op → Prop)
    (small : (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop)
    (zero : ∀ op bad, small op 0 bad → ∀ v, allowed op v → ¬bad v) (p : Process S H A)
    (done : A → Prop) (halt : H → Prop)
    (h : p.interpret (.charged allowed small) (fun a _ => done a) (fun e _ => halt e) 0) :
    p.Every allowed done halt := by
  induction p with
  | done | halt => exact h
  | call op k ih =>
    obtain ⟨fee, bad, bound, ok, next⟩ := h
    obtain rfl := le_zero_iff.mp bound
    exact fun v valid => ih v (tsub_zero (0 : ℚ≥0) ▸ next v valid (zero op bad ok v valid))

end Zkc.Core
