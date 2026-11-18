module

@[expose] public section

/-!
Lemmas about types of Lean's library that the proofs of the core use: lists and `Except`.
-/

namespace Zkc.Core

/-! ## Lists -/

theorem foldl_invariant {α β : Type} {P : β → Prop} (f : β → α → β) :
    ∀ (xs : List α) (b : β), P b → (∀ b x, x ∈ xs → P b → P (f b x)) → P (xs.foldl f b)
  | [], _, hb, _ => hb
  | x :: xs, b, hb, step =>
      foldl_invariant f xs (f b x) (step b x List.mem_cons_self hb)
        (fun b' x' m h => step b' x' (List.mem_cons_of_mem _ m) h)

theorem mem_range'_bounds {s n i : Nat} (m : i ∈ List.range' s n) : s ≤ i ∧ i < s + n := by
  obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp m
  exact ⟨by omega, by omega⟩

theorem range'_getD {s n j : Nat} (h : j < n) : (List.range' s n).getD j 0 = s + j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_range' h]
  simp

theorem nodup_apart {α : Type} {l₁ l₂ : List α} (h : (l₁ ++ l₂).Nodup) {x : α} (h₁ : x ∈ l₁)
    (h₂ : x ∈ l₂) : False :=
  (List.nodup_append.mp h).2.2 x h₁ x h₂ rfl

/-! ## `Except` -/

theorem ok_of_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : x.bind f = .ok y) : ∃ v, x = .ok v ∧ f v = .ok y := by
  cases x with
  | error _ => cases h
  | ok v => exact ⟨v, rfl, h⟩

theorem ok_of_map {ε α β : Type} {x : Except ε α} {f : α → β} {y : β}
    (h : x.map f = .ok y) : ∃ v, x = .ok v ∧ f v = y := by
  cases x with
  | error _ => cases h
  | ok v => exact ⟨v, rfl, Except.ok.inj h⟩

end Zkc.Core
