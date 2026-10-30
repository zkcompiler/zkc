module

public import ZkcSecurity.ProgramLogic.Transcript.Budget

@[expose] public section

/-! Composition of the existing charged walk bound. Branches retain their
actual guard; a uniform bound for a continuation must hold for every returned
value and reached history. No independence or alternate cost semantics is used. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.CostComposition
open Zkc.Transcript ZkcSecurity.FiatShamir
variable {I : PIR.Signature} {E P A B : Type} {Raw : E → Type}
  {absorb : Interface I E P Raw} {charge : List E → E → ENNReal}
  {history : List E}

theorem mono {process : PIR.Process I A} {small large : ENNReal}
    (bounded : Typed.ChargedCostBound absorb charge process history small)
    (le : small ≤ large) : Typed.ChargedCostBound absorb charge process history large :=
  (Typed.chargedCostBound_iff _ _ _ _ _).mpr
    (Walk.Bound.mono _ _ ((Typed.chargedCostBound_iff _ _ _ _ _).mp bounded) le)

theorem done (value : A) :
    Typed.ChargedCostBound absorb charge (.done value) history 0 := trivial

theorem halt (reason : PIR.Stop) :
    Typed.ChargedCostBound absorb charge (.halt reason : PIR.Process I A) history 0 := trivial

theorem bind (head : PIR.Process I A) (next : A → PIR.Process I B)
    (first second : ENNReal)
    (headBound : Typed.ChargedCostBound absorb charge head history first)
    (suffix : ∀ value reached, Typed.ChargedCostBound absorb charge (next value) reached second) :
    Typed.ChargedCostBound absorb charge (head.bind next) history (first + second) := by
  apply (Typed.chargedCostBound_iff _ _ _ _ _).mpr
  exact Walk.Bound.bind _ (fun _ => bot_le) next
    (fun value reached => (Typed.chargedCostBound_iff _ _ _ _ _).mp (suffix value reached))
    head ((Typed.chargedCostBound_iff _ _ _ _ _).mp headBound)

/-- A pure result projection preserves the cost of every reached query. -/
theorem map_iff (head : PIR.Process I A) (project : A → B)
    (budget : ENNReal) :
    Typed.ChargedCostBound absorb charge (head.bind fun value => .done (project value)) history budget ↔
      Typed.ChargedCostBound absorb charge head history budget := by
  induction head generalizing history budget with
  | done value => rfl
  | halt reason => rfl
  | call operation next ih =>
    rcases absorbed : absorb operation with ⟨event, recover⟩ | ⟨event, value⟩ |
      ⟨event, decode⟩ | _
    · simp only [PIR.Process.bind, Typed.ChargedCostBound, absorbed]
      constructor
      · intro bounded message value recovered
        exact (ih value _).mp (bounded message value recovered)
      · intro bounded message value recovered
        exact (ih value _).mpr (bounded message value recovered)
    · simp only [PIR.Process.bind, Typed.ChargedCostBound, absorbed]
      exact ih value _
    · simp only [PIR.Process.bind, Typed.ChargedCostBound, absorbed]
      constructor
      · rintro ⟨remaining, le, bounded⟩
        exact ⟨remaining, le, fun value => (ih value _).mp (bounded value)⟩
      · rintro ⟨remaining, le, bounded⟩
        exact ⟨remaining, le, fun value => (ih value _).mpr (bounded value)⟩
    · simp only [PIR.Process.bind, Typed.ChargedCostBound, absorbed]

theorem branch (condition : Prop) [Decidable condition]
    (left right : PIR.Process I A) (first second : ENNReal)
    (yes : condition → Typed.ChargedCostBound absorb charge left history first)
    (no : ¬ condition → Typed.ChargedCostBound absorb charge right history second) :
    Typed.ChargedCostBound absorb charge (if condition then left else right) history (if condition then first else second) := by
  by_cases selected : condition
  · simpa only [selected, ite_true] using yes selected
  · simpa only [selected, ite_false] using no selected

end ZkcSecurity.FiatShamir.CostComposition
