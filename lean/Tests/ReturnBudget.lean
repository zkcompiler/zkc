import Zkc.Transcript.ReturnBudget
import Mathlib.Basic.ENNReal.Basic

set_option autoImplicit false
noncomputable section
namespace Tests.ReturnBudget
open Zkc.Transcript

abbrev signature : PIR.Signature := ⟨Bool, fun _ => Unit⟩

def absorb : Interface signature Bool Unit (fun _ => Unit)
  | false => .send false ()
  | true => .query true some

def price (history : List Bool) (_event : Bool) : ENNReal :=
  if history = [] then 1 else 0

def walk : Walk signature (List Bool) ENNReal := absorb.walk (absorb.lossCharge price)

def first : PIR.Process signature Unit := .call false (fun _ => .done ())
def next : PIR.Process signature Unit := .call true (fun _ => .done ())

def interaction : PIR.Interaction signature where
  Role := Unit
  Phase := List Bool
  owner _ := ()
  enabled _ _ := True
  advance history operation _ := history ++ [operation]

theorem position_preserved (phase position : List Bool) (operation : Bool)
    (reply : Unit) (later : List Bool) (same : phase = position)
    (edge : walk.next position operation reply later) :
    interaction.advance phase operation reply = later := by
  subst phase
  cases operation with
  | false => exact edge.2.symm
  | true => exact edge.symm

theorem prefix_budget : walk.Bound first [] 0 :=
  ⟨trivial, 0, by change (0 : ENNReal) + 0 ≤ 0; simp, fun _ _ _ => trivial⟩

/-- The generic rule uses the send's reached history to discharge the suffix
at zero. It never asks for that bound at the unrelated empty history. -/
theorem reached_history_composition : walk.Bound (first.bind (fun _ => next)) [] 0 := by
  have composed := Walk.Bound.bind_of_returns walk (fun _ => bot_le)
    interaction (fun _ phase => phase = [false]) Eq position_preserved (fun _ => next)
    (second := 0) (fun _ phase position returned related => by
      have atReturn : position = [false] := related.symm.trans returned
      rw [atReturn]
      exact ⟨trivial, 0, by change (0 : ENNReal) + 0 ≤ 0; simp, fun _ _ _ => trivial⟩)
    first [] [] 0 (fun _ => rfl) rfl prefix_budget
  simpa only [add_zero] using composed

/-- The old universal-position premise is false for the same suffix. -/
theorem universal_suffix_budget_false : ¬ ∀ position, walk.Bound next position 0 := by
  intro claimed
  obtain ⟨_, remaining, bounded, _⟩ := claimed []
  change (1 : ENNReal) + remaining ≤ 0 at bounded
  have impossible : (1 : ENNReal) ≤ 0 :=
    (le_add_of_nonneg_right (show (0 : ENNReal) ≤ remaining from bot_le)).trans bounded
  exact (by simp : ¬ (1 : ENNReal) ≤ 0) impossible

/-- Strengthening just the logical return predicate cannot recover the missing
relationship with the walk position in the conservative contract. -/
theorem universal_position_premises_unavailable :
    ¬ ∃ post : Unit → List Bool → Prop,
      PIR.Boundary.Returns interaction post first [] ∧
      (∀ value phase, post value phase → ∀ position, walk.Bound next position 0) := by
  rintro ⟨post, returned, suffix⟩
  exact universal_suffix_budget_false (suffix () [false] (returned ()))

/-- A stopped prefix needs neither a possible return nor a suffix budget. -/
theorem stopped_prefix_needs_no_suffix :
    walk.Bound ((PIR.Process.halt .abort).bind (fun _ : Unit => next)) [] 0 := by
  have composed := Walk.Bound.bind_of_returns walk (fun _ => bot_le)
    interaction (fun (_ : Unit) _ => False) Eq position_preserved (fun _ => next)
    (second := 0) (fun _ _ _ impossible _ => impossible.elim)
    (.halt .abort) [] [] 0 trivial rfl trivial
  simpa only [add_zero] using composed

#print axioms Walk.Bound.bind_of_returns
#print axioms reached_history_composition
#print axioms universal_suffix_budget_false
#print axioms universal_position_premises_unavailable
#print axioms stopped_prefix_needs_no_suffix
end Tests.ReturnBudget
