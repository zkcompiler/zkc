import Zkc.Relation.Encoding
import Zkc.Relation.RankOne
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace Tests.RelationEncoding

open Zkc.Relation

private def squareSource : PIR.Relation.Family where
  Statement := ℤ × ℤ
  Witness := ℤ
  holds s w := w * w = s.1 ∧ w = s.2

private def auxiliaryTarget : PIR.Relation.Family where
  Statement := ℤ × ℤ
  Witness := ℤ × ℤ
  holds t z := z.2 * z.2 = z.1 ∧ z.1 = t.2 ∧ z.2 = t.1

/-- Statement slots are swapped and the target carries a constrained auxiliary. -/
private def squareEncoding : Encoding squareSource auxiliaryTarget where
  statementMap s := (s.2, s.1)
  corresponds s w z := z.2 = w ∧ z.1 = s.1
  complete s w h := ⟨(s.1, w), ⟨h.1, rfl, h.2⟩, rfl, rfl⟩
  sound _s z h := ⟨z.2, ⟨h.1.trans h.2.1, h.2.2⟩, rfl, h.2.1⟩

example : PIR.Relation.Valid auxiliaryTarget (3, 9) :=
  (squareEncoding.valid_iff (9, 3)).mp ⟨(3 : ℤ), by change 3 * 3 = (9 : ℤ) ∧ 3 = (3 : ℤ); decide⟩

example : ¬ auxiliaryTarget.holds (3, 9) (8, 3) := by unfold auxiliaryTarget; dsimp; decide

private def source : PIR.Relation.Family where
  Statement := Bool
  Witness := Unit
  holds s _ := s = true

private def underconstrained : PIR.Relation.Family where
  Statement := Bool
  Witness := Unit
  holds _ _ := True

-- Every honest witness translates, even though false statements are admitted.
example : ∀ s w, source.holds s w → underconstrained.holds s w := by
  intro _ _ _
  trivial

example : ¬ ∃ e : Encoding source underconstrained, e.statementMap = id := by
  rintro ⟨e, _map⟩
  have target : PIR.Relation.Valid underconstrained (e.statementMap false) := ⟨(), trivial⟩
  obtain ⟨w, impossible⟩ := (e.valid_iff false).mpr target
  exact Bool.noConfusion impossible

def layout : RankOne.Layout 2 1 4 where
  toFun
    | .one => 0
    | .publicInput j => ⟨j.val + 1, by omega⟩
    | .witness _ => 3
  invFun i := if i = 0 then .one else if i = 1 then .publicInput 0
    else if i = 2 then .publicInput 1 else .witness 0
  left_inv slot := by
    cases slot with
    | one => rfl
    | publicInput j => fin_cases j <;> rfl
    | witness j => fin_cases j; rfl
  right_inv i := by fin_cases i <;> rfl

def system : RankOne.System (ZMod 101) 2 4 :=
  ⟨⟨#v[[(3, 1)], [(1, 1)]]⟩, ⟨#v[[(3, 1)], [(3, 1)]]⟩,
    ⟨#v[[(1, 1)], [(2, 1)]]⟩⟩

private def statement : Fin 2 → ZMod 101 := ![4, 8]
private def assignment : Fin 4 → ZMod 101 := ![1, 4, 8, 2]

example : system.Satisfies assignment := by unfold RankOne.System.Satisfies; decide
example : RankOne.Bound layout statement assignment := by unfold RankOne.Bound; decide
example : ¬ RankOne.Bound layout (![8, 4] : Fin 2 → ZMod 101) assignment := by unfold RankOne.Bound; decide
example : system.Satisfies (fun _ => 0) := system.satisfies_zero
example : ¬ RankOne.Bound layout statement (fun _ => 0) := by unfold RankOne.Bound; decide

-- Soundness recovers the witness from an independently supplied assignment.
example : ∃ w, (system.family layout).holds statement w ∧
    RankOne.embed layout statement w = assignment :=
  (system.encoding layout).sound statement assignment
    ⟨by change RankOne.Bound layout statement assignment; unfold RankOne.Bound; decide,
      by unfold RankOne.System.Satisfies; decide⟩

end Tests.RelationEncoding
