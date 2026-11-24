module

public import Zkc.Core.Facts.Contracts.RoleReader
public import Zkc.Core.Facts.Contracts.AssertionReader
public import Zkc.Core.Facts.Knowledge.DialectReadings

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {hs : Headers V} {r : Role}

theorem readRoleValue_prints {raw : RoleRaw V} {ins outs} {op : RoleOp V hs r ins outs}
    (found : readRoleValue hs r raw ins = some ⟨outs,op⟩) : roleValueForm op = some raw := by
  cases raw with
  | compute holders w =>
    simp only [readRoleValue] at found
    split at found <;> try cases found
    split at found <;> try cases found
    split at found
    · next res localOp parsed =>
      cases found
      have same := localRules_canonical.op w localOp parsed
      exact congrArg (fun form => some (RoleRaw.compute holders form)) same
    · cases found
  | absent types =>
    cases ins <;> simp only [readRoleValue] at found
    · split at found <;> cases found <;> rfl
    · cases found
  | keep holders =>
    cases ins with
    | nil => cases found
    | cons head tail =>
      cases tail with
      | cons => cases found
      | nil =>
        cases head
        simp only [readRoleValue] at found
        split at found <;> cases found <;> rfl
  | effect | apply => cases found

theorem roleAssertionBool (M : Model V) (fns : FnTable M hs.fns) (roles : RTable M hs.protocols)
    {t : LTy V} (passes : t.ty = .bool ∧ r ∈ t.holders) {v}
    (typed : TypedValue (roleSem M r fns roles) (RoleValueValid M r) v t) :
    ∃ b, (roleReading M r).bool v = some b := by
  obtain ⟨⟨ty, holders⟩, val⟩ := v
  obtain ⟨_,rfl⟩ := typed
  obtain ⟨rfl,held⟩ := passes
  exact ⟨reveal M held val, by simp [roleReading, heldValue, held, localReading]⟩

theorem roleAssertionTypes_lawful (σ : Setting (roleDialect V hs r) (RoleRaw V))
    (rules : σ.cfg.rules.AssertionLaws σ.sem σ.R σ.Run σ.Valid)
    (written : ∀ {ins outs} (op : RoleOp V hs r ins outs) {raw}, roleValueForm op = some raw →
      σ.cfg.rules.written op = raw)
    (readBool : ∀ {t}, t.ty = .bool ∧ r ∈ t.holders → ∀ v,
      TypedValue σ.sem σ.Valid v t → ∃ b, σ.R.bool v = some b) :
    (roleAssertionTypes hs r σ.cfg.rules.assertable).Lawful σ := by
  apply AssertionTypes.ofResolved_lawful _ rules _ (fun ok => readBool (of_decide_eq_true ok))
  intro raw ins outs found
  simp only [roleAssertionTypes] at found
  split at found
  · next allowed =>
    obtain ⟨⟨types, op⟩, parsed, rfl⟩ := Option.map_eq_some_iff.mp found
    exact ⟨allowed, op, written op (readRoleValue_prints parsed)⟩
  · cases found

section
variable (hs : Headers V)
private def allForms (_ : RoleRaw V) := true
example : (roleAssertionTypes hs 0 allForms).signature (.compute [0] (.owned .natLess [] []))
    [⟨.nat,[0,1]⟩, ⟨.nat,[0]⟩] = some [⟨.bool,[0]⟩] := by rfl'
example : (roleAssertionTypes hs 0 allForms).signature (.compute [0] (.owned .natLess [] []))
    [⟨.nat,[1]⟩, ⟨.nat,[0]⟩] = none := by rfl'
example : (roleAssertionTypes hs 0 allForms).signature (.keep [0]) [⟨.nat,[0,1]⟩] = some [⟨.nat,[0]⟩] := by rfl'
example : (roleAssertionTypes hs 0 allForms).signature (.keep [1]) [⟨.nat,[0,1]⟩] = none := by rfl'
example : (roleAssertionTypes hs 0 allForms).signature (.absent [⟨.fin 0,[1]⟩]) [] = some [⟨.fin 0,[1]⟩] := by rfl'
example : (roleAssertionTypes hs 0 allForms).boolean ⟨.bool,[1]⟩ = false := by rfl'
end

end Zkc.Core.BodyAnalysis
