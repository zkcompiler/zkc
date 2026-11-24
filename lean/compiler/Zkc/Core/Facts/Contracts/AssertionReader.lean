module

public import Zkc.Core.Facts.Contracts.LocalReader
public import Zkc.Core.Facts.Contracts.TypeLaws
public import Zkc.Core.Program.LocalRules
public import Zkc.Core.Meaning.Validity

@[expose] public section

namespace Zkc.Core.BodyAnalysis

variable {D : Dialect} {Raw Who : Type}

/-- A dialect can resolve just the operations available in its assertion language. -/
theorem AssertionTypes.ofResolved_lawful {σ : Setting D Raw} (types : AssertionTypes D.Ty Raw)
    (rules : σ.cfg.rules.AssertionLaws σ.sem σ.R σ.Run σ.Valid)
    (resolve : ∀ {raw ins outs}, types.signature raw ins = some outs →
      σ.cfg.rules.assertable raw = true ∧ ∃ op : D.Op ins outs, σ.cfg.rules.written op = raw)
    (readBool : ∀ {t}, types.boolean t = true → ∀ v,
      TypedValue σ.sem σ.Valid v t → ∃ b, σ.R.bool v = some b) : types.Lawful σ := by
  refine ⟨fun h => (resolve h).1, ?_, readBool⟩
  intro raw ins outs checked xs typed
  obtain ⟨allowed, op, printed⟩ := resolve checked
  rw [← printed] at allowed ⊢
  obtain ⟨args, rfl, valid⟩ := typed.realizes
  obtain ⟨shared, noRequirements⟩ := rules.assertable op allowed
  have required : σ.cfg.rules.Required σ.sem σ.R σ.Run σ.Valid op args := by
    intro e mem
    rw [noRequirements] at mem
    cases mem
  obtain ⟨ys, _, ran, _⟩ := rules.defined op shared ⟨0⟩ [] args valid required
  have kept := (rules.keeps _ _ _ ran valid).1
  exact ⟨_, ⟨ran, valid, kept⟩, ArgumentsMatch.ofValues ys kept⟩

theorem AssertionTypes.ofReader_lawful {σ : Setting D Raw}
    (rules : σ.cfg.rules.Lawful σ.sem σ.permitted σ.R σ.Run σ.Valid σ.undefined)
    (reader : Zkc.Core.Rules D Raw Who) (canonical : reader.Canonical)
    (same : ∀ {ins outs} (op : D.Op ins outs), σ.cfg.rules.written op = reader.printOp op)
    (boolean : D.Ty → Bool) (readBool : ∀ {t}, boolean t = true → ∀ v,
      TypedValue σ.sem σ.Valid v t → ∃ b, σ.R.bool v = some b) :
    (ofReader reader σ.cfg.rules.assertable boolean).Lawful σ := by
  have resolve {raw ins outs}
      (h : (ofReader reader σ.cfg.rules.assertable boolean).signature raw ins = some outs) :
      σ.cfg.rules.assertable raw = true ∧ ∃ op : D.Op ins outs, σ.cfg.rules.written op = raw := by
    cases allowed : σ.cfg.rules.assertable raw with
    | false => simp [ofReader, allowed] at h
    | true =>
      cases parsed : reader.op raw ins with
      | error _ => simp [ofReader, allowed, parsed, Except.toOption] at h
      | ok result =>
        obtain ⟨res, op⟩ := result
        simp [ofReader, allowed, parsed, Except.toOption] at h
        subst res
        exact ⟨rfl, op, (same op).trans (canonical.op raw op parsed)⟩
  exact ofResolved_lawful _ rules.toAssertionLaws resolve readBool

theorem localAssertionBool {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)}
    (table : FnTable M fns) {t : V.Ty} (passes : decide (t = .bool) = true)
    (v : (localSem M fns table).Dyn) (typed : TypedValue _ (ValidDyn M) v t) :
    ∃ b, (localReading M).bool v = some b := by
  obtain ⟨u, x⟩ := v
  have eq : u = .bool := typed.2.trans (of_decide_eq_true passes)
  subst u
  exact ⟨x, rfl⟩

section
variable {V : Vocabulary} (fns : List (FnHeader V))
private def acceptsAll : LocalRaw V → Bool := fun _ => true

example : (localAssertionTypes fns acceptsAll).signature (.owned .natLess [] []) [.nat, .nat] =
    some [.bool] := rfl
example : (localAssertionTypes fns acceptsAll).signature (.owned .natLess [] []) [.bool, .nat] =
    none := rfl
example : (localAssertionTypes fns (fun _ => false)).signature (.owned .natLess [] []) [.nat, .nat] =
    none := rfl
end

end Zkc.Core.BodyAnalysis
