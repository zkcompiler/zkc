module

public import Zkc.Core.Program.Erase

@[expose] public section
namespace Zkc.Core
variable {D : Dialect} {Raw Who : Type} (rules : Rules D Raw Who)

/-- The executable region and its inferred result types are recovered together. -/
theorem Term.packed_eq_of_erasure (lawful : rules.Lawful) {Γ : Ctx D.Ty} {xs ys : List D.Ty}
    (a : Term D Γ xs) (b : Term D Γ ys) (aArmed : a.armed = true) (bArmed : b.armed = true)
    (same : eraseBody rules.printOp rules.printWho a = eraseBody rules.printOp rules.printWho b) :
    (⟨xs,a⟩ : (res : List D.Ty) × Term D Γ res) = ⟨ys,b⟩ := by
  have left := elabBody_erase rules lawful ⟨0⟩ a aArmed [] none
  rw [same, elabBody_erase rules lawful ⟨0⟩ b bArmed [] none] at left
  exact (Except.ok.inj left).symm

/-- A checked occurrence retains the exact block instruction, its result bindings and the
remainder of the caller. The remainder runs in the original extended environment. -/
structure FirstBlock {Γ : Ctx D.Ty} {mid outs : List D.Ty} (body : Term D Γ outs) (expected : Term D Γ mid) where
  key : Key
  index : Nat
  results : Names mid
  rest : Term D (Γ.extend results) outs
  exactBody : body = .block key index expected results rest

def Term.firstBlock [DecidableEq Raw] [DecidableEq Who] (lawful : rules.Lawful)
    {Γ : Ctx D.Ty} {mid outs : List D.Ty} (candidate : Term D Γ mid) (armed : candidate.armed = true) :
    (actual : Term D Γ outs) → actual.armed = true → Option (FirstBlock actual candidate)
  | .block key i inside results rest, ok => do
    if same : eraseBody rules.printOp rules.printWho inside = eraseBody rules.printOp rules.printWho candidate then
      have packed := Term.packed_eq_of_erasure rules lawful inside candidate (Bool.and_eq_true_iff.mp ok).1 armed same
      return ← show Option _ from by
        cases packed
        exact some ⟨key,i,results,rest,rfl⟩
    else none
  | _, _ => none

end Zkc.Core
