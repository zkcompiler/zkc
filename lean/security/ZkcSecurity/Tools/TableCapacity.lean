module

public import Zkc.Source.Structured.Algebra
public meta import Lean.Elab.Tactic
public meta import Mathlib.Tactic.Tauto

@[expose] public section

/-! A finite table capacity follows from an actual round guard and a proved
shape equation. No honest-input policy is inserted into an adversarial proof.
The tactic searches only for candidates; the ordinary theorem checks them. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.TableCapacity
open Zkc.Source.Structured

theorem of_guard {F : Type} (raw : List F) (count maximum : Nat)
    (allowed : count ≤ maximum) (shape : raw.length = 2 ^ count)
    (bounded : 2 ^ maximum < indexLimit) : raw.length < indexLimit := by
  rw [shape]
  exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) allowed) bounded

open Lean Meta Elab Tactic in
elab "prove_table_capacity" : tactic => withMainContext <| Term.withoutErrToSorry <| withoutRecover do
  let pending := (← getGoals).tail
  let original ← saveState
  let mut errors : Array MessageData := #[]
  for declaration in ← getLCtx do
    unless declaration.isImplementationDetail do
      let type ← instantiateMVars declaration.type
      if type.isAppOf ``LE.le then
        original.restore
        try
          setGoals [(← getMainGoal)]
          let bound ← Term.exprToSyntax declaration.toExpr
          evalTactic (← `(tactic|
            apply of_guard (allowed := $bound)
            <;> first | assumption | tauto | decide +kernel))
          if (← getGoals).isEmpty then
            setGoals pending
            return
        catch error => errors := errors.push error.toMessageData
  original.restore
  throwError "no checked source guard and shape establish table capacity: {errors}"

end ZkcSecurity.Tools.TableCapacity
