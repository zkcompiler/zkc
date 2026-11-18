module

public import Zkc.Formal.Written.GroupModel

@[expose] public section
set_option autoImplicit false

namespace Zkc.Formal.Written
open Core

variable {D : Dialect} {sem : Semantics D} {Γ : Ctx D.Ty} {mid outs : List D.Ty}
    {key : Key} {i : Instr D Γ mid} {names : Names mid} {rest : Term D (Γ.extend names) outs}
    {path : List Frame} {env : Env sem.Val Γ}
    {trace : List ((op : sem.S.Op) × sem.S.Reply op)} {Q : Prop}

theorem afterReturn (exit : HList (Var Γ) outs) (env : Env sem.Val Γ) (path : List Frame) :
    Returns ((Term.ret exit).denote sem path env) [] := by
  rw [Term.denote_ret]
  exact returns_done _

/-- Consume one pure instruction. Its result is explicit so later instructions can reuse
the value without re-evaluating its producing instruction or traversing an old environment. -/
theorem afterValue (values : HList sem.Val mid) (step : i.denote sem key path env = .done values)
    (tail : Returns (rest.denote sem path (env.extend names values)) trace ↔ Q) :
    Returns ((Term.step key i names rest).denote sem path env) trace ↔ Q := by
  rw [Term.denote_step, step]
  exact tail

/-- Consume exactly the operation and typed reply at the front of the recorded execution. -/
theorem afterReply (op : sem.S.Op) (reply : sem.S.Reply op) (bindValue : sem.S.Reply op → HList sem.Val mid)
    (step : i.denote sem key path env = .call op (fun x => .done (bindValue x)))
    (tail : Returns (rest.denote sem path (env.extend names (bindValue reply))) trace ↔ Q) :
    Returns ((Term.step key i names rest).denote sem path env) (⟨op,reply⟩ :: trace) ↔ Q := by
  rw [Term.denote_step, step]
  exact (@returns_call sem.S sem.H _ op (fun x => rest.denote sem path (env.extend names (bindValue x))) reply trace).trans tail

/-- A checked branch either returns its values to the remaining term or stops. -/
theorem afterDecision (test : Bool) (why : sem.H) (values : HList sem.Val mid)
    (step : i.denote sem key path env = (bif test then .done values else .halt why))
    (tail : Returns (rest.denote sem path (env.extend names values)) []) :
    Returns ((Term.step key i names rest).denote sem path env) [] ↔ require test = some () := by
  rw [Term.denote_step, step]
  cases test <;> simp [require, Process.bind, tail]

end Zkc.Formal.Written
