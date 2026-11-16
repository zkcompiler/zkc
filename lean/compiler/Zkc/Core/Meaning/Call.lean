module

public import Zkc.Core.Meaning.Local

@[expose] public section

/-!
The rule of a call.

A contract of a function is a property of its entry in a table of functions: on inputs that
satisfy its precondition, every return satisfies what it promises of the results, and every
stop what it promises of the stops. A law of a total function gives its results by a
mathematical function and never stops. The rule of a call installs a
contract at an actual call of a body: the operands and the continuation come from the term,
so that whoever uses the rule proves nothing about the plumbing of the call. A consumer of the
rule quantifies over every table that has the contract, so it cannot unfold the callee.
-/

namespace Zkc.Core

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)
  {hdr : FnHeader V} (callee : Member fns hdr)

/-- The contract of a function at its entry in a table: on inputs that satisfy `pre`, every
return satisfies `post` and every stop satisfies `stops`. -/
structure Contract (pre : HList M.Val hdr.ins → Prop)
    (post : HList M.Val hdr.ins → HList M.Val hdr.outs → Prop)
    (stops : HList M.Val hdr.ins → Stop → Prop) : Prop where
  holds : ∀ args, pre args → (table _ callee args).Every (fun _ _ => True) (post args) (stops args)

/-- The law of a total function at its entry in a table: it returns what `model` gives. -/
structure Law (model : HList M.Val hdr.ins → HList M.Val hdr.outs) : Prop where
  implements : ∀ args, table _ callee args = .done (model args)

/-- The rule of a call: at a call of the function in a body, with its operands from the
environment, every path satisfies what the continuation satisfies on every result that the
contract promises, and the stops that it promises, where the operands satisfy the
precondition. -/
theorem Contract.call {pre : HList M.Val hdr.ins → Prop}
    {post : HList M.Val hdr.ins → HList M.Val hdr.outs → Prop}
    {stops : HList M.Val hdr.ins → Stop → Prop} (contract : Contract M table callee pre post stops)
    {Γ : Ctx V.Ty} {outs : List V.Ty} (key : Key) (args : HList (Var Γ) hdr.ins)
    (results : Names hdr.outs) (rest : Term (localDialect V fns) (Γ.extend results) outs)
    (path : List Frame) (env : Env M.Val Γ) (Q : HList M.Val outs → Prop) (R : Stop → Prop)
    (admitted : pre (env.all args))
    (continues : ∀ values, post (env.all args) values →
      (rest.denote (localSem M fns table) path (env.extend results values)).Every
        (fun _ _ => True) Q R)
    (stopped : ∀ why, stops (env.all args) why → R why) :
    ((Term.op (D := localDialect V fns) key (LocalOp.call callee) args results rest).denote
      (localSem M fns table) path env).Every (fun _ _ => True) Q R := by
  change ((table _ callee (env.all args)).bind _).Every _ _ _
  rw [Process.every_bind]
  exact Process.every_mono _ _ continues stopped (contract.holds _ admitted)

/-- The rule of a call of a total function: the call is the continuation on what the law
gives. -/
theorem Law.call {model : HList M.Val hdr.ins → HList M.Val hdr.outs}
    (law : Law M table callee model) {Γ : Ctx V.Ty} {outs : List V.Ty} (key : Key)
    (args : HList (Var Γ) hdr.ins) (results : Names hdr.outs)
    (rest : Term (localDialect V fns) (Γ.extend results) outs) (path : List Frame)
    (env : Env M.Val Γ) :
    (Term.op (D := localDialect V fns) key (LocalOp.call callee) args results rest).denote
        (localSem M fns table) path env =
      rest.denote (localSem M fns table) path (env.extend results (model (env.all args))) := by
  change (table _ callee (env.all args)).bind _ = _
  rw [law.implements]
  rfl

end

end Zkc.Core
