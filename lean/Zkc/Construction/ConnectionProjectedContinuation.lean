module

public import Zkc.Construction.ConnectionProjectedFrames
public import Zkc.Construction.ConnectionSubstitution

@[expose] public section

/-! Finite continuation instantiation for the source-owned repeat output mask. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionSubstitution
open Zkc.Source Zkc.Source.Structured NormalForm

def maskHead {scope : Scope} {types : List Ty} (role : Nat) (scopes : List (List Nat)) :
    Substitution (.tuple types :: scope) (.tuple types :: scope)
  | _, .here => calleeOutputs role scopes (Operands.identity types)
  | _, .there binder => identityArgument (.there binder)

def maskNext {scope : Scope} {types out : List Ty} {callees : List CalleeKey}
    (role : Nat) (scopes : List (List Nat)) (next : Form [] callees (.tuple types :: scope) out) :
    Form [] callees (.tuple types :: scope) out :=
  form next (maskHead role scopes)

theorem maskNext_denote {model : DomainModel} {I : PIR.Signature} {scope : Scope}
    {types out : List Ty} {callees : List CalleeKey} (role : Nat) (scopes : List (List Nat))
    (actions : PIR.OperationInterpretation (Interface model) I) (tables : Tables model I)
    (context : ProtocolContext) (runs : Runs model I) (processes : CalleeProcesses model callees I)
    (next : Form [] callees (.tuple types :: scope) out) (binders : Binders model scope)
    (values : Values (Component model.Value) types) :
    (maskNext role scopes next).denoteOn model actions tables (LawResults.empty model)
      context runs processes (.cons values binders) =
    next.denoteOn model actions tables (LawResults.empty model) context runs processes
      (.cons (maskValues role scopes values) binders) := by
  apply form_denote
  intro slot binder
  cases binder with
  | here =>
    exact (comps_eval_calleeOutputs (LawResults.empty model) binders role values scopes
      (Operands.identity types)).trans (ConnectionLibrary.staticMask_identity role scopes values)
  | there binder =>
    exact identityArgument_eval (.there binder)
      (show Binders model (.tuple types :: scope) from .cons values binders)

theorem form_calls {callees : List CalleeKey} {source target : Scope} {out : List Ty}
    (body : Form [] callees source out) (substitution : Substitution source target) :
    ((form body substitution).lawCalls, (form body substitution).calleeCalls) =
      (body.lawCalls, body.calleeCalls) := by
  induction body generalizing target with
  | byLaw entry => exact entry.elim0
  | split value absent present absentIH presentIH =>
    simp only [form, Form.lawCalls, Form.calleeCalls, (Prod.mk.inj (absentIH substitution)).1,
      (Prod.mk.inj (absentIH substitution)).2, (Prod.mk.inj (presentIH (lift substitution _))).1,
      (Prod.mk.inj (presentIH (lift substitution _))).2]
  | done | halt => rfl
  | _ =>
    simp_all only [form, Form.lawCalls, Form.calleeCalls, Prod.mk.injEq]

theorem maskNext_callsMatch {callees : List CalleeKey} {scope : Scope} {types out : List Ty}
    (role : Nat) (scopes : List (List Nat)) (next : Form [] callees (.tuple types :: scope) out)
    (matched : (maskNext role scopes next).CallsMatch) : next.CallsMatch := by
  have same := Prod.mk.inj (form_calls next (maskHead role scopes))
  simpa only [Form.CallsMatch, maskNext, same.1, same.2] using matched

theorem form_callsMatch {callees : List CalleeKey} {source target : Scope} {out : List Ty}
    (body : Form [] callees source out) (substitution : Substitution source target) :
    (form body substitution).CallsMatch ↔ body.CallsMatch := by
  have same := Prod.mk.inj (form_calls body substitution)
  simp only [Form.CallsMatch, same.1, same.2]

end Zkc.Construction.ConnectionSubstitution
