module

public import Zkc.Construction.ConnectionProjectedContinuation

@[expose] public section

/-! Checked liveness at an internal application seam. A finite typed selection
changes successful return leaves only. The caller must pass a syntactic
factorization check; neither a semantic equation nor a weakened root return
relation is an interface field. All operations, callbacks and stops are kept.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionReturnProjection
open Zkc.Source Zkc.Source.Structured NormalForm

abbrev Selection (types : List Ty) := Values (fun _ : Ty => Bool) types

def components {scope : Scope} : {types : List Ty} → Selection types →
    Values (Comp [] scope) types → Values (Comp [] scope) types
  | _, .nil, .nil => .nil
  | _, .cons keep rest, .cons value values =>
      .cons (if keep then value else .absent) (components rest values)

def values {V : Ty → Type} : {types : List Ty} → Selection types →
    Values (Component V) types → Values (Component V) types
  | _, .nil, .nil => .nil
  | _, .cons keep rest, .cons value tail =>
      .cons (if keep then value else none) (values rest tail)

theorem components_eval {model : DomainModel} {scope : Scope} {types : List Ty}
    (selection : Selection types) (tuple : Values (Comp [] scope) types)
    (binders : Binders model scope) :
    Comps.eval (LawResults.empty model) (components selection tuple) binders =
      values selection (Comps.eval (LawResults.empty model) tuple binders) := by
  induction selection with
  | nil => cases tuple; rfl
  | cons keep rest ih =>
    cases tuple with
    | cons value tail => cases keep <;> simp [components, values, Comps.eval, Comp.eval, ih]

/-- Project leaves of the referenced template, without expanding any nested
callee or changing any operation that can fail or have an effect. -/
def form {callees : List CalleeKey} {types : List Ty} (selection : Selection types) :
    {scope : Scope} → Form [] callees scope types → Form [] callees scope types
  | _, .done tuple => .done (components selection tuple)
  | _, .halt reason => .halt reason
  | _, .send ty site peer value next => .send ty site peer value (form selection next)
  | _, .receive ty site peer next => .receive ty site peer (form selection next)
  | _, .query site request args next => .query site request args (form selection next)
  | _, .split value absent present => .split value (form selection absent) (form selection present)
  | _, .guard equality left right next => .guard equality left right (form selection next)
  | _, .strict helper args next => .strict helper args (form selection next)
  | _, .compute op allowed args next => .compute op allowed args (form selection next)
  | _, .math helper args next => .math helper args (form selection next)
  | _, .byLaw entry _ _ => entry.elim0
  | _, .owned owner helper args next => .owned owner helper args (form selection next)
  | _, .repeat spec site callback count state captures next =>
      .repeat spec site callback count state captures (form selection next)
  | _, .apply callee signature roles site args next =>
      .apply callee signature roles site args (form selection next)

/-- Exact all-outcome preservation: the same process, followed solely at a
successful leaf by the finite projection. In particular a stopped computation
does not become a successful empty return. -/
theorem form_denote {model : DomainModel} {I : PIR.Signature} {callees : List CalleeKey}
    {types : List Ty} (selection : Selection types)
    (actions : PIR.OperationInterpretation (Interface model) I) (tables : Tables model I)
    (context : ProtocolContext) (runs : Runs model I) (processes : CalleeProcesses model callees I)
    {scope : Scope} (body : Form [] callees scope types) (binders : Binders model scope) :
    (form selection body).denoteOn model actions tables (LawResults.empty model) context runs processes binders =
      (body.denoteOn model actions tables (LawResults.empty model) context runs processes binders).bind
        (fun tuple => .done (values selection tuple)) := by
  induction body with
  | done tuple => exact congrArg PIR.Process.done (components_eval selection tuple binders)
  | halt => rfl
  | byLaw entry => exact entry.elim0
  | split value absent present absentIH presentIH =>
    simp only [form, Form.denoteOn, Form.denoteWithOn]
    cases value.eval (LawResults.empty model) binders with
    | none => exact absentIH selection binders
    | some value => exact presentIH selection (.cons value binders)
  | guard equality left right next ih =>
    simp only [form, Form.denoteOn, Form.denoteWithOn]
    split
    · exact ih selection binders
    · rfl
  | _ =>
    simp only [form, Form.denoteOn, Form.denoteWithOn, PIR.Process.bind_assoc]
    congr 1
    funext value
    apply_assumption

def head {scope : Scope} {types : List Ty} (selection : Selection types) :
    ConnectionSubstitution.Substitution (.tuple types :: scope) (.tuple types :: scope)
  | _, .here => components selection (ConnectionSubstitution.identityArgument (slot := .tuple types) .here)
  | _, .there binder => ConnectionSubstitution.identityArgument (.there binder)

/-- The finite caller check. The equation is about typed syntax and is checked
by kernel reduction, rather than assumed as an equation about executions. -/
def continuation {scope : Scope} {types out : List Ty} {callees : List CalleeKey}
    (selection : Selection types) (next : Form [] callees (.tuple types :: scope) out) :
    Form [] callees (.tuple types :: scope) out :=
  ConnectionSubstitution.form next (head selection)

theorem continuation_denote {model : DomainModel} {I : PIR.Signature} {callees : List CalleeKey}
    {scope : Scope} {types out : List Ty} (selection : Selection types)
    (actions : PIR.OperationInterpretation (Interface model) I) (tables : Tables model I)
    (context : ProtocolContext) (runs : Runs model I) (processes : CalleeProcesses model callees I)
    (next : Form [] callees (.tuple types :: scope) out) (binders : Binders model scope)
    (tuple : Values (Component model.Value) types) :
    (continuation selection next).denoteOn model actions tables (LawResults.empty model)
      context runs processes (.cons tuple binders) =
    next.denoteOn model actions tables (LawResults.empty model) context runs processes
      (.cons (values selection tuple) binders) := by
  let extended : Binders model (.tuple types :: scope) := .cons tuple binders
  apply ConnectionSubstitution.form_denote
  intro slot binder
  cases binder with
  | here =>
    exact (components_eval selection _ extended).trans
      (congrArg (values selection) (ConnectionSubstitution.identityArgument_eval (slot := .tuple types) .here extended))
  | there binder => exact ConnectionSubstitution.identityArgument_eval (.there binder) extended

/-- The shared composition theorem used by both simulation and independent
route coverage. Its only instance obligation is the finite caller equality. -/
theorem bind_continuation {model : DomainModel} {I : PIR.Signature}
    {callees earlier : List CalleeKey} {scope : Scope} {types out : List Ty}
    (selection : Selection types) (body : Form [] earlier scope types)
    (next : Form [] callees (.tuple types :: scope) out)
    (checked : continuation selection next = next)
    (actions : PIR.OperationInterpretation (Interface model) I) (tables : Tables model I)
    (calleeContext context : ProtocolContext) (calleeRuns runs : Runs model I)
    (calleeProcesses : CalleeProcesses model earlier I) (processes : CalleeProcesses model callees I)
    (binders : Binders model scope) :
    (body.denoteOn model actions tables (LawResults.empty model) calleeContext calleeRuns calleeProcesses binders).bind
      (fun tuple => next.denoteOn model actions tables (LawResults.empty model) context runs processes (.cons tuple binders)) =
    ((form selection body).denoteOn model actions tables (LawResults.empty model) calleeContext calleeRuns calleeProcesses binders).bind
      (fun tuple => next.denoteOn model actions tables (LawResults.empty model) context runs processes (.cons tuple binders)) := by
  rw [form_denote, PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext tuple
  exact (congrArg (fun body => body.denoteOn model actions tables (LawResults.empty model)
    context runs processes (.cons tuple binders)) checked).symm.trans
      (continuation_denote selection actions tables context runs processes next binders tuple)

end Zkc.Construction.ConnectionReturnProjection
