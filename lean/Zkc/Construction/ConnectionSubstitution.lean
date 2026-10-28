module

public import Zkc.Source.Structured.NormalForm.Observation

@[expose] public section

/-! Typed finite instantiation of a checked normal-form body. Substitution
changes binder references only: callbacks, nominal operations, helper keys,
callee keys, application sites and ordered roles remain source owned. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionSubstitution
open Zkc.Source Zkc.Source.Structured NormalForm

abbrev Substitution (source target : Scope) :=
  {slot : Slot} → Var source slot → Argument [] target slot

def resultTerms {scope : Scope} {types : List Ty} (binder : Var scope (.results types)) :
    {rest : List Ty} → Operands types rest → Terms [] scope rest
  | _, .nil => .nil
  | _, .cons position rest => .cons (.result binder position) (resultTerms binder rest)

def identityArgument {scope : Scope} : {slot : Slot} → Var scope slot → Argument [] scope slot
  | .value _, binder => .var binder
  | .component _, binder => .input binder
  | .results types, binder => resultTerms binder (Operands.identity types)
  | .tuple types, binder => mapValues (fun position => .read binder position) (Operands.identity types)

def renameArgument {source target : Scope} (rename : Rename source target) :
    {slot : Slot} → Argument [] source slot → Argument [] target slot
  | .value _, term => term.rename rename
  | .component _, component => component.rename rename
  | .results _, terms => Terms.rename rename terms
  | .tuple _, components => mapValues (fun component => component.rename rename) components

def lift {source target : Scope} (substitution : Substitution source target) (bound : Slot) :
    Substitution (bound :: source) (bound :: target)
  | _, .here => identityArgument .here
  | _, .there binder => renameArgument .there (substitution binder)

mutual
  def term {source target : Scope} (substitution : Substitution source target) :
      {ty : Ty} → Term [] source ty → Term [] target ty
    | _, .var binder => substitution binder
    | _, .result binder position => termsAt (substitution binder) position
    | _, .capability service handle => .capability service handle
    | _, .index value => .index value
    | _, .bool value => .bool value
    | _, .field domain value => .field domain value
    | _, .groupZero domain => .groupZero domain
    | _, .calc operation total arguments position => .calc operation total (terms substitution arguments) position
    | _, .law entry _ _ => entry.elim0

  def terms {source target : Scope} (substitution : Substitution source target) :
      {types : List Ty} → Terms [] source types → Terms [] target types
    | _, .nil => .nil
    | _, .cons head tail => .cons (term substitution head) (terms substitution tail)
end

def component {source target : Scope} (substitution : Substitution source target) :
    {ty : Ty} → Comp [] source ty → Comp [] target ty
  | _, .absent => .absent
  | _, .present value => .present (term substitution value)
  | _, .input binder => substitution binder
  | _, .read binder position => (substitution binder).get position

def components {source target : Scope} (substitution : Substitution source target) {types : List Ty}
    (values : Values (Comp [] source) types) : Values (Comp [] target) types :=
  mapValues (component substitution) values

def argument {source target : Scope} (substitution : Substitution source target) :
    {slot : Slot} → Argument [] source slot → Argument [] target slot
  | .value _, value => term substitution value
  | .component _, value => component substitution value
  | .results _, values => terms substitution values
  | .tuple _, values => components substitution values

/-- A shared source body instantiated by one finite typed argument map. -/
def form {callees : List CalleeKey} {source : Scope} {out : List Ty}
    (body : Form [] callees source out) : {target : Scope} → Substitution source target → Form [] callees target out :=
  match body with
  | .done values => fun substitution => .done (components substitution values)
  | .halt reason => fun _ => .halt reason
  | .send ty site peer value next => fun substitution =>
      .send ty site peer (term substitution value) (form next substitution)
  | .receive ty site peer next => fun substitution =>
      .receive ty site peer (form next (lift substitution (.value ty)))
  | .query site request values next => fun substitution =>
      .query site request (terms substitution values) (form next (lift substitution (.value (services.result request))))
  | .split value absent present => fun substitution =>
      .split (component substitution value) (form absent substitution) (form present (lift substitution _))
  | .guard equality left right next => fun substitution =>
      .guard equality (term substitution left) (term substitution right) (form next substitution)
  | .strict helper values next => fun substitution =>
      .strict helper (terms substitution values) (form next (lift substitution (.results helper.outputs)))
  | .compute operation total values next => fun substitution =>
      .compute operation total (terms substitution values) (form next (lift substitution (.results operation.results)))
  | .math helper values next => fun substitution =>
      .math helper (components substitution values) (form next (lift substitution (.tuple helper.outputs)))
  | .byLaw entry _ _ => entry.elim0
  | .owned owner helper values next => fun substitution =>
      .owned owner helper (components substitution values) (form next (lift substitution (.tuple helper.outputs)))
  | .repeat spec site callback count state captures next => fun substitution =>
      .repeat spec site callback (component substitution count) (components substitution state)
        (components substitution captures) (form next (lift substitution (.tuple spec.state)))
  | .apply callee signature roles site values next => fun substitution =>
      .apply callee signature roles site (mapValues (argument substitution) values)
        (form next (lift substitution (.tuple (calleeAt callees callee).signature.outputs)))

section Meaning
variable {model : DomainModel} {source target : Scope}
  (before : Binders model source) (after : Binders model target) (substitution : Substitution source target)
  (related : ∀ {slot : Slot} (binder : Var source slot),
    Argument.eval (LawResults.empty model) (substitution binder) after = before.get binder)

private theorem resultTerms_eval {scope : Scope} {types rest : List Ty}
    (binder : Var scope (.results types)) (positions : Operands types rest) (binders : Binders model scope) :
    Terms.eval (LawResults.empty model) (resultTerms binder positions) binders =
      Operands.eval (binders.get binder).get positions := by
  induction positions with
  | nil => rfl
  | cons position rest ih => simp only [resultTerms, Terms.eval, Term.eval, entryAt_eq_get, Operands.eval, ih]

theorem identityArgument_eval {scope : Scope} {slot : Slot}
    (binder : Var scope slot) (binders : Binders model scope) :
    Argument.eval (LawResults.empty model) (identityArgument binder) binders = binders.get binder := by
  cases slot with
  | value | component => exact entryAt_eq_get _ _
  | results types =>
    rw [identityArgument, Argument.eval, resultTerms_eval]
    exact values_ext fun position => congrFun (congrFun (Operands.get_eval_identity (binders.get binder).get) _) position
  | tuple types =>
    apply values_ext
    intro ty position
    simp only [identityArgument, Argument.eval, comps_get_eval, get_mapValues, Operands.identity_get,
      Comp.eval, entryAt_eq_get]

private theorem renameArgument_eval {scope next : Scope} (rename : Rename scope next)
    (binders : Binders model scope) (newBinders : Binders model next)
    (same : ∀ {slot : Slot} (binder : Var scope slot), newBinders.get (rename binder) = binders.get binder)
    {slot : Slot} (value : Argument [] scope slot) :
    Argument.eval (LawResults.empty model) (renameArgument rename value) newBinders =
      Argument.eval (LawResults.empty model) value binders := by
  cases slot with
  | value => exact term_eval_rename _ rename binders newBinders same _
  | component => exact comp_eval_rename _ rename binders newBinders same _
  | results => exact terms_eval_rename _ rename binders newBinders same _
  | tuple =>
    apply values_ext
    intro ty position
    simp only [renameArgument, Argument.eval, comps_get_eval, get_mapValues]
    exact comp_eval_rename _ rename binders newBinders same _

include related

theorem lift_related {slot : Slot} (value : Slot.Value model slot) :
    ∀ {bound : Slot} (binder : Var (slot :: source) bound),
      Argument.eval (LawResults.empty model) (lift substitution slot binder) (.cons value after) =
        (Values.cons value before).get binder := by
  intro bound binder
  cases binder with
  | here => exact identityArgument_eval _ _
  | there binder => exact (renameArgument_eval .there after (.cons value after) (fun _ => rfl) _).trans (related binder)

omit related in
mutual
  theorem term_eval
      (related : ∀ {slot : Slot} (binder : Var source slot),
        Argument.eval (LawResults.empty model) (substitution binder) after = before.get binder) {ty : Ty} (value : Term [] source ty) :
      (term substitution value).eval (LawResults.empty model) after = value.eval (LawResults.empty model) before := by
    cases value with
    | var binder => simpa only [term, Term.eval, Argument.eval, entryAt_eq_get] using related binder
    | result binder position =>
      rw [term, termsAt_eval, entryAt_eq_get]
      simpa only [Argument.eval, Term.eval, entryAt_eq_get] using
        congrArg (fun values => values.get position) (related binder)
    | capability | index | bool | field | groupZero => rfl
    | «calc» operation total values position =>
      simp only [term, Term.eval, terms_eval related values]
    | law entry => exact entry.elim0

  theorem terms_eval
      (related : ∀ {slot : Slot} (binder : Var source slot),
        Argument.eval (LawResults.empty model) (substitution binder) after = before.get binder) {types : List Ty} (values : Terms [] source types) :
      Terms.eval (LawResults.empty model) (terms substitution values) after =
        Terms.eval (LawResults.empty model) values before := by
    cases values with
    | nil => rfl
    | cons head tail =>
      simp only [terms, Terms.eval, term_eval related head, terms_eval related tail]
end

theorem component_eval {ty : Ty} (value : Comp [] source ty) :
    (component substitution value).eval (LawResults.empty model) after = value.eval (LawResults.empty model) before := by
  cases value with
  | absent => rfl
  | present value => exact congrArg some (term_eval before after substitution related value)
  | input binder => simpa only [component, Comp.eval, Argument.eval, entryAt_eq_get] using related binder
  | read binder position =>
    rw [component, ← comps_get_eval, Comp.eval, entryAt_eq_get]
    exact congrArg (fun values => values.get position) (related binder)

theorem components_eval {types : List Ty} (values : Values (Comp [] source) types) :
    Comps.eval (LawResults.empty model) (components substitution values) after =
      Comps.eval (LawResults.empty model) values before := by
  apply values_ext
  intro ty position
  simp only [components, comps_get_eval, get_mapValues]
  exact component_eval before after substitution related _

theorem argument_eval {slot : Slot} (value : Argument [] source slot) :
    Argument.eval (LawResults.empty model) (argument substitution value) after =
      Argument.eval (LawResults.empty model) value before := by
  cases slot with
  | value => exact term_eval before after substitution related _
  | component => exact component_eval before after substitution related _
  | results => exact terms_eval before after substitution related _
  | tuple => exact components_eval before after substitution related _

theorem arguments_eval {slots : Scope} (values : Values (Argument [] source) slots) :
    Arguments.eval (LawResults.empty model) (mapValues (argument substitution) values) after =
      Arguments.eval (LawResults.empty model) values before := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [mapValues, Arguments.eval, argument_eval before after substitution related value, ih]


theorem form_denoteWith {I : PIR.Signature} {A : Type} {callees : List CalleeKey} {out : List Ty}
    (actions : PIR.OperationInterpretation (Interface model) I) (tables : Tables model I)
    (context : ProtocolContext) (runs : Runs model I) (processes : CalleeProcesses model callees I)
    (leaf : Values (Component model.Value) out → PIR.Process I A) (body : Form [] callees source out) :
    (form body substitution).denoteWithOn model actions tables (LawResults.empty model) context runs processes
        (fun values binders => leaf (Comps.eval (LawResults.empty model) values binders)) after =
      body.denoteWithOn model actions tables (LawResults.empty model) context runs processes
        (fun values binders => leaf (Comps.eval (LawResults.empty model) values binders)) before := by
  induction body generalizing target with
  | done values => exact congrArg leaf (components_eval before after substitution related values)
  | halt => rfl
  | send ty site peer value next ih =>
    simp only [form, Form.denoteWithOn]
    rw [term_eval before after substitution related value]
    exact congrArg (PIR.Process.bind _) (funext fun _ => ih before after substitution related leaf)
  | receive ty site peer next ih =>
    simp only [form, Form.denoteWithOn]
    exact congrArg (PIR.Process.bind _) (funext fun value =>
      ih (.cons value before) (.cons value after) (lift substitution _) (fun binder => lift_related before after substitution related value binder) leaf)
  | query site request values next ih =>
    simp only [form, Form.denoteWithOn]
    rw [terms_eval before after substitution related values]
    exact congrArg (PIR.Process.bind _) (funext fun value =>
      ih (.cons value before) (.cons value after) (lift substitution _) (fun binder => lift_related before after substitution related value binder) leaf)
  | split value absent present absentIH presentIH =>
    simp only [form, Form.denoteWithOn, component_eval before after substitution related value]
    split
    · exact absentIH before after substitution related leaf
    · rename_i value _
      exact presentIH (.cons value before) (.cons value after) (lift substitution _)
        (fun binder => lift_related before after substitution related value binder) leaf
  | guard equality left right next ih =>
    simp only [form, Form.denoteWithOn]
    rw [term_eval before after substitution related left, term_eval before after substitution related right]
    congr 1
    exact ih before after substitution related leaf
  | strict helper values next ih =>
    simp only [form, Form.denoteWithOn]
    rw [terms_eval before after substitution related values]
    exact congrArg (PIR.Process.bind _) (funext fun value =>
      ih (.cons value before) (.cons value after) (lift substitution _) (fun binder => lift_related before after substitution related value binder) leaf)
  | compute operation total values next ih =>
    simp only [form, Form.denoteWithOn]
    rw [terms_eval before after substitution related values]
    exact congrArg (PIR.Process.bind _) (funext fun value =>
      ih (.cons value before) (.cons value after) (lift substitution _) (fun binder => lift_related before after substitution related value binder) leaf)
  | math helper values next ih =>
    simp only [form, Form.denoteWithOn, components_eval before after substitution related values]
    exact congrArg (PIR.Process.bind _) (funext fun value =>
      ih (.cons value before) (.cons value after) (lift substitution _) (fun binder => lift_related before after substitution related value binder) leaf)
  | byLaw entry => exact entry.elim0
  | owned owner helper values next ih =>
    simp only [form, Form.denoteWithOn, components_eval before after substitution related values]
    exact congrArg (PIR.Process.bind _) (funext fun value =>
      ih (.cons value before) (.cons value after) (lift substitution _) (fun binder => lift_related before after substitution related value binder) leaf)
  | «repeat» spec site callback count state captures next ih =>
    simp only [form, Form.denoteWithOn, component_eval before after substitution related count,
      components_eval before after substitution related state, components_eval before after substitution related captures]
    exact congrArg (PIR.Process.bind _) (funext fun value =>
      ih (.cons value before) (.cons value after) (lift substitution _) (fun binder => lift_related before after substitution related value binder) leaf)
  | apply callee signature roles site values next ih =>
    simp only [form, Form.denoteWithOn, arguments_eval before after substitution related values]
    exact congrArg (PIR.Process.bind _) (funext fun value =>
      ih (.cons value before) (.cons value after) (lift substitution _) (fun binder => lift_related before after substitution related value binder) leaf)

theorem form_denote {I : PIR.Signature} {callees : List CalleeKey} {out : List Ty}
    (actions : PIR.OperationInterpretation (Interface model) I) (tables : Tables model I)
    (context : ProtocolContext) (runs : Runs model I) (processes : CalleeProcesses model callees I)
    (body : Form [] callees source out) :
    (form body substitution).denoteOn model actions tables (LawResults.empty model) context runs processes after =
      body.denoteOn model actions tables (LawResults.empty model) context runs processes before :=
  form_denoteWith before after substitution related actions tables context runs processes PIR.Process.done body


omit related in
theorem arguments_related {slots : Scope} (values : Values (Argument [] target) slots)
    (binders : Binders model target) : ∀ {slot : Slot} (binder : Var slots slot),
      Argument.eval (LawResults.empty model) (entryAt values binder) binders =
        (Arguments.eval (LawResults.empty model) values binders).get binder := by
  intro slot binder
  induction binder with
  | here => cases values; rfl
  | there binder ih => cases values with | cons _ rest => exact ih rest

end Meaning
end Zkc.Construction.ConnectionSubstitution
