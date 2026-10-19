module

public import Zkc.Source.Structured.NormalForm.Normalize
public import Zkc.Source.DenotationLaws

@[expose] public section

/-! Soundness of the normalizer, proved once.

If the normalizer returns a form for a body at a role, the body's plain
participant process at that role equals the form's process, for every value
of the form's binders, every protocol context whose roster gives the other
roles different participants, every helper table satisfying the signature's
laws at the body's inputs, and every protocol table. The case analysis of the
participant rules (ownership, presence, masks of restrictions, decided
conditions, literals) happens here, once; an instance only evaluates the
normalizer and compares two processes of the same shape. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace NormalForm

variable {model : DomainModel} {laws : List LawKey}

/-! Values. -/

theorem values_ext {α : Type} {V : α → Type} :
    {types : List α} → {left right : Values V types} →
      (∀ {a : α} (position : Var types a), left.get position = right.get position) → left = right
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons left lefts, .cons right rights, same => by
    have head : left = right := same .here
    have tail : lefts = rights := values_ext fun position => same (.there position)
    rw [head, tail]

theorem get_mapValues {α : Type} {V W : α → Type} (f : {a : α} → V a → W a) :
    {types : List α} → (values : Values V types) → {a : α} → (position : Var types a) →
      (mapValues f values).get position = f (values.get position)
  | _ :: _, .cons _ _, _, .here => rfl
  | _ :: _, .cons _ tail, _, .there position => get_mapValues f tail position

theorem get_setValue_same {α : Type} {V : α → Type} :
    {types : List α} → {a : α} → (values : Values V types) → (position : Var types a) → (value : V a) →
      (setValue values position value).get position = value
  | _ :: _, _, .cons _ _, .here, _ => rfl
  | _ :: _, _, .cons _ tail, .there position, value => get_setValue_same tail position value

theorem var_same?_heq {α : Type} :
    {Γ : List α} → {a b : α} → (left : Var Γ a) → (right : Var Γ b) → (same : a = b) →
      Var.same? left right = some ⟨same⟩ → HEq left right
  | _, _, _, .here, .here, _, _ => HEq.rfl
  | _, _, _, .there left, .there right, same, found => by
    have inner := var_same?_heq left right same found
    subst same
    cases eq_of_heq inner
    exact HEq.rfl
  | _, _, _, .here, .there _, _, found => by simp [Var.same?] at found
  | _, _, _, .there _, .here, _, found => by simp [Var.same?] at found

theorem var_same?_eq {α : Type} {Γ : List α} {a : α} {left right : Var Γ a}
    (found : (Var.same? left right).isSome) : left = right := by
  cases result : Var.same? left right with
  | none => simp [result] at found
  | some same => exact eq_of_heq (var_same?_heq left right same.down (by rw [result]))

/-! Evaluation of components. -/

section Evaluation
variable (results : LawResults model laws)

theorem comps_get_eval {Δ : Scope} :
    {types : List Ty} → (values : Values (Comp laws Δ) types) → (binders : Binders model Δ) →
      {ty : Ty} → (position : Var types ty) →
        (Comps.eval results values binders).get position = (values.get position).eval results binders
  | _ :: _, .cons _ _, _, _, .here => rfl
  | _ :: _, .cons _ tail, binders, _, .there position => comps_get_eval tail binders position

theorem comps_eval_operands {Δ : Scope} {Γ : List Ty} (env : Values (Comp laws Δ) Γ)
    (binders : Binders model Δ) :
    {args : List Ty} → (operands : Operands Γ args) →
      Comps.eval results (Operands.eval env.get operands) binders =
        Operands.eval (Comps.eval results env binders).get operands
  | [], .nil => rfl
  | _ :: _, .cons head tail => by
    simp only [Operands.eval, Comps.eval, comps_get_eval, comps_eval_operands env binders tail]

theorem comps_eval_append {Δ : Scope} (binders : Binders model Δ) :
    {left right : List Ty} → (first : Values (Comp laws Δ) left) → (second : Values (Comp laws Δ) right) →
      Comps.eval results (first.append second) binders =
        (Comps.eval results first binders).append (Comps.eval results second binders)
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons _ tail, second => by
    simp only [Values.append, Comps.eval, comps_eval_append binders tail second]

theorem comps_eval_map {Δ Δ' : Scope} (f : {ty : Ty} → Comp laws Δ ty → Comp laws Δ' ty)
    (binders : Binders model Δ) (binders' : Binders model Δ')
    (preserved : ∀ {ty : Ty} (comp : Comp laws Δ ty), (f comp).eval results binders' = comp.eval results binders) :
    {types : List Ty} → (values : Values (Comp laws Δ) types) →
      Comps.eval results (mapValues f values) binders' = Comps.eval results values binders
  | [], .nil => rfl
  | _ :: _, .cons head tail => by
    simp only [mapValues, Comps.eval, preserved, comps_eval_map f binders binders' preserved tail]

theorem comps_eval_absent {Δ : Scope} (binders : Binders model Δ) :
    (types : List Ty) → Comps.eval results (absentComps (laws := laws) (Δ := Δ) types) binders =
      Values.absent model.Value types
  | [] => rfl
  | _ :: rest => by simp only [absentComps, Comps.eval, Comp.eval, Values.absent, comps_eval_absent binders rest]

theorem comps_eval_set {Δ : Scope} (binders : Binders model Δ) :
    {types : List Ty} → {ty : Ty} → (values : Values (Comp laws Δ) types) → (position : Var types ty) →
      (value : Comp laws Δ ty) → value.eval results binders = (values.get position).eval results binders →
        Comps.eval results (setValue values position value) binders = Comps.eval results values binders
  | _ :: _, _, .cons _ _, .here, _, same => by
    simp only [setValue, Comps.eval]
    rw [same]
    rfl
  | _ :: _, _, .cons _ tail, .there position, value, same => by
    simp only [setValue, Comps.eval]
    rw [comps_eval_set binders tail position value same]

/-- Evaluating the identity positions of a tuple of terms. -/
theorem comps_eval_positions {Δ : Scope} (binders : Binders model Δ) {types : List Ty}
    (term : {ty : Ty} → Var types ty → Term laws Δ ty) (values : Values model.Value types)
    (evaluated : ∀ {ty : Ty} (position : Var types ty), (term position).eval results binders = values.get position) :
    Comps.eval results (mapValues (fun position => .present (term position)) (Operands.identity types)) binders =
      values.present := by
  apply values_ext
  intro ty position
  rw [comps_get_eval, get_mapValues, Operands.identity_get, Values.get_present]
  simp only [Comp.eval, evaluated]

/-! Renaming. -/

mutual
  theorem term_eval_rename {Δ Δ' : Scope} (rename : Rename Δ Δ') (binders : Binders model Δ)
      (binders' : Binders model Δ')
      (renamed : ∀ {slot : Slot} (binder : Var Δ slot), binders'.get (rename binder) = binders.get binder) :
      {ty : Ty} → (term : Term laws Δ ty) → (term.rename rename).eval results binders' = term.eval results binders
    | _, .var binder => by simp only [Term.rename, Term.eval, renamed]
    | _, .result binder position => by simp only [Term.rename, Term.eval, renamed]
    | _, .index _ => rfl
    | _, .bool _ => rfl
    | _, .field .. => rfl
    | _, .groupZero _ => rfl
    | _, .calc op total args position => by
      simp only [Term.rename, Term.eval, terms_eval_rename rename binders binders' renamed args]
    | _, .law entry args position => by
      simp only [Term.rename, Term.eval, terms_eval_rename rename binders binders' renamed args]

  theorem terms_eval_rename {Δ Δ' : Scope} (rename : Rename Δ Δ') (binders : Binders model Δ)
      (binders' : Binders model Δ')
      (renamed : ∀ {slot : Slot} (binder : Var Δ slot), binders'.get (rename binder) = binders.get binder) :
      {types : List Ty} → (terms : Terms laws Δ types) →
        Terms.eval results (Terms.rename rename terms) binders' = Terms.eval results terms binders
    | _, .nil => rfl
    | _, .cons head tail => by
      simp only [Terms.rename, Terms.eval, term_eval_rename rename binders binders' renamed head,
        terms_eval_rename rename binders binders' renamed tail]
end

theorem comp_eval_rename {Δ Δ' : Scope} (rename : Rename Δ Δ') (binders : Binders model Δ)
    (binders' : Binders model Δ')
    (renamed : ∀ {slot : Slot} (binder : Var Δ slot), binders'.get (rename binder) = binders.get binder)
    {ty : Ty} (comp : Comp laws Δ ty) : (comp.rename rename).eval results binders' = comp.eval results binders := by
  cases comp with
  | absent => rfl
  | present term => simp only [Comp.rename, Comp.eval, term_eval_rename results rename binders binders' renamed]
  | input binder => simp only [Comp.rename, Comp.eval, renamed]
  | read binder position => simp only [Comp.rename, Comp.eval, renamed]

theorem comp_eval_weaken {Δ : Scope} {slot : Slot} (value : Slot.Value model slot) (binders : Binders model Δ)
    {ty : Ty} (comp : Comp laws Δ ty) :
    (comp.rename .there).eval results (.cons value binders) = comp.eval results binders :=
  comp_eval_rename results (fun binder => .there binder) binders (.cons value binders) (fun _ => rfl) comp

theorem term_eval_weaken {Δ : Scope} {slot : Slot} (value : Slot.Value model slot) (binders : Binders model Δ)
    {ty : Ty} (term : Term laws Δ ty) :
    (term.rename .there).eval results (.cons value binders) = term.eval results binders :=
  term_eval_rename results (fun binder => .there binder) binders (.cons value binders) (fun _ => rfl) term

/-! Splits. -/

theorem comp_eval_absentAt {Δ : Scope} {ty₀ : Ty} (subject : Var Δ (.component ty₀))
    (binders : Binders model Δ) (absent : binders.get subject = none) {ty : Ty} (comp : Comp laws Δ ty) :
    (comp.absentAt subject).eval results binders = comp.eval results binders := by
  cases comp with
  | input binder =>
    simp only [Comp.absentAt]
    split
    · rename_i same found
      obtain ⟨same⟩ := same
      have sameSort := Slot.component.inj same
      subst sameSort
      cases eq_of_heq (var_same?_heq binder subject same found)
      simp only [Comp.eval, absent]
    · rfl
  | absent => rfl
  | present _ => rfl
  | read _ _ => rfl

theorem comp_eval_presentAt {Δ : Scope} {ty₀ : Ty} (subject : Var Δ (.component ty₀))
    (value : model.Value ty₀) (binders : Binders model Δ) (present : binders.get subject = some value)
    {ty : Ty} (comp : Comp laws Δ ty) :
    (comp.presentAt subject).eval results (.cons value binders) = comp.eval results binders := by
  cases comp with
  | input binder =>
    simp only [Comp.presentAt]
    split
    · rename_i same found
      have sameSort := Slot.component.inj same
      subst sameSort
      cases eq_of_heq (var_same?_heq binder subject same found)
      simp only [Comp.eval, present]
      rfl
    · rfl
  | absent => rfl
  | present term => exact congrArg some (term_eval_weaken results _ binders term)
  | read _ _ => rfl

end Evaluation


/-! Operands, laws and conditions. -/

section Facts
variable (results : LawResults model laws)

theorem presentTerms_eval {Δ : Scope} (binders : Binders model Δ) :
    {types : List Ty} → (values : Values (Comp laws Δ) types) → (terms : Terms laws Δ types) →
      presentTerms values = some terms →
        Comps.eval results values binders = (Terms.eval results terms binders).present
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons head tail, terms, found => by
    cases head with
    | present term =>
      cases rest : presentTerms tail with
      | none => simp [presentTerms, Comp.term?, rest] at found
      | some restTerms =>
        simp only [presentTerms, Comp.term?, rest, Option.some.injEq] at found
        subst found
        simp only [Comps.eval, Comp.eval, Terms.eval, Values.present,
          presentTerms_eval binders tail restTerms rest]
    | absent => simp [presentTerms, Comp.term?] at found
    | input _ => simp [presentTerms, Comp.term?] at found
    | read _ _ => simp [presentTerms, Comp.term?] at found

theorem anyAbsent_sequence {Δ : Scope} (binders : Binders model Δ) :
    {types : List Ty} → (values : Values (Comp laws Δ) types) → anyAbsent values = true →
      RoleFamily.sequence (Comps.eval results values binders) = none
  | [], .nil, found => by simp [anyAbsent] at found
  | _ :: _, .cons head tail, found => by
    cases head with
    | absent => simp [Comps.eval, Comp.eval, RoleFamily.sequence]
    | present term =>
      simp only [anyAbsent, Comp.isAbsent, Bool.false_or] at found
      simp [Comps.eval, RoleFamily.sequence, anyAbsent_sequence binders tail found]
    | input binder =>
      simp only [anyAbsent, Comp.isAbsent, Bool.false_or] at found
      simp [Comps.eval, RoleFamily.sequence, anyAbsent_sequence binders tail found]
    | read binder position =>
      simp only [anyAbsent, Comp.isAbsent, Bool.false_or] at found
      simp [Comps.eval, RoleFamily.sequence, anyAbsent_sequence binders tail found]

theorem term_var?_eval {Δ : Scope} (binders : Binders model Δ) {ty : Ty} (term : Term laws Δ ty)
    (binder : Var Δ (.value ty)) (found : term.var? = some binder) :
    term.eval results binders = binders.get binder := by
  cases term <;> simp [Term.var?] at found
  subst found
  rfl

theorem term_literal?_eval {Δ : Scope} (binders : Binders model Δ) {ty : Ty} (left right : Term laws Δ ty)
    (value : Nat) (first : left.literal? = some value) (second : right.literal? = some value) :
    left.eval results binders = right.eval results binders := by
  cases left <;> simp [Term.literal?] at first <;> cases right <;> simp [Term.literal?] at second
  all_goals first
    | (subst first; subst second; rfl)
    | (rename_i a b
       cases a <;> cases b <;> simp only [Bool.toNat_true, Bool.toNat_false] at first second <;>
         first | rfl | (exfalso; omega))

theorem term_same_eval {Δ : Scope} (binders : Binders model Δ) {ty : Ty} (left right : Term laws Δ ty)
    (same : left.same right = true) : left.eval results binders = right.eval results binders := by
  unfold Term.same at same
  cases leftVar : left.var? with
  | some first =>
    cases rightVar : right.var? with
    | some second =>
      simp only [leftVar, rightVar] at same
      rw [term_var?_eval results binders left first leftVar, term_var?_eval results binders right second rightVar,
        var_same?_eq same]
    | none => simp [leftVar, rightVar] at same
  | none =>
    cases rightVar : right.var? with
    | some second => simp [leftVar, rightVar] at same
    | none =>
      simp only [leftVar, rightVar] at same
      cases leftLiteral : left.literal? with
      | none => simp [leftLiteral] at same
      | some first =>
        cases rightLiteral : right.literal? with
        | none => simp [leftLiteral, rightLiteral] at same
        | some second =>
          simp only [leftLiteral, rightLiteral, beq_iff_eq] at same
          subst same
          exact term_literal?_eval results binders left right first leftLiteral rightLiteral

theorem pinsMatch_pinned {Γ₀ : List Ty} {Δ : Scope} (state : Values (Comp laws Δ) Γ₀)
    (inputs : Values (Component model.Value) Γ₀) (binders : Binders model Δ)
    (evaluated : Comps.eval results state binders = inputs) :
    {types : List Ty} → (pins : List (Option Nat)) → (terms : Terms laws Δ types) →
      pinsMatch state pins terms = true → Pinned inputs pins (Terms.eval results terms binders)
  | [], _, .nil, _ => by simp [Terms.eval, Pinned]
  | _ :: _, [], .cons _ _, _ => by simp [Terms.eval, Pinned]
  | ty :: _, none :: pins, .cons term terms, found => by
    simp only [pinsMatch, Bool.true_and] at found
    exact ⟨trivial, pinsMatch_pinned state inputs binders evaluated pins terms found⟩
  | ty :: _, some index :: pins, .cons term terms, found => by
    simp only [pinsMatch, Bool.and_eq_true] at found
    refine ⟨?_, pinsMatch_pinned state inputs binders evaluated pins terms found.2⟩
    have head := found.1
    show match Var.decode Γ₀ ty index with
      | some binder => inputs.get binder = some (term.eval results binders)
      | none => False
    cases decoded : Var.decode Γ₀ ty index with
    | none => simp [decoded] at head
    | some binder =>
      simp only [decoded] at head ⊢
      split at head
      · rename_i pinned stored
        rw [← evaluated, comps_get_eval, stored, Comp.eval, term_same_eval results binders _ _ head]
      · simp at head

/-- The value of a decided guard condition. -/
theorem decision_holds {Δ : Scope} (binders : Binders model Δ) (condition : Term laws Δ .boolean)
    (decided : decision condition = .holds) : condition.eval results binders = true := by
  cases condition with
  | bool value => cases value <;> simp [decision] at decided; rfl
  | «calc» op total args position =>
    simp only [decision] at decided
    revert decided
    cases op
    all_goals first
      | (intro decided; cases decided)
      | (rcases args with _ | ⟨_, _ | ⟨_, _ | _⟩⟩; intro decided; cases decided)
  | var _ => simp [decision] at decided
  | result _ _ => simp [decision] at decided
  | law _ _ _ => simp [decision] at decided

theorem decision_fails {Δ : Scope} (binders : Binders model Δ) (condition : Term laws Δ .boolean)
    (decided : decision condition = .fails) : condition.eval results binders = false := by
  cases condition with
  | bool value => cases value <;> simp [decision] at decided; rfl
  | «calc» op total args position =>
    simp only [decision] at decided
    revert decided
    cases op
    all_goals first
      | (intro decided; cases decided)
      | (rcases args with _ | ⟨_, _ | ⟨_, _ | _⟩⟩; intro decided; cases decided)
  | var _ => simp [decision] at decided
  | result _ _ => simp [decision] at decided
  | law _ _ _ => simp [decision] at decided

theorem decision_compare {Δ : Scope} (binders : Binders model Δ) (condition : Term laws Δ .boolean)
    {ty : Ty} (equality : Equality ty) (left right : Term laws Δ ty)
    (decided : decision condition = .compare equality left right) :
    condition.eval results binders =
      @decide (left.eval results binders = right.eval results binders) (equality.decide model _ _) := by
  cases condition with
  | bool value => cases value <;> simp [decision] at decided
  | «calc» op total args position =>
    simp only [decision] at decided
    revert decided
    cases op
    all_goals first
      | (intro decided; cases decided)
      | (rcases args with _ | ⟨_, _ | ⟨_, _ | _⟩⟩
         intro decided
         cases decided
         match position with
         | .here => rfl)
  | var _ => simp [decision] at decided
  | result _ _ => simp [decision] at decided
  | law _ _ _ => simp [decision] at decided

end Facts

/-! Calculations. -/

set_option linter.unnecessarySeqFocus false in
theorem operationOn_total (model : DomainModel) {I : PIR.Signature} (observations : SiteObservations I)
    (table : Evaluation.MeaningsOn model.toCarriers I) (op : Op) (total : op.total = true)
    (args : Values model.Value op.arguments) (bodies : Values (RegionFunction model.Value I) op.regions) :
    Evaluation.operationOn model observations table op args bodies = .done (op.evalTotal model total args) := by
  cases op <;> simp [Op.total] at total
  all_goals
    (rcases bodies with _ | _) <;> (rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩) <;> rfl

theorem componentOperationOn_total (model : DomainModel) {I : PIR.Signature}
    (observations : SiteObservations I) (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (op : Op) (total : op.total = true) (args : Values (Component model.Value) op.arguments)
    (bodies : Values (RegionFunction model.Value I) op.regions) :
    Evaluation.componentOperationOn model observations tables op args bodies =
      strictComponent (Evaluation.meaningOn model observations tables.closed) op args bodies := by
  cases op <;> simp [Op.total] at total <;> rfl

theorem calculation_eval (results : LawResults model laws) {Δ : Scope} (binders : Binders model Δ)
    (op : Op) (total : op.total = true) (terms : Terms laws Δ op.arguments) :
    Comps.eval results (calculation op total terms) binders =
      (op.evalTotal model total (Terms.eval results terms binders)).present := by
  cases op
  case fieldConstant domain value =>
    cases terms
    show Comps.eval results (.cons (.present (.field domain value)) .nil) binders = _
    simp only [Comps.eval, Comp.eval, Term.eval, Op.evalTotal, Terms.eval, fieldLiteral_eq]
    rfl
  case indexConstant value => cases terms; rfl
  case booleanConstant value => cases terms; rfl
  case groupIdentity domain => cases terms; rfl
  all_goals
    exact comps_eval_positions results binders (fun position => Term.calc _ total terms position)
      (Op.evalTotal model _ total (Terms.eval results terms binders)) fun _ => rfl

/-! The plain participant rules, one operation at a time. -/

section Rules
variable (model : DomainModel) (tables : Tables model)
  (protocols : ProtocolTable model.Value (Interface model)) (context : ProtocolContext) (self : Nat)

theorem interpret_plain {A : Type} (process : PIR.Proc (Interface model) A) :
    process.interpret (participantActionsOn model.toCarriers) = process :=
  PIR.Proc.interpret_identity process

theorem calculate_absent (op : Op) (allowed : op.isCalculation = true) (total : op.total = true)
    (args : Values (Component model.Value) (ProtocolOp.calculate op allowed).arguments)
    (callbacks : Values (RegionFunction (Component model.Value) (Interface model))
      (ProtocolOp.calculate op allowed).regions)
    (absent : RoleFamily.sequence (Value := model.Value) (types := op.arguments) args = none) :
    protocolOperationWithOn model (SiteObservations.silent (Interface model)) (participantActionsOn model.toCarriers) tables self (.calculate op allowed) args callbacks protocols context =
      .done (Values.absent model.Value op.results) := by
  simp only [protocolOperationWithOn]
  refine (componentOperationOn_total model _ tables op total args _).trans ?_
  unfold strictComponent
  split
  · rfl
  · rename_i values found
    exact absurd (found.symm.trans absent) (by simp)

theorem calculate_present (op : Op) (allowed : op.isCalculation = true) (total : op.total = true)
    (values : Values model.Value op.arguments)
    (callbacks : Values (RegionFunction (Component model.Value) (Interface model))
      (ProtocolOp.calculate op allowed).regions) :
    protocolOperationWithOn model (SiteObservations.silent (Interface model)) (participantActionsOn model.toCarriers) tables self (.calculate op allowed) values.present callbacks protocols context =
      .done (op.evalTotal model total values).present := by
  simp only [protocolOperationWithOn]
  refine (componentOperationOn_total model _ tables op total values.present _).trans ?_
  unfold strictComponent
  split
  · rename_i found
    exact absurd (found.symm.trans (RoleFamily.sequence_present values)) (by simp)
  · rename_i present found
    have same : present = values := Option.some.inj (found.symm.trans (RoleFamily.sequence_present values))
    subst same
    change PIR.Proc.bind (Evaluation.operationOn model _ tables.closed op present _) _ = _
    rw [operationOn_total model _ tables.closed op total]
    rfl

theorem localCall_rule (helper : Helper) (kind : helper.kind = .local) (owner : Nat) (site : String)
    (args : Values (Component model.Value) helper.inputs)
    (callbacks : Values (RegionFunction (Component model.Value) (Interface model))
      (ProtocolOp.localCall helper kind owner site).regions) :
    protocolOperationWithOn model (SiteObservations.silent (Interface model)) (participantActionsOn model.toCarriers) tables self (.localCall helper kind owner site) args callbacks protocols context =
      Participant.owned self (context.roles owner) (invoke tables.closed helper) args := rfl

theorem exchange_rule (ty : Ty) (sender receiver : Nat) (site : String) (value : Option (model.Value ty))
    (callbacks : Values (RegionFunction (Component model.Value) (Interface model))
      (ProtocolOp.exchange ty sender receiver site).regions) :
    protocolOperationWithOn model (SiteObservations.silent (Interface model)) (participantActionsOn model.toCarriers) tables self (.exchange ty sender receiver site) (.cons value .nil) callbacks protocols context =
      ((Participant.exchange (services := services) self (context.roles sender) (context.roles receiver)
        (qualifyProtocolSite context.applicationPrefix site) value).interpret
          (participantActionsOn model.toCarriers)).bind fun result => .done (.cons result .nil) := rfl

theorem restrict_rule (ty : Ty) (roles : List Nat) (value : Option (model.Value ty))
    (callbacks : Values (RegionFunction (Component model.Value) (Interface model))
      (ProtocolOp.restrict ty roles).regions) :
    protocolOperationWithOn model (SiteObservations.silent (Interface model)) (participantActionsOn model.toCarriers) tables self (.restrict ty roles) (.cons value .nil) callbacks protocols context =
      .done (.cons (Participant.restrict ((roles.map context.roles).contains self) value) .nil) := rfl

theorem draw_rule (owner : Nat) (field site : String)
    (args : Values (Component model.Value) (ProtocolOp.draw owner field site).arguments)
    (callbacks : Values (RegionFunction (Component model.Value) (Interface model))
      (ProtocolOp.draw owner field site).regions) :
    protocolOperationWithOn model (SiteObservations.silent (Interface model)) (participantActionsOn model.toCarriers) tables self (.draw owner field site) args callbacks protocols context =
      ((Participant.query (services := services) self (context.roles owner)
        (qualifyProtocolSite context.applicationPrefix site) field args).interpret
          (participantActionsOn model.toCarriers)).bind fun result => .done (.cons result .nil) := rfl

theorem guard_rule (owner : Nat) (site : String) (condition : Option Bool)
    (callbacks : Values (RegionFunction (Component model.Value) (Interface model))
      (ProtocolOp.guard owner site).regions) :
    protocolOperationWithOn model (SiteObservations.silent (Interface model)) (participantActionsOn model.toCarriers) tables self (.guard owner site) (.cons condition .nil) callbacks protocols context =
      ((Participant.guard (services := services) (Value := model.Value) self (context.roles owner)
        condition).interpret (participantActionsOn model.toCarriers)).bind fun _ => .done .nil := rfl

theorem mark_rule (site : String)
    (callbacks : Values (RegionFunction (Component model.Value) (Interface model))
      (ProtocolOp.mark site).regions) :
    protocolOperationWithOn model (SiteObservations.silent (Interface model)) (participantActionsOn model.toCarriers) tables self (.mark site) .nil callbacks protocols context = .done .nil := rfl

theorem statement_rule (relation : String) (types : List Ty) (selectors : List String) (acceptance : Nat)
    (args : Values (Component model.Value) (ProtocolOp.statement relation types selectors acceptance).arguments)
    (callbacks : Values (RegionFunction (Component model.Value) (Interface model))
      (ProtocolOp.statement relation types selectors acceptance).regions) :
    protocolOperationWithOn model (SiteObservations.silent (Interface model)) (participantActionsOn model.toCarriers) tables self (.statement relation types selectors acceptance) args callbacks protocols context = .done .nil := rfl

theorem owned_absent {I : PIR.Signature} {inputs outputs : List Ty} (self : Nat)
    (work : Values model.Value inputs → PIR.Proc I (Values model.Value outputs))
    (args : Values (Component model.Value) inputs) (absent : RoleFamily.sequence args = none) :
    Participant.owned self self work args = .halt .incomplete := by
  simp [Participant.owned, absent]

end Rules

/-! The main theorem. -/

theorem bind_congr_left {I : PIR.Signature} {A B : Type} {first second : PIR.Proc I A}
    (same : first = second) (next : A → PIR.Proc I B) : first.bind next = second.bind next := by
  rw [same]

theorem except_bind_ok {ε α β : Type} (value : α) (f : α → Except ε β) :
    (Except.ok value >>= f) = f value := rfl

theorem except_bind_error {ε α β : Type} (error : ε) (f : α → Except ε β) :
    (Except.error error >>= f) = .error error := rfl

theorem except_bind_ok_inv {ε α β : Type} {first : Except ε α} {f : α → Except ε β} {result : β}
    (found : (first >>= f) = .ok result) : ∃ value, first = .ok value ∧ f value = .ok result := by
  cases first with
  | error refusal => cases found
  | ok value => exact ⟨value, rfl, found⟩

section Main
variable (model : DomainModel) (tables : Tables model)
  (protocols : ProtocolTable model.Value (Interface model)) (context : ProtocolContext)

/-- The plain participant meaning, with silent sites, at the participant the
context gives a roster index. -/
abbrev meaningAt (role : Nat) : RegionMeaning protocolDialect (Interface model) :=
  participantMeaningWithOn model (.silent (Interface model)) (participantActionsOn model.toCarriers)
    tables (context.roles role) protocols context

/-- Every form a normalization step returns from a state denotes the region's
process at the state's environment, whenever the state's inputs are the body's
and the form's law uses are calls of the laws' own helpers. -/
def Continues (sig : Signature) (results : LawResults model sig.laws) (role : Nat)
    {Γ₀ Γ out : List Ty} (inputs : Values (Component model.Value) Γ₀) (region : Region protocolDialect Γ out)
    (normalized : {Δ : Scope} → State sig.laws Γ₀ Δ Γ → Except Refusal (Form sig.laws Δ out)) : Prop :=
  ∀ {Δ : Scope} (state : State sig.laws Γ₀ Δ Γ) (form : Form sig.laws Δ out), normalized state = .ok form →
    form.LawsMatch → ∀ binders : Binders model Δ, Comps.eval results state.inputs binders = inputs →
      region.denote (meaningAt model tables protocols context role) (Comps.eval results state.env binders).get =
        form.denote model tables results context binders

variable {model tables protocols context}

theorem state_map_eval (results : LawResults model laws) {Γ₀ Γ : List Ty} {Δ Δ' : Scope}
    (f : {ty : Ty} → Comp laws Δ ty → Comp laws Δ' ty) (binders : Binders model Δ)
    (binders' : Binders model Δ')
    (preserved : ∀ {ty : Ty} (comp : Comp laws Δ ty), (f comp).eval results binders' = comp.eval results binders)
    (state : State laws Γ₀ Δ Γ) :
    Comps.eval results (state.map f).inputs binders' = Comps.eval results state.inputs binders ∧
      Comps.eval results (state.map f).env binders' = Comps.eval results state.env binders :=
  ⟨comps_eval_map results f binders binders' preserved state.inputs,
    comps_eval_map results f binders binders' preserved state.env⟩

theorem resolve_sound (sig : Signature) (results : LawResults model sig.laws) (role : Nat)
    {Γ₀ Γ out : List Ty} (inputs : Values (Component model.Value) Γ₀) (region : Region protocolDialect Γ out)
    (op : ProtocolOp) (args : Operands Γ op.arguments)
    (proceed : {Δ : Scope} → State sig.laws Γ₀ Δ Γ → Except Refusal (Form sig.laws Δ out))
    (sound : Continues model tables protocols context sig results role inputs region proceed) (fuel : Nat) :
    Continues model tables protocols context sig results role inputs region
      (fun state => resolve sig role op args fuel state proceed) := by
  induction fuel with
  | zero => exact sound
  | succ fuel ih =>
    intro Δ state form normalized matched binders inputsEq
    simp only [resolve] at normalized
    split at normalized
    · split at normalized
      · exact sound state form normalized matched binders inputsEq
      · rename_i ty subject _
        cases absentResult : resolve sig role op args fuel (state.map (Comp.absentAt subject)) proceed with
        | error refusal => rw [absentResult, except_bind_error] at normalized; cases normalized
        | ok absentForm =>
          cases presentResult : resolve sig role op args fuel (state.map (Comp.presentAt subject)) proceed with
          | error refusal =>
            rw [absentResult, except_bind_ok, presentResult, except_bind_error] at normalized
            cases normalized
          | ok presentForm =>
            rw [absentResult, except_bind_ok, presentResult, except_bind_ok] at normalized
            cases normalized
            simp only [Form.denote, Form.denoteWith, Comp.eval]
            cases value : binders.get subject with
            | none =>
              have preserved := state_map_eval results (Comp.absentAt subject) binders binders
                (comp_eval_absentAt results subject binders value) state
              have step := ih (state.map (Comp.absentAt subject)) absentForm absentResult matched.1 binders
                (preserved.1.trans inputsEq)
              rw [preserved.2] at step
              exact step
            | some present =>
              have preserved := state_map_eval results (Comp.presentAt subject) binders (.cons present binders)
                (comp_eval_presentAt results subject present binders value) state
              have step := ih (state.map (Comp.presentAt subject)) presentForm presentResult matched.2
                (.cons present binders) (preserved.1.trans inputsEq)
              rw [preserved.2] at step
              exact step
    · exact sound state form normalized matched binders inputsEq

theorem continue_push (sig : Signature) (results : LawResults model sig.laws) (role : Nat)
    {Γ₀ Γ out types : List Ty} (inputs : Values (Component model.Value) Γ₀)
    (nextRegion : Region protocolDialect (types ++ Γ) out)
    (next : {Δ : Scope} → State sig.laws Γ₀ Δ (types ++ Γ) → Except Refusal (Form sig.laws Δ out))
    (sound : Continues model tables protocols context sig results role inputs nextRegion next)
    {Δ : Scope} (state : State sig.laws Γ₀ Δ Γ) (added : Values (Comp sig.laws Δ) types)
    (form : Form sig.laws Δ out) (normalized : next (state.push added) = .ok form) (matched : form.LawsMatch)
    (binders : Binders model Δ)
    (inputsEq : Comps.eval results state.inputs binders = inputs) (values : Values (Component model.Value) types)
    (evaluated : Comps.eval results added binders = values) :
    nextRegion.denote (meaningAt model tables protocols context role)
        (values.append (Comps.eval results state.env binders)).get =
      form.denote model tables results context binders := by
  have step := sound (state.push added) form normalized matched binders inputsEq
  simp only [State.push, comps_eval_append, evaluated] at step
  exact step

theorem continue_weaken_push (sig : Signature) (results : LawResults model sig.laws) (role : Nat)
    {Γ₀ Γ out types : List Ty} (inputs : Values (Component model.Value) Γ₀)
    (nextRegion : Region protocolDialect (types ++ Γ) out)
    (next : {Δ : Scope} → State sig.laws Γ₀ Δ (types ++ Γ) → Except Refusal (Form sig.laws Δ out))
    (sound : Continues model tables protocols context sig results role inputs nextRegion next)
    {Δ : Scope} (state : State sig.laws Γ₀ Δ Γ) (slot : Slot) (value : Slot.Value model slot)
    (added : Values (Comp sig.laws (slot :: Δ)) types)
    (form : Form sig.laws (slot :: Δ) out) (normalized : next ((state.weaken slot).push added) = .ok form)
    (matched : form.LawsMatch) (binders : Binders model Δ)
    (inputsEq : Comps.eval results state.inputs binders = inputs)
    (values : Values (Component model.Value) types)
    (evaluated : Comps.eval results added (.cons value binders) = values) :
    nextRegion.denote (meaningAt model tables protocols context role)
        (values.append (Comps.eval results state.env binders)).get =
      form.denote model tables results context (.cons value binders) := by
  have preserved := state_map_eval results (Comp.rename .there) binders (.cons value binders)
    (comp_eval_weaken results value binders) state
  have step := sound ((state.weaken slot).push added) form normalized matched (.cons value binders)
    (preserved.1.trans inputsEq)
  simp only [State.push, comps_eval_append, evaluated] at step
  rw [State.weaken, preserved.2] at step
  exact step

theorem restrict_contains {context : ProtocolContext} {role roster : Nat}
    (distinct : RosterDistinct context role roster) (roles : List Nat)
    (bounded : roles.any (roster ≤ ·) = false) :
    (roles.map context.roles).contains (context.roles role) = roles.contains role := by
  induction roles with
  | nil => rfl
  | cons head rest ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at bounded
    simp only [List.map_cons, List.contains_cons, ih bounded.2]
    by_cases same : head = role
    · subst same
      simp
    · have different := distinct head bounded.1 same
      rw [beq_eq_false_iff_ne.mpr (Ne.symm different), beq_eq_false_iff_ne.mpr (Ne.symm same)]

theorem operation_sound (sig : Signature) (results : LawResults model sig.laws) (role roster : Nat)
    (distinct : RosterDistinct context role roster) {Γ₀ : List Ty} (inputs : Values (Component model.Value) Γ₀)
    (lawsHold : LawsHold tables results inputs) {Γ out : List Ty} (op : ProtocolOp)
    (args : Operands Γ op.arguments) (bodies : Regions protocolDialect op.regions)
    (nextRegion : Region protocolDialect (op.results ++ Γ) out)
    (next : {Δ : Scope} → State sig.laws Γ₀ Δ (op.results ++ Γ) → Except Refusal (Form sig.laws Δ out))
    (sound : Continues model tables protocols context sig results role inputs nextRegion next) :
    Continues model tables protocols context sig results role inputs (.letOp op args bodies nextRegion)
      (fun state => operation sig role roster op args state next) := by
  intro Δ state form normalized matched binders inputsEq
  rw [Region.denote_letOp_values]
  change (protocolOperationWithOn model (.silent _) (participantActionsOn model.toCarriers) tables
    (context.roles role) op (Operands.eval (Comps.eval results state.env binders).get args)
    (bodies.denote (meaningAt model tables protocols context role)) protocols context).bind _ = _
  rw [← comps_eval_operands]
  cases op with
  | calculate op allowed =>
    simp only [operation] at normalized
    split at normalized
    · rename_i total
      split at normalized
      · rename_i absent
        refine (bind_congr_left (calculate_absent model tables protocols context _ op allowed total _ _
          (anyAbsent_sequence results binders _ absent)) _).trans ?_
        exact continue_push sig results role inputs nextRegion next sound state _ form normalized matched binders inputsEq
          _ (comps_eval_absent results binders op.results)
      · split at normalized
        · cases normalized
        · rename_i terms found
          rw [presentTerms_eval results binders _ terms found]
          refine (bind_congr_left (calculate_present model tables protocols context _ op allowed total _ _) _).trans ?_
          exact continue_push sig results role inputs nextRegion next sound state _ form normalized matched binders inputsEq
            _ (calculation_eval results binders op total terms)
    · cases normalized
  | localCall helper kind owner site =>
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i inRoster
      refine (bind_congr_left (localCall_rule model tables protocols context _ helper kind owner site _ _) _).trans ?_
      split at normalized
      · rename_i other
        have different : context.roles owner ≠ context.roles role :=
          distinct owner (by omega) (by simpa using other)
        refine (bind_congr_left (Participant.owned_other _ _ different _ _) _).trans ?_
        exact continue_push sig results role inputs nextRegion next sound state _ form normalized matched binders inputsEq
          _ (comps_eval_absent results binders helper.outputs)
      · rename_i own
        have same : owner = role := by simpa using own
        subst same
        split at normalized
        · rename_i absent
          cases normalized
          refine (bind_congr_left (owned_absent model _ _ _ (anyAbsent_sequence results binders _ absent)) _).trans ?_
          rfl
        · split at normalized
          · cases normalized
          · rename_i terms found
            rw [presentTerms_eval results binders _ terms found]
            refine (bind_congr_left (Participant.owned_present _ _ _) _).trans ?_
            split at normalized
            · rename_i entry inputsSame outputsSame lawFound
              split at normalized
              · rename_i pinned
                split at normalized
                · rename_i shape
                  obtain ⟨restForm, rest, built⟩ := except_bind_ok_inv normalized
                  cases built
                  obtain ⟨same, restMatched⟩ := matched
                  subst same
                  have law := lawsHold entry (Terms.eval results terms binders)
                    (pinsMatch_pinned results state.inputs inputs binders inputsEq _ _ pinned)
                  simp only [shape] at law
                  refine (bind_congr_left (bind_congr_left law _) _).trans ?_
                  exact continue_push sig results _ inputs nextRegion next sound state _ restForm rest restMatched
                    binders inputsEq _ (comps_eval_positions results binders _ _ fun _ => rfl)
                · rename_i reason shape
                  cases normalized
                  obtain ⟨same, _⟩ := matched
                  subst same
                  have law := lawsHold entry (Terms.eval results terms binders)
                    (pinsMatch_pinned results state.inputs inputs binders inputsEq _ _ pinned)
                  simp only [shape] at law
                  refine (bind_congr_left (bind_congr_left law _) _).trans ?_
                  rfl
              · cases normalized
            · split at normalized
              · cases rest : next ((state.weaken (.results helper.outputs)).push
                  (mapValues (fun position => .present (.result .here position)) (Operands.identity helper.outputs)))
                  with
                | error refusal => rw [rest, except_bind_error] at normalized; cases normalized
                | ok restForm =>
                  rw [rest, except_bind_ok] at normalized
                  cases normalized
                  refine (PIR.Proc.bind_assoc _ _ _).trans ?_
                  simp only [Form.denote, Form.denoteWith]
                  apply congrArg
                  funext values
                  exact continue_weaken_push sig results _ inputs nextRegion next sound state _ values _
                    restForm rest matched binders inputsEq _ (comps_eval_positions results _ _ _ fun _ => rfl)
              · cases normalized
  | exchange ty sender receiver site =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i bounded
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at bounded
      refine (bind_congr_left (exchange_rule model tables protocols context _ ty sender receiver site _ _) _).trans ?_
      rw [interpret_plain]
      split at normalized
      · rename_i isSender
        have same : sender = role := by simpa using isSender
        subst same
        split at normalized
        · rename_i stored
          cases normalized
          simp [Participant.exchange, stored, Comp.eval, PIR.Proc.bind, Form.denote, Form.denoteWith]
        · rename_i term stored
          cases rest : next (state.push (.cons (.present term) .nil)) with
          | error refusal => rw [rest, except_bind_error] at normalized; cases normalized
          | ok restForm =>
            rw [rest, except_bind_ok] at normalized
            cases normalized
            simp only [Participant.exchange, stored, Comp.eval, ite_true, PIR.Proc.bind, Form.denote,
              Form.denoteWith]
            apply congrArg
            funext reply
            exact continue_push sig results _ inputs nextRegion next sound state _ restForm rest matched binders inputsEq
              _ rfl
        · cases normalized
      · rename_i notSender
        have different : context.roles sender ≠ context.roles role :=
          distinct sender bounded.1 (by simpa using notSender)
        split at normalized
        · rename_i isReceiver
          have same : receiver = role := by simpa using isReceiver
          subst same
          cases rest : next ((state.weaken (.value ty)).push (.cons (.present (.var .here)) .nil)) with
          | error refusal => rw [rest, except_bind_error] at normalized; cases normalized
          | ok restForm =>
            rw [rest, except_bind_ok] at normalized
            cases normalized
            simp only [Participant.exchange, different, ite_false, ite_true, PIR.Proc.bind, Form.denote,
              Form.denoteWith]
            apply congrArg
            funext reply
            exact continue_weaken_push sig results _ inputs nextRegion next sound state _ reply _ restForm rest
              matched binders inputsEq _ rfl
        · rename_i notReceiver
          have otherReceiver : context.roles receiver ≠ context.roles role :=
            distinct receiver bounded.2 (by simpa using notReceiver)
          simp only [Participant.exchange, different, otherReceiver, ite_false, PIR.Proc.bind]
          exact continue_push sig results role inputs nextRegion next sound state _ form normalized matched binders inputsEq
            _ rfl
  | restrict ty roles =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i bounded
      have contains := restrict_contains distinct roles (by simpa using bounded)
      refine (bind_congr_left (restrict_rule model tables protocols context _ ty roles _ _) _).trans ?_
      simp only [contains, PIR.Proc.bind]
      split at normalized
      · rename_i member
        simp only [member, Participant.restrict, ite_true]
        exact continue_push sig results role inputs nextRegion next sound state _ form normalized matched binders inputsEq
          _ rfl
      · rename_i notMember
        simp only [Participant.restrict, Bool.not_eq_true] at notMember ⊢
        simp only [notMember, Bool.false_eq_true, ite_false]
        exact continue_push sig results role inputs nextRegion next sound state _ form normalized matched binders inputsEq
          _ rfl
  | draw owner field site =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i bounded
      refine (bind_congr_left (draw_rule model tables protocols context _ owner field site _ _) _).trans ?_
      rw [interpret_plain]
      simp only [Operands.eval]
      split at normalized
      · rename_i other
        have different : context.roles owner ≠ context.roles role :=
          distinct owner (by omega) (by simpa using other)
        simp only [Participant.query, different, ite_false, PIR.Proc.bind]
        exact continue_push sig results role inputs nextRegion next sound state _ form normalized matched binders inputsEq
          _ rfl
      · rename_i own
        have same : owner = role := by simpa using own
        subst same
        split at normalized
        · rename_i stored
          cases normalized
          simp only [Participant.query, ite_true, stored]
          rfl
        · rename_i handle stored
          cases rest : next ((state.weaken (.value (services.result field))).push (.cons (.present (.var .here)) .nil))
            with
          | error refusal => rw [rest, except_bind_error] at normalized; cases normalized
          | ok restForm =>
            rw [rest, except_bind_ok] at normalized
            cases normalized
            simp only [Participant.query, ite_true, stored]
            refine congrArg (PIR.Proc.call _) (funext fun reply => ?_)
            exact continue_weaken_push sig results _ inputs nextRegion next sound state _ reply _ restForm rest
              matched binders inputsEq _ rfl
        · cases normalized
  | guard owner site =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i bounded
      refine (bind_congr_left (guard_rule model tables protocols context _ owner site _ _) _).trans ?_
      rw [interpret_plain]
      split at normalized
      · rename_i other
        have different : context.roles owner ≠ context.roles role :=
          distinct owner (by omega) (by simpa using other)
        simp only [Participant.guard, different, ite_false, PIR.Proc.bind]
        exact continue_push sig results role inputs nextRegion next sound state _ form normalized matched binders inputsEq
          _ rfl
      · rename_i own
        have same : owner = role := by simpa using own
        subst same
        split at normalized
        · rename_i stored
          cases normalized
          simp [Participant.guard, stored, Comp.eval, PIR.Proc.bind, Form.denote, Form.denoteWith]
        · rename_i condition stored
          split at normalized
          · rename_i decided
            simp only [Participant.guard, stored, Comp.eval, decision_holds results binders condition decided,
              ite_true, PIR.Proc.bind]
            exact continue_push sig results _ inputs nextRegion next sound state _ form normalized matched binders inputsEq
              _ rfl
          · rename_i decided
            cases normalized
            simp [Participant.guard, stored, Comp.eval, decision_fails results binders condition decided,
              PIR.Proc.bind, Form.denote, Form.denoteWith]
          · rename_i ty equality left right decided
            cases rest : next ((state.set arg (.present (.bool true))).push .nil) with
            | error refusal => rw [rest, except_bind_error] at normalized; cases normalized
            | ok restForm =>
              rw [rest, except_bind_ok] at normalized
              cases normalized
              simp only [Participant.guard, stored, Comp.eval, decision_compare results binders condition equality
                left right decided, ite_true, Form.denote, Form.denoteWith]
              by_cases holds : left.eval results binders = right.eval results binders
              · simp only [holds, decide_true, ite_true]
                have kept : Comps.eval results (state.set arg (.present (.bool true))).env binders =
                    Comps.eval results state.env binders :=
                  comps_eval_set results binders state.env arg _ (by
                    simp only [stored, Comp.eval, Term.eval, decision_compare results binders condition equality
                      left right decided, holds, decide_true])
                have step := continue_push sig results _ inputs nextRegion next sound
                  (state.set arg (.present (.bool true))) .nil restForm rest matched binders inputsEq _ rfl
                rw [kept] at step
                exact step
              · simp only [holds, decide_false, Bool.false_eq_true, ite_false]
                rfl
          · cases normalized
        · cases normalized
  | statement relation types selectors acceptance =>
    simp only [operation] at normalized
    refine (bind_congr_left (statement_rule model tables protocols context _ relation types selectors acceptance
      _ _) _).trans ?_
    exact continue_push sig results role inputs nextRegion next sound state _ form normalized matched binders inputsEq _ rfl
  | mark site =>
    rcases args with _ | _
    simp only [operation] at normalized
    refine (bind_congr_left (mark_rule model tables protocols context _ site _) _).trans ?_
    exact continue_push sig results role inputs nextRegion next sound state _ form normalized matched binders inputsEq _ rfl
  | protocolApply => simp only [operation] at normalized; cases normalized
  | «repeat» => simp only [operation] at normalized; cases normalized

theorem normalizeRegion_sound (sig : Signature) (results : LawResults model sig.laws) (role roster : Nat)
    (distinct : RosterDistinct context role roster) {Γ₀ : List Ty} (inputs : Values (Component model.Value) Γ₀)
    (lawsHold : LawsHold tables results inputs) {out : List Ty} :
    {Γ : List Ty} → (region : Region protocolDialect Γ out) →
      Continues model tables protocols context sig results role inputs region
        (fun state => normalizeRegion sig role roster region state)
  | _, .ret values => by
    intro state form normalized _ binders _
    simp only [normalizeRegion, Except.ok.injEq] at normalized
    subst normalized
    simp only [Region.denote, Form.denote, Form.denoteWith, comps_eval_operands]
  | _, .stop reason => by
    intro state form normalized _ binders _
    simp only [normalizeRegion, Except.ok.injEq] at normalized
    subst normalized
    rfl
  | _, .letOp op args bodies next => by
    intro state form normalized matched binders inputsEq
    exact resolve_sound sig results role inputs (.letOp op args bodies next) op args _
      (operation_sound sig results role roster distinct inputs lawsHold op args bodies next _
        (normalizeRegion_sound sig results role roster distinct inputs lawsHold next))
      _ state form normalized matched binders inputsEq
  | _, .bind body next => by
    intro state form normalized
    simp [normalizeRegion] at normalized

theorem initialIn_eval (results : LawResults model laws) {Δ : Scope} (binders' : Binders model Δ) :
    {Γ : List Ty} → (pattern : InputPattern Γ) → (lift : Rename pattern.scope Δ) →
      (binders : Binders model pattern.scope) →
      (∀ {slot : Slot} (binder : Var pattern.scope slot), binders'.get (lift binder) = binders.get binder) →
      Comps.eval results (pattern.initialIn (laws := laws) lift) binders' = pattern.environment model binders
  | [], .nil, _, _, _ => rfl
  | ty :: _, .cons .present rest, lift, binders, placed => by
    have step : ∀ (lift : Rename (.value ty :: InputPattern.scope rest) Δ)
        (values : Values (Slot.Value model) (.value ty :: InputPattern.scope rest)),
        (∀ {slot : Slot} (binder : Var (.value ty :: InputPattern.scope rest) slot),
          binders'.get (lift binder) = values.get binder) →
        Comps.eval results (InputPattern.initialIn (laws := laws) (.cons (Input.present (ty := ty)) rest) lift)
            binders' =
          InputPattern.environment model (.cons (Input.present (ty := ty)) rest) values := by
      intro lift values placed
      cases values with
      | cons value tail =>
        change Values.cons (some (binders'.get (lift .here))) (Comps.eval results (InputPattern.initialIn
            (laws := laws) rest fun binder => lift (.there binder)) binders') =
          Values.cons (some value) (InputPattern.environment model rest tail)
        rw [placed .here, initialIn_eval results binders' rest _ tail fun binder => placed (.there binder)]
        rfl
    exact step lift binders placed
  | ty :: _, .cons .optional rest, lift, binders, placed => by
    have step : ∀ (lift : Rename (.component ty :: InputPattern.scope rest) Δ)
        (values : Values (Slot.Value model) (.component ty :: InputPattern.scope rest)),
        (∀ {slot : Slot} (binder : Var (.component ty :: InputPattern.scope rest) slot),
          binders'.get (lift binder) = values.get binder) →
        Comps.eval results (InputPattern.initialIn (laws := laws) (.cons (Input.optional (ty := ty)) rest) lift)
            binders' =
          InputPattern.environment model (.cons (Input.optional (ty := ty)) rest) values := by
      intro lift values placed
      cases values with
      | cons value tail =>
        change (Values.cons (binders'.get (lift .here)) (Comps.eval results (InputPattern.initialIn
            (laws := laws) rest fun binder => lift (.there binder)) binders') : Values (Component model.Value) _) =
          (Values.cons value (InputPattern.environment model rest tail) : Values (Component model.Value) _)
        rw [placed .here, initialIn_eval results binders' rest _ tail fun binder => placed (.there binder)]
        rfl
    exact step lift binders placed
  | _ :: _, .cons .absent rest, lift, binders, placed =>
    congrArg (Values.cons _) (initialIn_eval results binders' rest lift binders placed)
  | _ :: _, .cons (.index _) rest, lift, binders, placed =>
    congrArg (Values.cons _) (initialIn_eval results binders' rest lift binders placed)
  | _ :: _, .cons (.field ..) rest, lift, binders, placed =>
    congrArg (Values.cons _) (initialIn_eval results binders' rest lift binders placed)
  | _ :: _, .cons (.bool _) rest, lift, binders, placed =>
    congrArg (Values.cons _) (initialIn_eval results binders' rest lift binders placed)

theorem initial_eval (results : LawResults model laws) {Γ : List Ty} (pattern : InputPattern Γ)
    (binders : Binders model pattern.scope) :
    Comps.eval results (pattern.initial (laws := laws)) binders = pattern.environment model binders :=
  initialIn_eval results binders pattern _ binders fun _ => rfl

/-- **Soundness of the normalizer.** If the normalizer returns a form for a body
at a role, the body's plain participant process at that role, on the inputs the
pattern's binders give, is the form's process, for every value of the binders.
The premises are visible: every law use of the form is a call of the law's
own helper, the roster gives the other roles different participants, and the
helper tables satisfy every law of the signature at these inputs. The protocol
table and the context are arbitrary. -/
theorem normalize_sound (sig : Signature) {Γ out : List Ty} (body : Region protocolDialect Γ out)
    (role roster : Nat) (pattern : InputPattern Γ) (form : Form sig.laws pattern.scope out)
    (normalized : normalize sig body role roster pattern = .ok form) (matched : form.CallsMatch)
    (distinct : RosterDistinct context role roster) (results : LawResults model sig.laws)
    (binders : Binders model pattern.scope)
    (lawsHold : LawsHold tables results (pattern.environment model binders)) :
    body.denote (meaningAt model tables protocols context role) (pattern.environment model binders).get =
      form.denote model tables results context binders := by
  have initial := initial_eval (laws := sig.laws) results pattern binders
  have sound := normalizeRegion_sound (protocols := protocols) sig results role roster distinct
    (pattern.environment model binders) lawsHold body ⟨pattern.initial, pattern.initial⟩ form normalized
    (form.lawsMatch_of_callsMatch matched) binders initial
  rw [initial] at sound
  exact sound

end Main

end NormalForm
end Zkc.Source.Structured
