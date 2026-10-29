module

public import Zkc.Source.Structured.NormalForm.Normalize
public import Zkc.Source.DenotationLaws

@[expose] public section

/-! Soundness of the normalizer, proved once.

If normalization returns a form for a typed body at a role, the body's
observation-parametric participant process equals the form's process. This
holds for all binders, action interpretations, iteration observations, contexts
with distinct roster coordinates, helper tables satisfying the input-pinned
laws, and callee tables satisfying their exact semantic equations.

The participant rule analysis happens here once. Call contexts and retained
repeat sites pass to the existing source interpreter, which supplies actual
dynamic iteration coordinates. The plain theorem is a silent specialization. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace NormalForm

variable {model : DomainModel} {laws : List LawKey} {callees : List CalleeKey}

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

theorem var_same?_heq {α : Type} {Γ : List α} {a b : α} (left : Var Γ a) (right : Var Γ b) (same : a = b)
    (found : Var.same? left right = some ⟨same⟩) : HEq left right := by
  unfold Var.same? at found
  split at found
  · rename_i equal
    exact (Var.index_heq left right equal).2
  · cases found

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
    simp only [setValue, Comps.eval, laterEntries_cons]
    rw [same]
    rfl
  | _ :: _, _, .cons _ tail, .there position, value, same => by
    simp only [setValue, Comps.eval, firstEntry_cons, laterEntries_cons]
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
    | _, .var binder => by simp only [Term.rename, Term.eval, entryAt_eq_get, renamed]
    | _, .result binder position => by simp only [Term.rename, Term.eval, entryAt_eq_get, renamed]
    | _, .capability .. => rfl
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
  | input binder => simp only [Comp.rename, Comp.eval, entryAt_eq_get, renamed]
  | read binder position => simp only [Comp.rename, Comp.eval, entryAt_eq_get, renamed]

theorem comp_eval_weaken {Δ : Scope} {slot : Slot} (value : Slot.Value model slot) (binders : Binders model Δ)
    {ty : Ty} (comp : Comp laws Δ ty) :
    (comp.rename .there).eval results (.cons value binders) = comp.eval results binders :=
  comp_eval_rename results (fun binder => .there binder) binders (.cons value binders) (fun _ => rfl) comp

theorem term_eval_weaken {Δ : Scope} {slot : Slot} (value : Slot.Value model slot) (binders : Binders model Δ)
    {ty : Ty} (term : Term laws Δ ty) :
    (term.rename .there).eval results (.cons value binders) = term.eval results binders :=
  term_eval_rename results (fun binder => .there binder) binders (.cons value binders) (fun _ => rfl) term

/-! Splits. -/

/-- A component the subject matches is the subject. -/
theorem subject_same?_heq {Δ : Scope} {ty₀ : Ty} (subject : Subject Δ ty₀) {ty : Ty} (comp : Comp laws Δ ty)
    (same : PLift (ty₀ = ty)) (found : subject.same? comp = some same) : HEq (subject.comp (laws := laws)) comp := by
  cases comp with
  | absent => simp [Subject.same?] at found
  | present _ => simp [Subject.same?] at found
  | input binder =>
    cases subject with
    | read _ _ => simp [Subject.same?] at found
    | input decided =>
      simp only [Subject.same?] at found
      split at found
      · rename_i sorts matched
        have sort := Slot.component.inj sorts
        subst sort
        cases eq_of_heq (var_same?_heq decided binder sorts matched)
        exact HEq.rfl
      · cases found
  | read binder position =>
    cases subject with
    | input _ => simp [Subject.same?] at found
    | read decided at₀ =>
      simp only [Subject.same?] at found
      split at found
      · rename_i indices
        exact (Comp.read_heq decided at₀ binder position indices.1 indices.2).2
      · cases found

theorem comp_eval_absentAt {Δ : Scope} {ty₀ : Ty} (subject : Subject Δ ty₀)
    (binders : Binders model Δ) (absent : (subject.comp (laws := laws)).eval results binders = none)
    {ty : Ty} (comp : Comp laws Δ ty) :
    (comp.absentAt subject).eval results binders = comp.eval results binders := by
  unfold Comp.absentAt
  split
  · rename_i same found
    obtain ⟨same⟩ := same
    subst same
    cases eq_of_heq (subject_same?_heq subject comp _ found)
    exact absent.symm
  · rfl

theorem comp_eval_presentAt {Δ : Scope} {ty₀ : Ty} (subject : Subject Δ ty₀)
    (value : model.Value ty₀) (binders : Binders model Δ)
    (present : (subject.comp (laws := laws)).eval results binders = some value)
    {ty : Ty} (comp : Comp laws Δ ty) :
    (comp.presentAt subject).eval results (.cons value binders) = comp.eval results binders := by
  unfold Comp.presentAt
  split
  · rename_i same found
    subst same
    cases eq_of_heq (subject_same?_heq subject comp _ found)
    exact present.symm
  · exact comp_eval_weaken results (slot := .value ty₀) value binders comp

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
  exact entryAt_eq_get _ _

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

theorem term_literal_pin {Δ : Scope} (binders : Binders model Δ) {ty : Ty} (term : Term laws Δ ty)
    (value : Nat) (found : term.literal? = some value) :
    literalValue model ty value = some (term.eval results binders) := by
  cases term <;> simp [Term.literal?] at found
  · subst found
    rfl
  · rename_i literal
    subst found
    cases literal <;> rfl
  · subst found
    rfl

theorem pinsMatch_pinned {Γ₀ : List Ty} {Δ : Scope} (state : Values (Comp laws Δ) Γ₀)
    (inputs : Values (Component model.Value) Γ₀) (binders : Binders model Δ)
    (evaluated : Comps.eval results state binders = inputs) :
    {types : List Ty} → (pins : List LawPin) → (terms : Terms laws Δ types) →
      pinsMatch state pins terms = true → Pinned inputs pins (Terms.eval results terms binders)
  | [], _, .nil, _ => by simp [Terms.eval, Pinned]
  | _ :: _, [], .cons _ _, _ => by simp [Terms.eval, Pinned]
  | ty :: _, .free :: pins, .cons term terms, found => by
    simp only [pinsMatch, Bool.true_and] at found
    exact ⟨trivial, pinsMatch_pinned state inputs binders evaluated pins terms found⟩
  | ty :: _, .literal value :: pins, .cons term terms, found => by
    simp only [pinsMatch, Bool.and_eq_true, beq_iff_eq] at found
    exact ⟨term_literal_pin results binders term value found.1,
      pinsMatch_pinned state inputs binders evaluated pins terms found.2⟩
  | ty :: _, .input index :: pins, .cons term terms, found => by
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
        rw [← evaluated, comps_get_eval, ← entryAt_eq_get, stored, Comp.eval, term_same_eval results binders _ _ head]
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

theorem term_capability?_eval {Δ : Scope} {service : String} (binders : Binders model Δ)
    (term : Term laws Δ (.service service)) (handle : Nat)
    (found : term.capability? = some handle) : term.eval results binders = handle := by
  cases term <;> simp [Term.capability?] at found
  subst found
  rfl

theorem term_index?_eval {Δ : Scope} (binders : Binders model Δ) (term : Term laws Δ .index) (value : Nat)
    (found : term.index? = some value) : term.eval results binders = value := by
  cases term <;> simp [Term.index?] at found
  subst found
  rfl

theorem term_bool?_eval {Δ : Scope} (binders : Binders model Δ) (term : Term laws Δ .boolean) (value : Bool)
    (found : term.bool? = some value) : term.eval results binders = value := by
  cases term <;> simp [Term.bool?] at found
  subst found
  rfl

theorem booleanFold_eval {Δ : Scope} (binders : Binders model Δ) (combine : Bool → Bool → Bool)
    (left right : Term laws Δ .boolean) (comps : Values (Comp laws Δ) [.boolean])
    (found : booleanFold combine left right = some comps) :
    Comps.eval results comps binders =
      Values.cons (some (combine (left.eval results binders) (right.eval results binders))) .nil := by
  unfold booleanFold at found
  cases first : left.bool? with
  | none => simp only [first] at found; cases found
  | some a =>
    cases second : right.bool? with
    | none => simp only [first, second] at found; cases found
    | some b =>
      simp only [first, second] at found
      cases found
      rw [term_bool?_eval results binders left a first, term_bool?_eval results binders right b second]
      rfl

theorem folded_eval {Δ : Scope} (binders : Binders model Δ) (op : Op) (total : op.total = true)
    (terms : Terms laws Δ op.arguments) (comps : Values (Comp laws Δ) op.results)
    (found : folded op terms = some comps) :
    Comps.eval results comps binders = (op.evalTotal model total (Terms.eval results terms binders)).present := by
  cases op
  case indexEqual =>
    rcases terms with _ | ⟨left, _ | ⟨right, _ | _⟩⟩
    simp only [folded] at found
    cases first : left.index? with
    | none => simp only [first] at found; cases found
    | some a =>
      cases second : right.index? with
      | none => simp only [first, second] at found; cases found
      | some b =>
        simp only [first, second] at found
        cases found
        change (Values.cons (some (a == b)) .nil : Values (Component model.Value) [.boolean]) =
          Values.cons (some (decide (left.eval results binders = right.eval results binders))) .nil
        rw [term_index?_eval results binders left a first, term_index?_eval results binders right b second]
        cases same : a == b <;> simp_all
  case booleanAnd | booleanOr | booleanXor | booleanEqual | booleanNotEqual =>
    rcases terms with _ | ⟨left, _ | ⟨right, _ | _⟩⟩
    exact (booleanFold_eval results binders _ left right comps found).trans rfl
  all_goals simp [folded] at found

end Facts

/-! Calculations. -/

theorem operationOn_total (model : DomainModel) {I : PIR.Signature} (observations : SiteObservations I)
    (table : Evaluation.MeaningsOn model.toCarriers I) (op : Op) (total : op.total = true)
    (args : Values model.Value op.arguments) (bodies : Values (RegionFunction model.Value I) op.regions) :
    Evaluation.operationOn model observations table op args bodies = .done (op.evalTotal model total args) := by
  cases op <;> simp [Op.total] at total
  case makeProduct => cases bodies; rfl
  all_goals
    (rcases bodies with _ | _); (rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩); rfl

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
  unfold calculation
  cases foldedResult : folded op terms with
  | some comps =>
    have constant : constantResults (laws := laws) (Δ := Δ) op = none := by
      cases op <;> first | rfl | simp [folded] at foldedResult
    rw [constant, Option.getD_none, Option.getD_some]
    exact folded_eval results binders op total terms comps foldedResult
  | none =>
  rw [Option.getD_none]
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

theorem comps_eval_entryAt (results : LawResults model laws) {Δ : Scope} (binders : Binders model Δ) :
    {types : List Ty} → {ty : Ty} → (comps : Values (Comp laws Δ) types) → (position : Var types ty) →
      entryAt (Comps.eval results comps binders) position = (entryAt comps position).eval results binders
  | _, _, .cons _ _, .here => rfl
  | _, _, .cons _ tail, .there position => comps_eval_entryAt results binders tail position

theorem passEntries_eval (results : LawResults model laws) {Δ : Scope} (binders : Binders model Δ)
    {inputs : List Ty} (comps : Values (Comp laws Δ) inputs) :
    (outputs : List Ty) → (positions : List Nat) →
      passEntries (Comps.eval results comps binders) outputs positions =
        (passEntries comps outputs positions).map fun passed => Comps.eval results passed binders
  | [], _ => rfl
  | _ :: _, [] => rfl
  | ty :: outputs, position :: positions => by
    simp only [passEntries]
    cases Var.decode inputs ty position with
    | none => rfl
    | some binder =>
      simp only [passEntries_eval results binders comps outputs positions, Option.map_map]
      cases passEntries comps outputs positions with
      | none => rfl
      | some rest => simp only [Option.map_some, Function.comp_apply, Comps.eval, comps_eval_entryAt]

theorem termsAt_eval (results : LawResults model laws) {Δ : Scope} (binders : Binders model Δ) :
    {types : List Ty} → {ty : Ty} → (terms : Terms laws Δ types) → (position : Var types ty) →
      (termsAt terms position).eval results binders = entryAt (Terms.eval results terms binders) position
  | _, _, .cons _ _, .here => rfl
  | _, _, .cons _ tail, .there position => termsAt_eval results binders tail position

theorem literalTerm_eval (results : LawResults model laws) {Δ : Scope} (binders : Binders model Δ) :
    (ty : Ty) → (value : Nat) →
      ((literalTerm (laws := laws) (Δ := Δ) ty value).map fun term => term.eval results binders) =
        literalValue model ty value
  | .index, _ => rfl
  | .boolean, _ => rfl
  | .field _, _ => rfl
  | .vector _, _ => rfl
  | .group _, _ => rfl
  | .service _, _ => rfl
  | .indices, _ | .groups _, _ | .oracle _, _ | .oracleSequence .., _
  | .sequence _, _ | .product .., _ => rfl

theorem lawComps_eval (results : LawResults model laws) {Δ : Scope} (binders : Binders model Δ)
    (entry : Fin laws.length) (args : Terms laws Δ laws[entry].helper.inputs) :
    (types : List Ty) → (position : {ty : Ty} → Var types ty → Var laws[entry].helper.outputs ty) →
      (outputs : List LawOutput) → (comps : Values (Comp laws Δ) types) →
        lawComps entry args types position outputs = some comps →
          ∃ values, lawValues model laws[entry].helper (results.result entry (Terms.eval results args binders))
              (Terms.eval results args binders) types position outputs = some values ∧
            Comps.eval results comps binders = values.present
  | [], _, _, comps, found => by
    simp only [lawComps, Option.some.injEq] at found
    subst found
    exact ⟨.nil, rfl, rfl⟩
  | ty :: types, position, outputs, comps, found => by
    simp only [lawComps] at found
    simp only [lawValues]
    generalize headed : outputs.headD .result = head at found ⊢
    cases head with
    | result =>
      simp only at found ⊢
      cases rest : lawComps entry args types (fun binder => position (.there binder)) outputs.tail with
      | none => simp [rest] at found
      | some restComps =>
        simp only [rest, Option.map_some, Option.some.injEq] at found
        subst found
        obtain ⟨values, valuesFound, evaluated⟩ :=
          lawComps_eval results binders entry args types _ outputs.tail restComps rest
        refine ⟨.cons ((results.result entry (Terms.eval results args binders)).get (position .here)) values,
          by simp only [valuesFound, Option.map_some], ?_⟩
        simp only [Comps.eval, Comp.eval, Term.eval, evaluated, Values.present]
    | argument input =>
      simp only at found ⊢
      cases decoded : Var.decode laws[entry].helper.inputs ty input with
      | none => simp only [decoded, Option.map_none] at found; cases found
      | some binder =>
        simp only [decoded, Option.map_some] at found ⊢
        cases rest : lawComps entry args types (fun binder => position (.there binder)) outputs.tail with
        | none => simp [rest] at found
        | some restComps =>
          simp only [rest, Option.map_some, Option.some.injEq] at found
          subst found
          obtain ⟨values, valuesFound, evaluated⟩ :=
            lawComps_eval results binders entry args types _ outputs.tail restComps rest
          refine ⟨.cons (entryAt (Terms.eval results args binders) binder) values,
            by simp only [valuesFound, Option.map_some], ?_⟩
          simp only [Comps.eval, Comp.eval, termsAt_eval, evaluated, Values.present]
    | literal value =>
      have same := literalTerm_eval (laws := laws) (Δ := Δ) results binders ty value
      cases literal : literalTerm (laws := laws) (Δ := Δ) ty value with
      | none => simp [literal] at found
      | some term =>
        rw [literal, Option.map_some] at same
        simp only [literal, Option.map_some] at found
        cases rest : lawComps entry args types (fun binder => position (.there binder)) outputs.tail with
        | none => simp [rest] at found
        | some restComps =>
          simp only [rest, Option.map_some, Option.some.injEq] at found
          subst found
          obtain ⟨values, valuesFound, evaluated⟩ :=
            lawComps_eval results binders entry args types _ outputs.tail restComps rest
          refine ⟨.cons (term.eval results binders) values, by simp only [← same, valuesFound, Option.map_some], ?_⟩
          simp only [Comps.eval, Comp.eval, evaluated, Values.present]

theorem comps_eval_reads (results : LawResults model laws) {Δ : Scope} (binders : Binders model Δ)
    {types : List Ty} (values : Values (Component model.Value) types) :
    Comps.eval results (readComps (laws := laws) (Δ := Δ) types) (.cons values binders) = values := by
  apply values_ext
  intro ty position
  rw [comps_get_eval, readComps, get_mapValues, Operands.identity_get]
  rfl

theorem comps_eval_split (results : LawResults model laws) {Δ : Scope} (binders : Binders model Δ) :
    (first : List Ty) → {rest : List Ty} → (comps : Values (Comp laws Δ) (first ++ rest)) →
      Values.split first (Comps.eval results comps binders) =
        (Comps.eval results (Values.split first comps).1 binders, Comps.eval results (Values.split first comps).2 binders)
  | [], _, _ => rfl
  | _ :: first, _, .cons head tail => by
    have inner := comps_eval_split results binders first tail
    simp only [Values.split, Comps.eval] at inner ⊢
    rw [inner]

/-! Applications. -/

@[simp] theorem recast_rfl {V : Ty → Type} {types : List Ty} (same : types = types) (values : Values V types) :
    recast same values = values := rfl

theorem rolePosition_none {role : Nat} :
    (roles : List Nat) → rolePosition role roles = none → role ∉ roles
  | [], _ => List.not_mem_nil
  | head :: rest, found => by
    simp only [rolePosition] at found
    split at found
    · cases found
    · rename_i different
      cases inner : rolePosition role rest with
      | none =>
        intro member
        rcases List.mem_cons.mp member with same | later
        · exact different same.symm
        · exact rolePosition_none rest inner later
      | some _ => simp [inner] at found

theorem rolePosition_some {role : Nat} :
    (roles : List Nat) → (position : Nat) → rolePosition role roles = some position →
      ∃ bound : position < roles.length, roles[position] = role
  | [], _, found => by simp [rolePosition] at found
  | head :: rest, position, found => by
    simp only [rolePosition] at found
    split at found
    · rename_i same
      cases found
      exact ⟨by simp, same⟩
    · cases inner : rolePosition role rest with
      | none => simp [inner] at found
      | some later =>
        simp only [inner, Option.map_some, Option.some.injEq] at found
        subst found
        obtain ⟨bound, same⟩ := rolePosition_some rest later inner
        exact ⟨by simp; omega, by simpa using same⟩

theorem findCallee_role (names : Bool) (signature : ProtocolSignature) (role : Nat) :
    (callees : List CalleeKey) → (found : Σ' callee : Fin callees.length,
      (calleeAt callees callee).signature.inputs = signature.inputs ∧
        (calleeAt callees callee).signature.outputs = signature.outputs) →
      findCallee names signature role callees = some found → (calleeAt callees found.1).role = role
  | [], _, find => by simp [findCallee] at find
  | key :: rest, found, find => by
    simp only [findCallee] at find
    split at find
    · rename_i agreed
      split at find
      · cases find
        exact agreed.1
      · cases inner : findCallee names signature role rest with
        | none => simp [inner] at find
        | some previous =>
          simp only [inner, Option.map_some, Option.some.injEq] at find
          subst find
          exact findCallee_role names signature role rest previous inner
    · cases inner : findCallee names signature role rest with
      | none => simp [inner] at find
      | some previous =>
        simp only [inner, Option.map_some, Option.some.injEq] at find
        subst find
        exact findCallee_role names signature role rest previous inner

theorem enter_roles (context : ProtocolContext) (site : String) (roles : List Nat) (position : Nat)
    (bound : position < roles.length) : (context.enter site roles).roles position = context.roles roles[position] := by
  simp [ProtocolContext.enter, roleSubstitution, bound]

theorem roles_bounded {roster : Nat} {roles : List Nat} (bounded : roles.any (roster ≤ ·) = false)
    (position : Nat) (bound : position < roles.length) : roles[position] < roster := by
  have := List.any_eq_false.mp bounded roles[position] (List.getElem_mem bound)
  simp at this
  exact this

theorem contains_absent {context : ProtocolContext} {role roster : Nat} (distinct : RosterDistinct context role roster)
    (signature : ProtocolSignature) (roles : List Nat) (site : String) (bounded : roles.any (roster ≤ ·) = false)
    (length : roles.length = signature.roles.length) (absent : role ∉ roles) :
    (context.enter site roles).contains signature (context.roles role) = false := by
  rw [Bool.eq_false_iff]
  intro contains
  obtain ⟨position, bound, same⟩ := (ProtocolContext.contains_iff _ _ _).mp contains
  have inside : position < roles.length := length ▸ bound
  rw [enter_roles _ _ _ _ inside] at same
  exact distinct roles[position] (roles_bounded bounded position inside)
    (fun equal => absent (equal ▸ List.getElem_mem inside)) same

theorem contains_present (context : ProtocolContext) (role : Nat) (signature : ProtocolSignature)
    (roles : List Nat) (site : String) (length : roles.length = signature.roles.length) (position : Nat)
    (bound : position < roles.length) (located : roles[position] = role) :
    (context.enter site roles).contains signature (context.roles role) = true :=
  (ProtocolContext.contains_iff _ _ _).mpr ⟨position, length ▸ bound, by rw [enter_roles _ _ _ _ bound, located]⟩

theorem nodup_getElem : (roles : List Nat) → roles.Nodup → (first second : Nat) →
    (firstBound : first < roles.length) → (secondBound : second < roles.length) →
      roles[first] = roles[second] → first = second
  | [], _, _, _, firstBound, _, _ => absurd firstBound (by simp)
  | head :: rest, nodup, first, second, firstBound, secondBound, same => by
    rw [List.nodup_cons] at nodup
    cases first with
    | zero =>
      cases second with
      | zero => rfl
      | succ second =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at same
        exact absurd (same ▸ List.getElem_mem (by simpa using secondBound)) nodup.1
    | succ first =>
      cases second with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at same
        exact absurd (same ▸ List.getElem_mem (by simpa using firstBound)) nodup.1
      | succ second =>
        simp only [List.getElem_cons_succ] at same
        exact congrArg (· + 1) (nodup_getElem rest nodup.2 first second (by simpa using firstBound)
          (by simpa using secondBound) same)

theorem distinct_enter {context : ProtocolContext} {role roster : Nat} (distinct : RosterDistinct context role roster)
    (signature : ProtocolSignature) (roles : List Nat) (site : String) (bounded : roles.any (roster ≤ ·) = false)
    (length : roles.length = signature.roles.length) (nodup : roles.Nodup) (position : Nat)
    (bound : position < roles.length) (located : roles[position] = role) :
    RosterDistinct (context.enter site roles) position signature.roles.length := by
  intro other otherBound different same
  have inside : other < roles.length := length ▸ otherBound
  rw [enter_roles _ _ _ _ inside, enter_roles _ _ _ _ bound, located] at same
  have unequal : roles[other] ≠ role := by
    rw [← located]
    intro equal
    exact different (nodup_getElem roles nodup other position inside bound equal)
  exact distinct roles[other] (roles_bounded bounded other inside) unequal same

section Arguments
variable (results : LawResults model laws)

theorem term_fieldValue?_eval {Δ : Scope} (binders : Binders model Δ) {domain : String}
    (term : Term laws Δ (.field domain)) (value : Nat) (found : term.fieldValue? = some value) :
    term.eval results binders = fieldLiteral model.toFieldModel domain value := by
  cases term <;> simp [Term.fieldValue?] at found
  subst found
  rfl

theorem calleeArguments_fill {Δ : Scope} (binders : Binders model Δ) :
    {Γ : List Ty} → (pattern : InputPattern Γ) → (comps : Values (Comp laws Δ) Γ) →
      (arguments : Values (Argument laws Δ) pattern.scope) → calleeArguments pattern comps = some arguments →
        ∃ others, Comps.eval results comps binders =
          pattern.fill model (Arguments.eval results arguments binders) others
  | [], .nil, .nil, _, _ => ⟨.nil, rfl⟩
  | ty :: _, .cons .present rest, .cons comp comps, arguments, found => by
    change (match comp.term? with
        | none => none
        | some term => (calleeArguments rest comps).map fun args =>
            (.cons (term : Argument laws Δ (.value ty)) args :
              Values (Argument laws Δ) (.value ty :: InputPattern.scope rest))) = some arguments at found
    cases term : comp.term? with
    | none => simp only [term] at found; cases found
    | some value =>
      simp only [term] at found
      cases inner : calleeArguments rest comps with
      | none => rw [inner] at found; cases found
      | some tail =>
        rw [inner] at found
        cases found
        obtain ⟨others, same⟩ := calleeArguments_fill binders rest comps tail inner
        refine ⟨others, ?_⟩
        cases comp <;> simp [Comp.term?] at term
        subst term
        change Values.cons _ (Comps.eval results comps binders) = _
        rw [same]
        rfl
  | ty :: _, .cons .optional rest, .cons comp comps, arguments, found => by
    change ((calleeArguments rest comps).map fun args =>
        (.cons (comp : Argument laws Δ (.component ty)) args :
          Values (Argument laws Δ) (.component ty :: InputPattern.scope rest))) = some arguments at found
    cases inner : calleeArguments rest comps with
    | none => rw [inner] at found; cases found
    | some tail =>
      rw [inner] at found
      cases found
      obtain ⟨others, same⟩ := calleeArguments_fill binders rest comps tail inner
      refine ⟨others, ?_⟩
      change Values.cons _ (Comps.eval results comps binders) = _
      rw [same]
      rfl
  | ty :: _, .cons .absent rest, .cons comp comps, arguments, found => by
    change calleeArguments rest comps = some arguments at found
    obtain ⟨others, same⟩ := calleeArguments_fill binders rest comps arguments found
    refine ⟨.cons (comp.eval results binders) others, ?_⟩
    change Values.cons _ (Comps.eval results comps binders) = _
    rw [same]
    rfl
  | _ :: _, .cons (.capability service value) rest, .cons comp comps, arguments, found => by
    change (match comp.term? with
        | none => none
        | some term => onlyIf (term.capability? == some value) (calleeArguments rest comps)) =
      some arguments at found
    cases term : comp.term? with
    | none => simp only [term] at found; cases found
    | some literal =>
      simp only [term] at found
      obtain ⟨agreed, found⟩ := onlyIf_eq_some found
      have agreed := beq_iff_eq.mp agreed
      · obtain ⟨others, same⟩ := calleeArguments_fill binders rest comps arguments found
        refine ⟨others, ?_⟩
        cases comp <;> simp [Comp.term?] at term
        subst term
        simp only [Comps.eval, Comp.eval, same, term_capability?_eval results binders _ value agreed]
        rfl
  | _ :: _, .cons (.index value) rest, .cons comp comps, arguments, found => by
    change (match comp.term? with
        | none => none
        | some term => onlyIf (term.index? == some value) (calleeArguments rest comps)) =
      some arguments at found
    cases term : comp.term? with
    | none => simp only [term] at found; cases found
    | some literal =>
      simp only [term] at found
      obtain ⟨agreed, found⟩ := onlyIf_eq_some found
      have agreed := beq_iff_eq.mp agreed
      · obtain ⟨others, same⟩ := calleeArguments_fill binders rest comps arguments found
        refine ⟨others, ?_⟩
        cases comp <;> simp [Comp.term?] at term
        subst term
        simp only [Comps.eval, Comp.eval, same, term_index?_eval results binders _ value agreed]
        rfl
  | _ :: _, .cons (.field domain value) rest, .cons comp comps, arguments, found => by
    change (match comp.term? with
        | none => none
        | some term => onlyIf (term.fieldValue? == some value) (calleeArguments rest comps)) =
      some arguments at found
    cases term : comp.term? with
    | none => simp only [term] at found; cases found
    | some literal =>
      simp only [term] at found
      obtain ⟨agreed, found⟩ := onlyIf_eq_some found
      have agreed := beq_iff_eq.mp agreed
      · obtain ⟨others, same⟩ := calleeArguments_fill binders rest comps arguments found
        refine ⟨others, ?_⟩
        cases comp <;> simp [Comp.term?] at term
        subst term
        simp only [Comps.eval, Comp.eval, same, term_fieldValue?_eval results binders _ value agreed]
        rfl
  | _ :: _, .cons (.bool value) rest, .cons comp comps, arguments, found => by
    change (match comp.term? with
        | none => none
        | some term => onlyIf (term.bool? == some value) (calleeArguments rest comps)) =
      some arguments at found
    cases term : comp.term? with
    | none => simp only [term] at found; cases found
    | some literal =>
      simp only [term] at found
      obtain ⟨agreed, found⟩ := onlyIf_eq_some found
      have agreed := beq_iff_eq.mp agreed
      · obtain ⟨others, same⟩ := calleeArguments_fill binders rest comps arguments found
        refine ⟨others, ?_⟩
        cases comp <;> simp [Comp.term?] at term
        subst term
        simp only [Comps.eval, Comp.eval, same, term_bool?_eval results binders _ value agreed]
        rfl

theorem calleePinsMatch_pinned {Γ₀ : List Ty} {Δ : Scope} (state : Values (Comp laws Δ) Γ₀)
    (inputs : Values (Component model.Value) Γ₀) (binders : Binders model Δ)
    (evaluated : Comps.eval results state binders = inputs) :
    {scope : Scope} → (pins : List (Option Nat)) → (arguments : Values (Argument laws Δ) scope) →
      calleePinsMatch state pins arguments = true → CalleePinned inputs pins (Arguments.eval results arguments binders)
  | _, [], .nil, _ => trivial
  | _, [], .cons _ _, _ => trivial
  | _, _ :: _, .nil, _ => trivial
  | _, none :: pins, .cons _ arguments, found => by
    simp only [calleePinsMatch] at found
    exact ⟨trivial, calleePinsMatch_pinned state inputs binders evaluated pins arguments found⟩
  | _, some input :: pins, .cons (ty := .value ty) term arguments, found => by
    simp only [calleePinsMatch, Bool.and_eq_true] at found
    refine ⟨?_, calleePinsMatch_pinned state inputs binders evaluated pins arguments found.2⟩
    have head := found.1
    show match Var.decode Γ₀ ty input with
      | some binder => inputs.get binder = some (Term.eval results (term : Term laws Δ ty) binders)
      | none => False
    cases decoded : Var.decode Γ₀ ty input with
    | none => simp [decoded] at head
    | some binder =>
      simp only [decoded] at head ⊢
      split at head
      · rename_i pinned stored
        rw [← evaluated, comps_get_eval, ← entryAt_eq_get, stored, Comp.eval,
          term_same_eval results binders _ _ head]
      · simp at head
  | _, some _ :: _, .cons (ty := .component _) _ _, found => by simp [calleePinsMatch] at found
  | _, some _ :: _, .cons (ty := .results _) _ _, found => by simp [calleePinsMatch] at found
  | _, some _ :: _, .cons (ty := .tuple _) _ _, found => by simp [calleePinsMatch] at found

theorem comps_eval_calleeOutputs {Δ : Scope} (binders : Binders model Δ) (role : Nat) {types : List Ty}
    (values : Values (Component model.Value) types) :
    (scopes : List (List Nat)) → {kept : List Ty} → (positions : Values (Var types) kept) →
      Comps.eval results (calleeOutputs (laws := laws) (Δ := Δ) role scopes positions) (.cons values binders) =
        staticMask role values scopes positions
  | _, _, .nil => rfl
  | scopes, _, .cons position rest => by
    simp only [calleeOutputs, staticMask, Comps.eval, comps_eval_calleeOutputs binders role values scopes.tail rest]
    split <;> rfl

end Arguments

/-! Participant rules under the selected observations, one operation at a time. -/

section Rules
variable (model : DomainModel) {I : PIR.Signature}
  (actions : PIR.OperationInterpretation (Interface model) I)
  {iterations : IterationObservations I} (tables : Tables model I)
  (protocols : ProtocolTable model.Value I) (context : ProtocolContext) (self : Nat)

theorem calculate_absent (op : Op) (allowed : op.isCalculation = true) (total : op.total = true)
    (args : Values (Component model.Value) (ProtocolOp.calculate op allowed).arguments)
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.calculate op allowed).regions)
    (absent : RoleFamily.sequence (Value := model.Value) (types := op.arguments) args = none) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.calculate op allowed) args callbacks protocols context iterations =
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
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.calculate op allowed).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.calculate op allowed) values.present callbacks protocols context iterations =
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
    change PIR.Process.bind (Evaluation.operationOn model _ tables.closed op present _) _ = _
    rw [operationOn_total model _ tables.closed op total]
    rfl

theorem boundedAt_absent (domain : String)
    (args : Values (Component model.Value) (Op.boundedAt domain).arguments)
    (callbacks : Values (RegionFunction (Component model.Value) I) [])
    (absent : RoleFamily.sequence (Value := model.Value) args = none) :
    protocolOperationWithOn model (.silent I) actions tables self (.calculate (.boundedAt domain) rfl)
      args callbacks protocols context iterations = .done (Values.absent model.Value [.field domain]) := by
  simp only [protocolOperationWithOn, Evaluation.componentOperationOn, strictComponent, absent]
  rfl

theorem boundedAt_present (domain : String) (values : Values model.Value (Op.boundedAt domain).arguments)
    (callbacks : Values (RegionFunction (Component model.Value) I) []) :
    protocolOperationWithOn model (.silent I) actions tables self (.calculate (.boundedAt domain) rfl)
      values.present callbacks protocols context iterations =
      (Evaluation.operationOn model (.silent I) tables.closed (.boundedAt domain) values .nil).bind
        (fun result => .done result.present) := by
  cases callbacks
  simp only [protocolOperationWithOn, Evaluation.componentOperationOn, strictComponent,
    RoleFamily.sequence_present]
  rfl

theorem localCall_rule (helper : Helper) (kind : helper.kind = .local) (owner : Nat) (site : String)
    (args : Values (Component model.Value) helper.inputs)
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.localCall helper kind owner site).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.localCall helper kind owner site) args callbacks protocols context iterations =
      Participant.owned self (context.roles owner) (invoke tables.closed helper) args := rfl

theorem exchange_rule (ty : Ty) (sender receiver : Nat) (site : String) (value : Option (model.Value ty))
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.exchange ty sender receiver site).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.exchange ty sender receiver site) (.cons value .nil) callbacks protocols context iterations =
      ((Participant.exchange (services := services) self (context.roles sender) (context.roles receiver)
        (qualifyProtocolSite context.applicationPrefix site) value).interpret
          actions).bind fun result => .done (.cons result .nil) := rfl

theorem restrict_rule (ty : Ty) (roles : List Nat) (value : Option (model.Value ty))
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.restrict ty roles).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.restrict ty roles) (.cons value .nil) callbacks protocols context iterations =
      .done (.cons (Participant.restrict ((roles.map context.roles).contains self) value) .nil) := rfl

theorem assemble_rule (ty : Ty) (roles : List Nat)
    (values : Values (Component model.Value) (roles.map (fun _ => ty)))
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.assemble ty roles).regions) :
    protocolOperationWithOn model (SiteObservations.silent I)
      actions tables self (.assemble ty roles) values callbacks protocols context iterations =
      .done (.cons (assembleComponent (fun role => context.roles role == self) none roles values) .nil) := rfl

theorem draw_rule (owner : Nat) (field site : String)
    (args : Values (Component model.Value) (ProtocolOp.draw owner field site).arguments)
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.draw owner field site).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.draw owner field site) args callbacks protocols context iterations =
      ((Participant.query (services := services) self (context.roles owner)
        (qualifyProtocolSite context.applicationPrefix site) field args).interpret
          actions).bind fun result => .done (.cons result .nil) := rfl

theorem guard_rule (owner : Nat) (site : String) (condition : Option Bool)
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.guard owner site).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.guard owner site) (.cons condition .nil) callbacks protocols context iterations =
      ((Participant.guard (services := services) (Value := model.Value) self (context.roles owner)
        condition).interpret actions).bind fun _ => .done .nil := rfl

theorem mark_rule (site : String)
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.mark site).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.mark site) .nil callbacks protocols context iterations = .done .nil := rfl

theorem statement_rule (relation : String) (types : List Ty) (selectors : List String) (acceptance : Nat)
    (args : Values (Component model.Value) (ProtocolOp.statement relation types selectors acceptance).arguments)
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.statement relation types selectors acceptance).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.statement relation types selectors acceptance) args callbacks protocols context iterations = .done .nil := rfl

theorem math_rule (helper : Helper) (allowed : (Op.invoke helper).isCalculation = true)
    (args : Values (Component model.Value) helper.inputs)
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.calculate (.invoke helper) allowed).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.calculate (.invoke helper) allowed) args callbacks protocols context iterations =
      invoke tables.components helper args := by
  have math : helper.kind = .math := by simpa [Op.isCalculation] using allowed
  simp only [protocolOperationWithOn]
  generalize (Op.invoke helper).calculationRegions allowed = regions
  cases regions
  simp only [Evaluation.componentOperationOn, math, ↓reduceIte]
  rfl

theorem repeat_rule (spec : RepeatSpec) (site : String) (count : Option Nat)
    (values : Values (Component model.Value) (spec.state ++ spec.captures))
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.repeat spec site).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.repeat spec site) (.cons count values) callbacks protocols context iterations =
      denoteRepeatOn spec context self count (Values.split spec.state values).1
        (Values.split spec.state values).2 (callbacks.get .here) iterations site := rfl

theorem apply_rule (signature : ProtocolSignature) (roles : List Nat) (site : String)
    (args : Values (Component model.Value) signature.inputs)
    (callbacks : Values (RegionFunction (Component model.Value) I)
      (ProtocolOp.protocolApply signature roles site).regions) :
    protocolOperationWithOn model (SiteObservations.silent I) actions tables self (.protocolApply signature roles site) args callbacks protocols context iterations =
      if (context.enter site roles).contains signature self then
        invokeProtocol protocols signature (context.enter site roles) self args
      else .done (Values.absent model.Value signature.outputs) := rfl

theorem owned_absent {J : PIR.Signature} {inputs outputs : List Ty} (self : Nat)
    (work : Values model.Value inputs → PIR.Process J (Values model.Value outputs))
    (args : Values (Component model.Value) inputs) (absent : RoleFamily.sequence args = none) :
    Participant.owned self self work args = .halt .incomplete := by
  simp [Participant.owned, absent]

end Rules

/-! The main theorem. -/

theorem bind_congr_left {I : PIR.Signature} {A B : Type} {first second : PIR.Process I A}
    (same : first = second) (next : A → PIR.Process I B) : first.bind next = second.bind next := by
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
variable (model : DomainModel) {I : PIR.Signature}
  (actions : PIR.OperationInterpretation (Interface model) I) (iterations : IterationObservations I)
  (tables : Tables model I) (protocols : ProtocolTable model.Value I) (context : ProtocolContext)

/-- The participant meaning under the selected action and iteration observations,
with silent helper sites, at the context's roster coordinate. -/
abbrev meaningAtOn (role : Nat) : RegionMeaning protocolDialect I :=
  participantMeaningWithOn model (.silent I) actions
    tables (context.roles role) protocols context iterations

/-- The repeats the participant rules run at the participant the context gives
a roster index: callbacks are denoted with the same meaning. -/
def runsAtOn (role : Nat) : Runs model I where
  callback _ region := fun args => region.denote (meaningAtOn model actions iterations tables protocols context role) args.get
  run spec count state captures body site :=
    denoteRepeatOn spec context (context.roles role) count state captures body iterations site

/-- Every form a normalization step returns from a state denotes the region's
process at the state's environment, whenever the state's inputs are the body's
and the form's law uses are calls of the laws' own helpers. -/
def Continues (sig : Signature) (results : LawResults model sig.laws)
    (processes : CalleeProcesses model sig.callees I) (role : Nat)
    {Γ₀ Γ out : List Ty} (inputs : Values (Component model.Value) Γ₀) (region : Region protocolDialect Γ out)
    (normalized : {Δ : Scope} → State sig.laws Γ₀ Δ Γ → Except Refusal (Form sig.laws sig.callees Δ out)) : Prop :=
  ∀ {Δ : Scope} (state : State sig.laws Γ₀ Δ Γ) (form : Form sig.laws sig.callees Δ out), normalized state = .ok form →
    form.LawsMatch → ∀ binders : Binders model Δ, Comps.eval results state.inputs binders = inputs →
      region.denote (meaningAtOn model actions iterations tables protocols context role) (Comps.eval results state.env binders).get =
        form.denoteOn model actions tables results context (runsAtOn model actions iterations tables protocols context role) processes binders

variable {model actions iterations tables protocols context}

theorem state_map_eval (results : LawResults model laws) {Γ₀ Γ : List Ty} {Δ Δ' : Scope}
    (f : {ty : Ty} → Comp laws Δ ty → Comp laws Δ' ty) (binders : Binders model Δ)
    (binders' : Binders model Δ')
    (preserved : ∀ {ty : Ty} (comp : Comp laws Δ ty), (f comp).eval results binders' = comp.eval results binders)
    (state : State laws Γ₀ Δ Γ) :
    Comps.eval results (state.map f).inputs binders' = Comps.eval results state.inputs binders ∧
      Comps.eval results (state.map f).env binders' = Comps.eval results state.env binders :=
  ⟨comps_eval_map results f binders binders' preserved state.inputs,
    comps_eval_map results f binders binders' preserved state.env⟩

theorem resolve_sound (sig : Signature) (results : LawResults model sig.laws)
    (processes : CalleeProcesses model sig.callees I) (role : Nat)
    {Γ₀ Γ out : List Ty} (inputs : Values (Component model.Value) Γ₀) (region : Region protocolDialect Γ out)
    (op : ProtocolOp) (args : Operands Γ op.arguments)
    (proceed : {Δ : Scope} → State sig.laws Γ₀ Δ Γ → Except Refusal (Form sig.laws sig.callees Δ out))
    (sound : Continues model actions iterations tables protocols context sig results processes role inputs region proceed) (fuel : Nat) :
    Continues model actions iterations tables protocols context sig results processes role inputs region
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
            simp only [Form.denoteOn, Form.denoteWithOn]
            cases value : Comp.eval results subject.comp binders with
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

theorem continue_push (sig : Signature) (results : LawResults model sig.laws)
    (processes : CalleeProcesses model sig.callees I) (role : Nat)
    {Γ₀ Γ out types : List Ty} (inputs : Values (Component model.Value) Γ₀)
    (nextRegion : Region protocolDialect (types ++ Γ) out)
    (next : {Δ : Scope} → State sig.laws Γ₀ Δ (types ++ Γ) → Except Refusal (Form sig.laws sig.callees Δ out))
    (sound : Continues model actions iterations tables protocols context sig results processes role inputs nextRegion next)
    {Δ : Scope} (state : State sig.laws Γ₀ Δ Γ) (added : Values (Comp sig.laws Δ) types)
    (form : Form sig.laws sig.callees Δ out) (normalized : next (state.push added) = .ok form) (matched : form.LawsMatch)
    (binders : Binders model Δ)
    (inputsEq : Comps.eval results state.inputs binders = inputs) (values : Values (Component model.Value) types)
    (evaluated : Comps.eval results added binders = values) :
    nextRegion.denote (meaningAtOn model actions iterations tables protocols context role)
        (values.append (Comps.eval results state.env binders)).get =
      form.denoteOn model actions tables results context (runsAtOn model actions iterations tables protocols context role) processes binders := by
  have step := sound (state.push added) form normalized matched binders inputsEq
  simp only [State.push, comps_eval_append, evaluated] at step
  exact step

theorem continue_weaken_push (sig : Signature) (results : LawResults model sig.laws)
    (processes : CalleeProcesses model sig.callees I) (role : Nat)
    {Γ₀ Γ out types : List Ty} (inputs : Values (Component model.Value) Γ₀)
    (nextRegion : Region protocolDialect (types ++ Γ) out)
    (next : {Δ : Scope} → State sig.laws Γ₀ Δ (types ++ Γ) → Except Refusal (Form sig.laws sig.callees Δ out))
    (sound : Continues model actions iterations tables protocols context sig results processes role inputs nextRegion next)
    {Δ : Scope} (state : State sig.laws Γ₀ Δ Γ) (slot : Slot) (value : Slot.Value model slot)
    (added : Values (Comp sig.laws (slot :: Δ)) types)
    (form : Form sig.laws sig.callees (slot :: Δ) out) (normalized : next ((state.weaken slot).push added) = .ok form)
    (matched : form.LawsMatch) (binders : Binders model Δ)
    (inputsEq : Comps.eval results state.inputs binders = inputs)
    (values : Values (Component model.Value) types)
    (evaluated : Comps.eval results added (.cons value binders) = values) :
    nextRegion.denote (meaningAtOn model actions iterations tables protocols context role)
        (values.append (Comps.eval results state.env binders)).get =
      form.denoteOn model actions tables results context (runsAtOn model actions iterations tables protocols context role) processes (.cons value binders) := by
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

theorem assemble_eval {context : ProtocolContext} {role roster : Nat}
    (distinct : RosterDistinct context role roster)
    (results : LawResults model laws) {Γ : List Ty} {Δ : Scope} {ty : Ty}
    (env : Values (Comp laws Δ) Γ) (binders : Binders model Δ) :
    (roles : List Nat) → roles.any (roster ≤ ·) = false →
    (args : Operands Γ (roles.map (fun _ => ty))) →
    (assembleComponent (fun owner => owner == role) .absent roles (lookup env args)).eval results binders =
      assembleComponent (V := Component model.Value)
        (fun owner => context.roles owner == context.roles role) none roles
        (Operands.eval (Comps.eval results env binders).get args)
  | [], _, .nil => rfl
  | owner :: roles, bounded, .cons arg args => by
    have bounds : owner < roster ∧ roles.any (roster ≤ ·) = false := by
      simpa using bounded
    have comparison : (context.roles owner == context.roles role) = (owner == role) := by
      by_cases same : owner = role
      · simp [same]
      · simp [same, distinct owner bounds.1 same]
    simp only [assembleComponent, lookup, Operands.eval, comparison]
    split
    · simp only [entryAt_eq_get, comps_get_eval]
    · exact assemble_eval distinct results env binders roles bounds.2 args

theorem operation_sound (sig : Signature) (results : LawResults model sig.laws)
    (processes : CalleeProcesses model sig.callees I) (role roster : Nat)
    (distinct : RosterDistinct context role roster) {Γ₀ : List Ty} (inputs : Values (Component model.Value) Γ₀)
    (lawsHold : LawsHold tables results inputs)
    (calleesHold : CalleesHold protocols processes inputs) {Γ out : List Ty} (op : ProtocolOp)
    (args : Operands Γ op.arguments) (bodies : Regions protocolDialect op.regions)
    (nextRegion : Region protocolDialect (op.results ++ Γ) out)
    (next : {Δ : Scope} → State sig.laws Γ₀ Δ (op.results ++ Γ) → Except Refusal (Form sig.laws sig.callees Δ out))
    (sound : Continues model actions iterations tables protocols context sig results processes role inputs nextRegion next) :
    Continues model actions iterations tables protocols context sig results processes role inputs (.letOp op args bodies nextRegion)
      (fun state => operation sig role roster op args bodies state next) := by
  intro Δ state form normalized matched binders inputsEq
  rw [Region.denote_letOp_values]
  change (protocolOperationWithOn model (.silent _) actions tables
    (context.roles role) op (Operands.eval (Comps.eval results state.env binders).get args)
    (bodies.denote (meaningAtOn model actions iterations tables protocols context role)) protocols context iterations).bind _ = _
  rw [← comps_eval_operands, ← lookup_eq_eval]
  cases op with
  | calculate op allowed =>
    simp only [operation, calculateOperation] at normalized
    split at normalized
    · rename_i total
      simp only [totalCalculation] at normalized
      split at normalized
      · rename_i absent
        refine (bind_congr_left (calculate_absent model actions tables protocols context _ op allowed total _ _
          (anyAbsent_sequence results binders _ absent)) _).trans ?_
        exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq
          _ (comps_eval_absent results binders op.results)
      · split at normalized
        · cases normalized
        · rename_i terms found
          erw [presentTerms_eval results binders _ terms found]
          refine (bind_congr_left (calculate_present model actions tables protocols context _ op allowed total _ _) _).trans ?_
          exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq
            _ (calculation_eval results binders op total terms)
    · rename_i notTotal
      cases op
      case invoke helper =>
        simp only [mathCall] at normalized
        split at normalized
        · split at normalized
          · rename_i entry inputsSame outputsSame lawFound
            split at normalized
            · rename_i positions shape
              split at normalized
              · rename_i passed found
                obtain ⟨restForm, rest, built⟩ := except_bind_ok_inv normalized
                cases built
                obtain ⟨same, restMatched⟩ := matched
                subst same
                have law := lawsHold entry
                simp only [LawHolds, shape] at law
                have lawAt := law (Comps.eval results (lookup state.env args) binders) _
                  (by rw [passEntries_eval, found, Option.map_some])
                refine (bind_congr_left ((math_rule model actions tables protocols context _ _ allowed _ _).trans lawAt) _).trans ?_
                exact continue_push sig results processes _ inputs nextRegion next sound state _ restForm rest restMatched
                  binders inputsEq _ rfl
              · cases normalized
            all_goals
              simp only [exactMathCall] at normalized
              obtain ⟨restForm, rest, built⟩ := except_bind_ok_inv normalized
              cases built
              refine (bind_congr_left (math_rule model actions tables protocols context _ _ allowed _ _) _).trans ?_
              simp only [Form.denoteOn, Form.denoteWithOn]
              apply congrArg
              funext values
              exact continue_weaken_push sig results processes _ inputs nextRegion next sound state _ values _ restForm rest
                matched binders inputsEq _ (comps_eval_reads (types := helper.outputs) results binders values)
          · simp only [exactMathCall] at normalized
            obtain ⟨restForm, rest, built⟩ := except_bind_ok_inv normalized
            cases built
            refine (bind_congr_left (math_rule model actions tables protocols context _ _ allowed _ _) _).trans ?_
            simp only [Form.denoteOn, Form.denoteWithOn]
            apply congrArg
            funext values
            exact continue_weaken_push sig results processes _ inputs nextRegion next sound state _ values _ restForm rest
              matched binders inputsEq _ (comps_eval_reads (types := helper.outputs) results binders values)
        · cases normalized
      case boundedAt domain =>
        simp only [partialCalculation] at normalized
        split at normalized
        · rename_i absent
          refine (bind_congr_left (boundedAt_absent model actions tables protocols context _ domain _ _
            (anyAbsent_sequence results binders _ absent)) _).trans ?_
          exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched
            binders inputsEq _ (comps_eval_absent results binders [.field domain])
        · split at normalized
          · cases normalized
          · rename_i terms found
            erw [presentTerms_eval results binders _ terms found]
            obtain ⟨restForm, rest, built⟩ := except_bind_ok_inv normalized
            cases built
            refine (bind_congr_left (boundedAt_present model actions tables protocols context _ domain _ _) _).trans ?_
            simp only [Form.denoteOn, Form.denoteWithOn]
            refine (PIR.Process.bind_assoc _ _ _).trans ?_
            apply congrArg
            funext values
            exact continue_weaken_push sig results processes _ inputs nextRegion next sound state _ values _ restForm rest
              matched binders inputsEq _ (comps_eval_positions results (.cons values binders)
                (fun position => Term.result .here position) values (fun _ => rfl))
      all_goals first
        | (simp [Op.total] at notTotal; done)
        | cases normalized
  | localCall helper kind owner site =>
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i inRoster
      refine (bind_congr_left (localCall_rule model actions tables protocols context _ helper kind owner site _ _) _).trans ?_
      split at normalized
      · rename_i other
        have different : context.roles owner ≠ context.roles role :=
          distinct owner (by omega) (by simpa using other)
        refine (bind_congr_left (Participant.owned_other _ _ different _ _) _).trans ?_
        exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq
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
          · rename_i kept
            obtain ⟨restForm, rest, built⟩ := except_bind_ok_inv normalized
            cases built
            simp only [Form.denoteOn, Form.denoteWithOn]
            apply congrArg
            funext values
            exact continue_weaken_push sig results processes _ inputs nextRegion next sound state _ values _ restForm rest
              matched binders inputsEq _ (comps_eval_reads (types := helper.outputs) results binders values)
          · split at normalized
            · cases normalized
            · rename_i terms found
              rw [presentTerms_eval results binders _ terms found]
              refine (bind_congr_left (Participant.owned_present _ _ _) _).trans ?_
              simp only [ownedCall] at normalized
              split at normalized
              · rename_i entry inputsSame outputsSame lawFound
                split at normalized
                · rename_i pinned
                  split at normalized
                  · rename_i outputs shape
                    simp only [lawReturn] at normalized
                    split at normalized
                    · rename_i lawResults found
                      obtain ⟨restForm, rest, built⟩ := except_bind_ok_inv normalized
                      cases built
                      obtain ⟨same, restMatched⟩ := matched
                      subst same
                      have law := lawsHold entry
                      simp only [LawHolds, shape] at law
                      obtain ⟨values, valuesFound, evaluated⟩ :=
                        lawComps_eval results binders entry _ _ _ _ _ found
                      have lawAt := law _ (pinsMatch_pinned results state.inputs inputs binders inputsEq _ _ pinned)
                        values valuesFound
                      refine (bind_congr_left (bind_congr_left lawAt _) _).trans ?_
                      exact continue_push sig results processes _ inputs nextRegion next sound state _ restForm rest restMatched
                        binders inputsEq _ evaluated
                    · cases normalized
                  · rename_i reason shape
                    cases normalized
                    obtain ⟨same, _⟩ := matched
                    subst same
                    have law := lawsHold entry
                    simp only [LawHolds, shape] at law
                    have lawAt := law (Terms.eval results terms binders)
                      (pinsMatch_pinned results state.inputs inputs binders inputsEq _ _ pinned)
                    refine (bind_congr_left (bind_congr_left lawAt _) _).trans ?_
                    rfl
                  · cases normalized
                · cases normalized
              · split at normalized
                · obtain ⟨restForm, rest, built⟩ := except_bind_ok_inv normalized
                  cases built
                  refine (PIR.Process.bind_assoc _ _ _).trans ?_
                  simp only [Form.denoteOn, Form.denoteWithOn]
                  apply congrArg
                  funext values
                  exact continue_weaken_push sig results processes _ inputs nextRegion next sound state _ values _
                    restForm rest matched binders inputsEq _ (comps_eval_positions results _ _ _ fun _ => rfl)
                · cases normalized
  | exchange ty sender receiver site =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i bounded
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at bounded
      refine (bind_congr_left (exchange_rule model actions tables protocols context _ ty sender receiver site _ _) _).trans ?_
      split at normalized
      · rename_i isSender
        have same : sender = role := by simpa using isSender
        subst same
        split at normalized
        · rename_i stored
          cases normalized
          simp [Participant.exchange, stored, Comp.eval, PIR.Process.bind, PIR.Process.interpret,
            Form.denoteOn, Form.denoteWithOn]
        · rename_i term stored
          cases rest : next (state.push (.cons (.present term) .nil)) with
          | error refusal => rw [rest, except_bind_error] at normalized; cases normalized
          | ok restForm =>
            rw [rest, except_bind_ok] at normalized
            cases normalized
            simp only [Participant.exchange, stored, Comp.eval, ite_true, PIR.Process.bind, PIR.Process.interpret, Form.denoteOn,
              Form.denoteWithOn, PIR.Process.bind_assoc]
            apply congrArg
            funext reply
            exact continue_push sig results processes _ inputs nextRegion next sound state _ restForm rest matched binders inputsEq
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
            simp only [Participant.exchange, different, ite_false, ite_true, PIR.Process.bind, PIR.Process.interpret, Form.denoteOn,
              Form.denoteWithOn, PIR.Process.bind_assoc]
            apply congrArg
            funext reply
            exact continue_weaken_push sig results processes _ inputs nextRegion next sound state _ reply _ restForm rest
              matched binders inputsEq _ rfl
        · rename_i notReceiver
          have otherReceiver : context.roles receiver ≠ context.roles role :=
            distinct receiver bounded.2 (by simpa using notReceiver)
          simp only [Participant.exchange, different, otherReceiver, ite_false]
          exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq
            _ rfl
  | restrict ty roles =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i bounded
      have contains := restrict_contains distinct roles (by simpa using bounded)
      refine (bind_congr_left (restrict_rule model actions tables protocols context _ ty roles _ _) _).trans ?_
      simp only [contains, PIR.Process.bind]
      split at normalized
      · rename_i member
        simp only [member, Participant.restrict, ite_true]
        exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq
          _ rfl
      · rename_i notMember
        simp only [Participant.restrict, Bool.not_eq_true] at notMember ⊢
        simp only [notMember, Bool.false_eq_true, ite_false]
        exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq
          _ rfl
  | assemble ty roles =>
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i bounded
      refine (bind_congr_left (assemble_rule model actions tables protocols context _ ty roles _ _) _).trans ?_
      simp only [PIR.Process.bind]
      exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq
        _ (by
          simp only [Comps.eval]
          congr 1
          rw [assemble_eval distinct results state.env binders roles (by simpa using bounded) args]
          simp only [lookup_eq_eval, comps_eval_operands]
          rfl)
  | draw owner field site =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i bounded
      refine (bind_congr_left (draw_rule model actions tables protocols context _ owner field site _ _) _).trans ?_
      simp only [lookup, Comps.eval]
      split at normalized
      · rename_i other
        have different : context.roles owner ≠ context.roles role :=
          distinct owner (by omega) (by simpa using other)
        simp only [Participant.query, different, ite_false]
        exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq
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
            simp only [Participant.query, ite_true, stored, Comp.eval,
              Form.denoteOn, Form.denoteWithOn, Terms.eval,
              PIR.Process.bind_assoc]
            have present : RoleFamily.sequence (Value := model.Value)
                (.cons (some (handle.eval results binders)) (.nil : Values (Component model.Value) [])) =
                  some (.cons (handle.eval results binders) .nil) := rfl
            erw [present]
            simp only [PIR.Process.interpret, PIR.Process.bind_assoc]
            refine congrArg (PIR.Process.bind _) (funext fun reply => ?_)
            exact continue_weaken_push sig results processes _ inputs nextRegion next sound state _ reply _ restForm rest
              matched binders inputsEq _ rfl
        · cases normalized
  | guard owner site =>
    rcases args with _ | ⟨arg, _ | _⟩
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i bounded
      refine (bind_congr_left (guard_rule model actions tables protocols context _ owner site _ _) _).trans ?_
      split at normalized
      · rename_i other
        have different : context.roles owner ≠ context.roles role :=
          distinct owner (by omega) (by simpa using other)
        simp only [Participant.guard, different, ite_false]
        exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq
          _ rfl
      · rename_i own
        have same : owner = role := by simpa using own
        subst same
        split at normalized
        · rename_i stored
          cases normalized
          simp [Participant.guard, stored, Comp.eval, PIR.Process.bind, PIR.Process.interpret,
            Form.denoteOn, Form.denoteWithOn]
        · rename_i condition stored
          split at normalized
          · rename_i decided
            simp only [Participant.guard, stored, Comp.eval, decision_holds results binders condition decided,
              ite_true]
            exact continue_push sig results processes _ inputs nextRegion next sound state _ form normalized matched binders inputsEq
              _ rfl
          · rename_i decided
            cases normalized
            simp [Participant.guard, stored, Comp.eval, decision_fails results binders condition decided,
              PIR.Process.bind, PIR.Process.interpret, Form.denoteOn, Form.denoteWithOn]
          · rename_i ty equality left right decided
            cases rest : next ((state.set arg (.present (.bool true))).push .nil) with
            | error refusal => rw [rest, except_bind_error] at normalized; cases normalized
            | ok restForm =>
              rw [rest, except_bind_ok] at normalized
              cases normalized
              simp only [Participant.guard, stored, Comp.eval, decision_compare results binders condition equality
                left right decided, ite_true, Form.denoteOn, Form.denoteWithOn, PIR.Process.bind_assoc]
              by_cases holds : left.eval results binders = right.eval results binders
              · simp only [holds, decide_true, ite_true]
                have kept : Comps.eval results (state.set arg (.present (.bool true))).env binders =
                    Comps.eval results state.env binders :=
                  comps_eval_set results binders state.env arg _ (by
                    simp only [← entryAt_eq_get, stored, Comp.eval, Term.eval, decision_compare results binders
                      condition equality left right decided, holds, decide_true])
                have step := continue_push sig results processes _ inputs nextRegion next sound
                  (state.set arg (.present (.bool true))) .nil restForm rest matched binders inputsEq _ rfl
                rw [kept] at step
                exact step
              · simp only [holds, decide_false, Bool.false_eq_true, ite_false]
                rfl
          · obtain ⟨restForm, rest, built⟩ := except_bind_ok_inv normalized
            cases built
            simp only [Participant.guard, stored, Comp.eval, ite_true, Form.denoteOn, Form.denoteWithOn, Term.eval, PIR.Process.bind_assoc]
            by_cases holds : condition.eval results binders = true
            · simp only [holds, ite_true, PIR.Process.bind]
              have kept : Comps.eval results (state.set arg (.present (.bool true))).env binders =
                  Comps.eval results state.env binders :=
                comps_eval_set results binders state.env arg _ (by
                  simp only [← entryAt_eq_get, stored, Comp.eval, Term.eval, holds])
              have step := continue_push sig results processes _ inputs nextRegion next sound
                (state.set arg (.present (.bool true))) .nil restForm rest matched binders inputsEq _ rfl
              rw [kept] at step
              exact step
            · simp only [holds, Bool.false_eq_true, ite_false, PIR.Process.interpret, PIR.Process.bind]
        · cases normalized
  | statement relation types selectors acceptance =>
    simp only [operation] at normalized
    refine (bind_congr_left (statement_rule model actions tables protocols context _ relation types selectors acceptance
      _ _) _).trans ?_
    exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq _ rfl
  | mark site =>
    rcases args with _ | _
    simp only [operation] at normalized
    refine (bind_congr_left (mark_rule model actions tables protocols context _ site _) _).trans ?_
    exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched binders inputsEq _ rfl
  | protocolApply signature roles site =>
    simp only [operation] at normalized
    split at normalized
    · cases normalized
    · rename_i valid
      simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_or, Bool.not_eq_true,
        bne_iff_ne, ne_eq, Decidable.not_not] at valid
      obtain ⟨⟨bounded, length⟩, nodup⟩ := valid
      refine (bind_congr_left (apply_rule model actions tables protocols context _ signature roles site _ _) _).trans ?_
      split at normalized
      · rename_i absent
        rw [contains_absent distinct signature roles site bounded length (rolePosition_none roles absent)]
        simp only [Bool.false_eq_true, ite_false]
        exact continue_push sig results processes role inputs nextRegion next sound state _ form normalized matched
          binders inputsEq _ (comps_eval_absent results binders signature.outputs)
      · rename_i position found
        obtain ⟨bound, located⟩ := rolePosition_some roles position found
        rw [contains_present context role signature roles site length position bound located]
        simp only [ite_true]
        simp only [applyCallee] at normalized
        split at normalized
        · cases normalized
        · rename_i callee inputsSame outputsSame calleeFound
          have calleeRole := findCallee_role sig.names signature position sig.callees _ calleeFound
          split at normalized
          · cases normalized
          · rename_i arguments argumentsFound
            split at normalized
            · rename_i pinned
              obtain ⟨restForm, rest, built⟩ := except_bind_ok_inv normalized
              cases built
              obtain ⟨same, restMatched⟩ := matched
              subst same
              simp only [recast_rfl] at argumentsFound rest
              obtain ⟨others, filled⟩ := calleeArguments_fill results binders _ _ _ argumentsFound
              have distinctChild := distinct_enter distinct _ roles site bounded length nodup position bound located
              rw [← calleeRole] at distinctChild
              have summary := calleesHold callee (context.enter site roles) _ others
                (calleePinsMatch_pinned results state.inputs inputs binders inputsEq _ _ pinned) distinctChild
              have self : (context.enter site roles).roles (calleeAt sig.callees callee).role = context.roles role := by
                rw [calleeRole, enter_roles _ _ _ _ bound, located]
              rw [self, ← filled] at summary
              refine (bind_congr_left summary _).trans ?_
              refine (PIR.Process.bind_assoc _ _ _).trans ?_
              simp only [Form.denoteOn, Form.denoteWithOn]
              apply congrArg
              funext values
              rw [calleeRole]
              exact continue_weaken_push sig results processes _ inputs nextRegion next sound state _ values _
                restForm rest restMatched binders inputsEq _
                (comps_eval_calleeOutputs results binders position values _ _)
            · cases normalized
  | «repeat» spec site =>
    rcases args with _ | ⟨count, rest⟩
    rcases bodies with _ | ⟨callback, _ | _⟩
    simp only [operation] at normalized
    obtain ⟨after, continued, built⟩ := except_bind_ok_inv normalized
    cases built
    refine (bind_congr_left (repeat_rule model actions tables protocols context _ spec site _ _ _) _).trans ?_
    simp only [comps_eval_split, Form.denoteOn, Form.denoteWithOn]
    apply congrArg
    funext values
    exact continue_weaken_push sig results processes _ inputs nextRegion next sound state _ values _ after continued
      matched binders inputsEq _ (comps_eval_reads (types := spec.state) results binders values)

theorem normalizeRegion_soundOn (sig : Signature) (results : LawResults model sig.laws)
    (processes : CalleeProcesses model sig.callees I) (role roster : Nat)
    (distinct : RosterDistinct context role roster) {Γ₀ : List Ty} (inputs : Values (Component model.Value) Γ₀)
    (lawsHold : LawsHold tables results inputs)
    (calleesHold : CalleesHold protocols processes inputs) {out : List Ty} :
    {Γ : List Ty} → (region : Region protocolDialect Γ out) →
      Continues model actions iterations tables protocols context sig results processes role inputs region
        (fun state => normalizeRegion sig role roster region state)
  | _, .ret values => by
    intro state form normalized _ binders _
    simp only [normalizeRegion, Except.ok.injEq] at normalized
    subst normalized
    simp only [Region.denote, Form.denoteOn, Form.denoteWithOn, lookup_eq_eval, comps_eval_operands]
  | _, .stop reason => by
    intro state form normalized _ binders _
    simp only [normalizeRegion, Except.ok.injEq] at normalized
    subst normalized
    rfl
  | _, .letOp op args bodies next => by
    intro state form normalized matched binders inputsEq
    exact resolve_sound sig results processes role inputs (.letOp op args bodies next) op args _
      (operation_sound sig results processes role roster distinct inputs lawsHold calleesHold op args bodies next _
        (normalizeRegion_soundOn sig results processes role roster distinct inputs lawsHold calleesHold next))
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
        change Values.cons (some (entryAt (V := Slot.Value model) binders' (lift .here))) (Comps.eval results (InputPattern.initialIn
            (laws := laws) rest fun binder => lift (.there binder)) binders') =
          Values.cons (some value) (InputPattern.environment model rest tail)
        rw [entryAt_eq_get, placed .here, initialIn_eval results binders' rest _ tail fun binder => placed (.there binder)]
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
        change (Values.cons (entryAt (V := Slot.Value model) binders' (lift .here)) (Comps.eval results (InputPattern.initialIn
            (laws := laws) rest fun binder => lift (.there binder)) binders') : Values (Component model.Value) _) =
          (Values.cons value (InputPattern.environment model rest tail) : Values (Component model.Value) _)
        rw [entryAt_eq_get, placed .here, initialIn_eval results binders' rest _ tail fun binder => placed (.there binder)]
        rfl
    exact step lift binders placed
  | _ :: _, .cons .absent rest, lift, binders, placed =>
    congrArg (Values.cons _) (initialIn_eval results binders' rest lift binders placed)
  | _ :: _, .cons (.capability ..) rest, lift, binders, placed =>
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

/-- Successful normalization preserves the complete observation-parametric process
of the same typed body on the pattern's inputs. Calls must match their exact
helper/callee keys; the tables must satisfy the input-pinned `LawsHold` and
`CalleesHold` equations. The context only needs distinct roster coordinates.
Actions, iteration observations, provider replies and all outputs are retained. -/
theorem normalize_soundOn (sig : Signature) {Γ out : List Ty} (body : Region protocolDialect Γ out)
    (role roster : Nat) (pattern : InputPattern Γ) (form : Form sig.laws sig.callees pattern.scope out)
    (normalized : normalize sig body role roster pattern = .ok form) (matched : form.CallsMatch)
    (distinct : RosterDistinct context role roster) (results : LawResults model sig.laws)
    (processes : CalleeProcesses model sig.callees I) (binders : Binders model pattern.scope)
    (lawsHold : LawsHold tables results (pattern.environment model binders))
    (calleesHold : CalleesHold protocols processes (pattern.environment model binders)) :
    body.denote (meaningAtOn model actions iterations tables protocols context role) (pattern.environment model binders).get =
      form.denoteOn model actions tables results context (runsAtOn model actions iterations tables protocols context role) processes binders := by
  have initial := initial_eval (laws := sig.laws) results pattern binders
  have sound := normalizeRegion_soundOn (actions := actions) (iterations := iterations) (protocols := protocols) sig results processes role roster distinct
    (pattern.environment model binders) lawsHold calleesHold body ⟨pattern.initial, pattern.initial⟩ form normalized
    (form.lawsMatch_of_callsMatch matched) binders initial
  rw [initial] at sound
  exact sound

end Main

/-- The plain participant meaning is the silent observation specialization. -/
abbrev meaningAt (model : DomainModel) (tables : Tables model)
    (protocols : ProtocolTable model.Value (Interface model)) (context : ProtocolContext) (role : Nat) :=
  meaningAtOn model (participantActionsOn model.toCarriers) .silent tables protocols context role

/-- Plain repeats are the silent observation specialization. -/
def runsAt (model : DomainModel) (tables : Tables model)
    (protocols : ProtocolTable model.Value (Interface model)) (context : ProtocolContext) (role : Nat) :=
  runsAtOn model (participantActionsOn model.toCarriers) .silent tables protocols context role

/-- Plain soundness follows from the observation-parametric theorem. -/
theorem normalize_sound {model : DomainModel} {tables : Tables model}
    {protocols : ProtocolTable model.Value (Interface model)} {context : ProtocolContext}
    (sig : Signature) {Γ out : List Ty} (body : Region protocolDialect Γ out)
    (role roster : Nat) (pattern : InputPattern Γ) (form : Form sig.laws sig.callees pattern.scope out)
    (normalized : normalize sig body role roster pattern = .ok form) (matched : form.CallsMatch)
    (distinct : RosterDistinct context role roster) (results : LawResults model sig.laws)
    (processes : CalleeProcesses model sig.callees) (binders : Binders model pattern.scope)
    (lawsHold : LawsHold tables results (pattern.environment model binders))
    (calleesHold : CalleesHold protocols processes (pattern.environment model binders)) :
    body.denote (meaningAt model tables protocols context role) (pattern.environment model binders).get =
      form.denote model tables results context (runsAt model tables protocols context role) processes binders :=
  normalize_soundOn (actions := participantActionsOn model.toCarriers) (iterations := .silent)
    sig body role roster pattern form normalized matched distinct results processes binders lawsHold calleesHold

end NormalForm
end Zkc.Source.Structured
