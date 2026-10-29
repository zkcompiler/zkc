module

public import Zkc.Source.Structured.NormalForm.Soundness

@[expose] public section

/-! Input visibility and output masks for typed source normal forms.
These facts depend only on source semantics. Construction certificates and
mathematical property bindings consume the same checked masks. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.InputVisibility
open NormalForm

/-- Every scope coordinate belongs to the declaration's roster. -/
def scopesBounded (roster : Nat) (scopes : List (List Nat)) : Bool :=
  scopes.all fun scope => !(scope.any (roster ≤ ·))

/-- Hidden inputs must be absent in the template; visible inputs may retain
optional components, nominal values, or fixed capabilities and literals. -/
def patternVisible (role : Nat) : {types : List Ty} →
    InputPattern types → List (List Nat) → Bool
  | [], .nil, scopes => scopes.isEmpty
  | _ :: _, .cons input rest, scopes =>
    match scopes with
    | [] => false
    | scope :: scopes =>
      (match input with | .absent => !scope.contains role | _ => scope.contains role) &&
        patternVisible role rest scopes

/-- An optional binder for each visible input and an absent component for
each private input. Malformed scope lists remain rejected by `build`. -/
def rolePattern (role : Nat) : (types : List Ty) → List (List Nat) → InputPattern types
  | [], _ => .nil
  | _ :: types, scopes =>
    .cons (if (scopes.headD []).contains role then .optional else .absent)
      (rolePattern role types scopes.tail)

theorem mask_fill (model : DomainModel) (role : Nat) {types : List Ty}
    (pattern : InputPattern types) (scopes : List (List Nat))
    (checked : patternVisible role pattern scopes = true)
    (binders : Binders model pattern.scope)
    (others : Values (Component model.Value) pattern.absentTypes) :
    maskValues role scopes (pattern.fill model binders others) = pattern.environment model binders := by
  induction pattern generalizing scopes with
  | nil => rfl
  | cons input rest ih =>
    cases scopes with
    | nil => simp [patternVisible] at checked
    | cons scope scopes =>
      cases input with
      | present =>
        cases binders with
        | cons value binders =>
          have parts : scope.contains role = true ∧ patternVisible role rest scopes = true := by
            simpa only [patternVisible, Bool.and_eq_true_iff] using checked
          change Values.cons (Participant.restrict (scope.contains role) _) (maskValues role scopes
            (InputPattern.fill model rest binders others)) = Values.cons _ (InputPattern.environment model rest binders)
          rw [ih scopes parts.2 binders others]
          simp only [Participant.restrict, parts.1, ↓reduceIte]
      | optional =>
        cases binders with
        | cons value binders =>
          have parts : scope.contains role = true ∧ patternVisible role rest scopes = true := by
            simpa only [patternVisible, Bool.and_eq_true_iff] using checked
          change Values.cons (Participant.restrict (scope.contains role) _) (maskValues role scopes
            (InputPattern.fill model rest binders others)) = Values.cons _ (InputPattern.environment model rest binders)
          rw [ih scopes parts.2 binders others]
          simp only [Participant.restrict, parts.1, ↓reduceIte]
      | absent =>
        cases others with
        | cons value others =>
          have parts : scope.contains role = false ∧ patternVisible role rest scopes = true := by
            simpa only [patternVisible, Bool.and_eq_true_iff, Bool.not_eq_true'] using checked
          change Values.cons (Participant.restrict (scope.contains role) value) (maskValues role scopes
            (InputPattern.fill model rest binders others)) = Values.cons none (InputPattern.environment model rest binders)
          rw [ih scopes parts.2 binders others]
          simp only [Participant.restrict, parts.1, Bool.false_eq_true, ↓reduceIte]
      | capability | index | field | bool =>
        have parts : scope.contains role = true ∧ patternVisible role rest scopes = true := by
          simpa only [patternVisible, Bool.and_eq_true_iff] using checked
        simp only [InputPattern.fill, InputPattern.environment, maskValues, List.headD_cons,
          List.tail_cons, Participant.restrict, parts.1, ↓reduceIte]
        exact congrArg (Values.cons _) (ih scopes parts.2 binders others)

theorem mask_context {model : DomainModel} {context : ProtocolContext} {role roster : Nat}
    (distinct : RosterDistinct context role roster) {types : List Ty}
    (scopes : List (List Nat)) (bounded : scopesBounded roster scopes = true)
    (values : Values (Component model.Value) types) :
    maskValues (context.roles role) (context.mapScopes scopes) values = maskValues role scopes values := by
  induction values generalizing scopes with
  | nil => rfl
  | cons value rest ih =>
    cases scopes with
    | nil =>
      simp only [ProtocolContext.mapScopes, List.map_nil, maskValues, List.headD_nil,
        List.contains_nil, Participant.restrict, Bool.false_eq_true, ↓reduceIte, List.tail_nil]
      exact congrArg (Values.cons none) (ih [] rfl)
    | cons scope scopes =>
      have parts : (scope.any (roster ≤ ·)) = false ∧ scopesBounded roster scopes = true := by
        simpa only [scopesBounded, List.all_cons, Bool.and_eq_true_iff, Bool.not_eq_true'] using bounded
      simp only [ProtocolContext.mapScopes, List.map_cons, maskValues, List.headD_cons, List.tail_cons]
      rw [restrict_contains distinct scope parts.1]
      exact congrArg (Values.cons _) (ih scopes parts.2)

theorem staticMask_identity {model : DomainModel} {types : List Ty}
    (role : Nat) (scopes : List (List Nat)) (values : Values (Component model.Value) types) :
    staticMask role values scopes (Operands.identity types) = maskValues role scopes values := by
  have general : ∀ {kept : List Ty} (positions : Operands types kept) (scopes : List (List Nat)),
      staticMask role values scopes positions = maskValues role scopes (Operands.eval values.get positions) := by
    intro kept positions
    induction positions with
    | nil => intro scopes; rfl
    | cons position rest ih =>
      intro scopes
      simp only [staticMask, Operands.eval, maskValues, ih, Participant.restrict]

  rw [general]
  have same : Operands.eval values.get (Operands.identity types) = values :=
    values_ext fun position => congrFun (congrFun (Operands.get_eval_identity values.get) _) position
  rw [same]

end Zkc.Source.Structured.InputVisibility
