module

public import Zkc.Source.Structured.NormalForm.Syntax

@[expose] public section

/-! The participant meaning of a form, over a domain model.

Binders are the values of a scope. Terms evaluate to values and components to
optional values. A form denotes a process of the plain participant interface:
sends, receives and service queries at sites qualified by the protocol
context, kept helper calls and stopping calculations through the helper
tables, decided conditions as conditionals and every other stop as itself.

The meaning of a law's results is a table of functions (`LawResults`). Which
helper behaviour justifies them is a proposition (`LawsHold`), assumed by the
soundness theorem and discharged by each instance from the admitted helper's
own laws; the denotation itself never reads a helper body. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- The value of a total calculation: the same cases as `Evaluation.operationOn`. -/
def Op.evalTotal (model : DomainModel) : (op : Op) → op.total = true →
    Values model.Value op.arguments → Values model.Value op.results
  | .indexConstant value, _, .nil => .cons value .nil
  | .indexEqual, _, .cons a (.cons b .nil) => .cons (decide (a = b)) .nil
  | .fieldConstant domain value, _, .nil => .cons (value : model.Field domain) .nil
  | .fieldAdd _, _, .cons a (.cons b .nil) => .cons (a + b) .nil
  | .fieldSubtract _, _, .cons a (.cons b .nil) => .cons (a - b) .nil
  | .fieldMultiply _, _, .cons a (.cons b .nil) => .cons (a * b) .nil
  | .fieldEqual _, _, .cons a (.cons b .nil) => .cons (decide (a = b)) .nil
  | .groupIdentity _, _, .nil => .cons 0 .nil
  | .groupAdd _, _, .cons a (.cons b .nil) => .cons (a + b) .nil
  | .groupScale group field, _, .cons point (.cons scalar .nil) =>
      .cons (model.smul group field scalar point) .nil
  | .groupEqual _, _, .cons a (.cons b .nil) => .cons (decide (a = b)) .nil
  | .booleanConstant value, _, .nil => .cons value .nil
  | .booleanAnd, _, .cons a (.cons b .nil) => .cons (a && b) .nil
  | .booleanOr, _, .cons a (.cons b .nil) => .cons (a || b) .nil
  | .booleanXor, _, .cons a (.cons b .nil) => .cons (xor a b) .nil
  | .booleanEqual, _, .cons a (.cons b .nil) => .cons (a == b) .nil
  | .booleanNotEqual, _, .cons a (.cons b .nil) => .cons (a != b) .nil
  | .select _, _, .cons condition (.cons yes (.cons no .nil)) =>
      .cons (if condition then yes else no) .nil
  | .exec _, total, _ | .boundedAt _, total, _ | .invoke _, total, _ | .fold _, total, _
  | .map _, total, _ | .branch .., total, _ | .loop .., total, _ | .loopCondition .., total, _
  | .guard, total, _ | .mark _, total, _ => nomatch total

namespace NormalForm

/-- The values of a binder. -/
abbrev Slot.Value (model : DomainModel) : Slot → Type
  | .value ty => model.Value ty
  | .component ty => Option (model.Value ty)
  | .results types => Values model.Value types
  | .tuple types => Values (Component model.Value) types

/-- The values of a scope, newest binder first. -/
abbrev Binders (model : DomainModel) (Δ : Scope) := Values (Slot.Value model) Δ

/-- Field literals as readable forms present them: `0`, `1`, or the cast. -/
def fieldLiteral (model : FieldModel) (domain : String) : Nat → model.Field domain
  | 0 => 0
  | 1 => 1
  | value + 2 => ((value + 2 : Nat) : model.Field domain)

theorem fieldLiteral_eq (model : FieldModel) (domain : String) (value : Nat) :
    fieldLiteral model domain value = (value : model.Field domain) := by
  match value with
  | 0 => simp [fieldLiteral]
  | 1 => simp [fieldLiteral]
  | _ + 2 => rfl

/-- The results each law presents, as functions of the call's arguments. -/
structure LawResults (model : DomainModel) (laws : List LawKey) where
  result : (entry : Fin laws.length) → Values model.Value laws[entry].helper.inputs →
    Values model.Value laws[entry].helper.outputs

variable {model : DomainModel} {laws : List LawKey}

mutual
  def Term.eval (results : LawResults model laws) {Δ : Scope} {ty : Ty} :
      Term laws Δ ty → Binders model Δ → model.Value ty
    | .var binder, binders => binders.get binder
    | .result binder position, binders => (binders.get binder).get position
    | .index value, _ => value
    | .bool value, _ => value
    | .field domain value, _ => fieldLiteral model.toFieldModel domain value
    | .groupZero _, _ => 0
    | .calc op total args position, binders =>
        (op.evalTotal model total (Terms.eval results args binders)).get position
    | .law entry args position, binders =>
        (results.result entry (Terms.eval results args binders)).get position

  def Terms.eval (results : LawResults model laws) {Δ : Scope} {types : List Ty} :
      Terms laws Δ types → Binders model Δ → Values model.Value types
    | .nil, _ => .nil
    | .cons head tail, binders => .cons (head.eval results binders) (Terms.eval results tail binders)
end

def Comp.eval (results : LawResults model laws) {Δ : Scope} {ty : Ty} :
    Comp laws Δ ty → Binders model Δ → Option (model.Value ty)
  | .absent, _ => none
  | .present term, binders => some (term.eval results binders)
  | .input binder, binders => binders.get binder
  | .read binder position, binders => (binders.get binder).get position

def Comps.eval (results : LawResults model laws) {Δ : Scope} :
    {types : List Ty} → Values (Comp laws Δ) types → Binders model Δ →
      Values (Component model.Value) types
  | [], .nil, _ => .nil
  | _ :: _, .cons head tail, binders => .cons (head.eval results binders) (Comps.eval results tail binders)

/-- The decision procedure of a compared sort. -/
def Equality.decide (model : DomainModel) : {ty : Ty} → Equality ty → DecidableEq (model.Value ty)
  | _, .field domain => model.fieldDecEq domain
  | _, .group domain => model.groupDecEq domain
  | _, .index => inferInstanceAs (DecidableEq Nat)

/-- The plain participant interface over the model's carriers. -/
abbrev Interface (model : DomainModel) := participantInterfaceOn model.toCarriers

/-- Plain helper tables with silent sites. -/
abbrev Tables (model : DomainModel) :=
  Evaluation.ComponentTablesOn model.toCarriers (Interface model)

section Denote
variable (model) (tables : Tables model) (results : LawResults model laws)
  (context : ProtocolContext) {out : List Ty}

/-- A form's process, with the given meaning of its returned tuples. -/
def Form.denoteWith {A : Type}
    (leaf : {Δ : Scope} → Values (Comp laws Δ) out → Binders model Δ → PIR.Proc (Interface model) A) :
    {Δ : Scope} → Form laws Δ out → Binders model Δ → PIR.Proc (Interface model) A
  | _, .done values, binders => leaf values binders
  | _, .halt reason, _ => .halt reason
  | _, .send ty site peer value next, binders =>
      .call (.send (ty := ty) (qualifyProtocolSite context.applicationPrefix site) (context.roles peer)
        (value.eval results binders)) fun _ => next.denoteWith leaf binders
  | _, .receive ty site peer next, binders =>
      .call (.receive ty (qualifyProtocolSite context.applicationPrefix site) (context.roles peer))
        fun reply => next.denoteWith leaf (.cons reply binders)
  | _, .query site request args next, binders =>
      .call (.query (qualifyProtocolSite context.applicationPrefix site) request
        (Terms.eval results args binders)) fun reply => next.denoteWith leaf (.cons reply binders)
  | _, .split subject absent present, binders =>
      match subject.eval results binders with
      | none => absent.denoteWith leaf binders
      | some value => present.denoteWith leaf (.cons value binders)
  | _, .guard equality left right next, binders =>
      @ite _ (left.eval results binders = right.eval results binders)
        (equality.decide model _ _) (next.denoteWith leaf binders) (.halt .reject)
  | _, .strict helper args next, binders =>
      (invoke tables.closed helper (Terms.eval results args binders)).bind fun values =>
        next.denoteWith leaf (.cons values binders)
  | _, .compute op allowed args next, binders =>
      (Evaluation.operationOn model (.silent _) tables.closed op (Terms.eval results args binders)
        (op.calculationRegions allowed)).bind fun values =>
          next.denoteWith leaf (.cons values binders)

/-- A form's process, returning its tuple of components. -/
def Form.denote {Δ : Scope} (form : Form laws Δ out) (binders : Binders model Δ) :
    PIR.Proc (Interface model) (Values (Component model.Value) out) :=
  form.denoteWith model tables results context (fun values binders => .done (Comps.eval results values binders))
    binders

end Denote

/-! Hypotheses of the soundness theorem. -/

/-- The arguments a law covers: each pinned argument is the present value of
its input. A pin that names no input of the argument's sort covers nothing. -/
def Pinned {Γ₀ : List Ty} (inputs : Values (Component model.Value) Γ₀) :
    {types : List Ty} → List (Option Nat) → Values model.Value types → Prop
  | [], _, .nil => True
  | _ :: _, [], .cons _ _ => True
  | ty :: _, pin :: pins, .cons value values =>
      (match pin with
        | none => True
        | some index =>
          match Var.decode Γ₀ ty index with
          | some binder => inputs.get binder = some value
          | none => False) ∧ Pinned inputs pins values

/-- The helper behaviour a law presents, on the arguments it covers. -/
def LawHolds {Γ₀ : List Ty} {I : PIR.Signature} (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (inputs : Values (Component model.Value) Γ₀) (key : LawKey)
    (result : Values model.Value key.helper.inputs → Values model.Value key.helper.outputs) : Prop :=
  ∀ args, Pinned inputs key.pins args →
    invoke tables.closed key.helper args =
      match key.shape with
      | .returns => .done (result args)
      | .stops reason => .halt reason

/-- One premise per law of the signature. -/
def LawsHold {Γ₀ : List Ty} {I : PIR.Signature} (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (results : LawResults model laws) (inputs : Values (Component model.Value) Γ₀) : Prop :=
  ∀ entry : Fin laws.length, LawHolds tables inputs laws[entry] (results.result entry)

/-- Every other role of the roster is played by a different participant. -/
def RosterDistinct (context : ProtocolContext) (role roster : Nat) : Prop :=
  ∀ other, other < roster → other ≠ role → context.roles other ≠ context.roles role

theorem RosterDistinct.root (role roster : Nat) : RosterDistinct {} role roster :=
  fun _ _ different same => different same

theorem RosterDistinct.ofSeparate {context : ProtocolContext} {role : Nat}
    (separate : context.roles (1 - role) ≠ context.roles role) (two : role < 2) :
    RosterDistinct context role 2 := by
  intro other bound different
  have : other = 1 - role := by omega
  subst this
  exact separate

theorem RosterDistinct.ofValid {rootRoles localRoles : List String} {context : ProtocolContext}
    (valid : ProtocolContext.Valid rootRoles localRoles context) (role : Nat)
    (bound : role < localRoles.length) : RosterDistinct context role localRoles.length :=
  fun other otherBound different same => different (valid.2 other otherBound role bound same)

end NormalForm
end Zkc.Source.Structured
