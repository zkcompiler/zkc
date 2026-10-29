module

public import Zkc.Source.Structured.NormalForm.Syntax

@[expose] public section

/-! The participant meaning of a form, over a domain model.

Binders are the values of a scope. Terms evaluate to values and components to
optional values. A form denotes a process under an action interpretation and
reached iteration observations. Sends, receives and service queries retain sites
qualified by the protocol context. Kept helpers and stopping calculations use
the original helper tables; conditions, all outputs and every stop are preserved.
The plain participant meaning specializes these observations to silent ones.

The meaning of a law's results is a table of functions (`LawResults`). Which
helper behaviour justifies them is a proposition (`LawsHold`), assumed by the
soundness theorem and discharged by each instance from the admitted helper's
own laws; the denotation itself never reads a helper body. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- The value of a total calculation: the same cases as `Evaluation.operationOn`. -/
def Op.evalTotal (model : DomainModel) : (op : Op) → op.total = true →
    Values model.Value op.arguments → Values model.Value op.results
  | .makeProduct _ _ fields, _, arguments => .cons (fields.pack arguments) .nil
  | .getProduct _ _ fields _ field, _, .cons value .nil =>
      .cons ((fields.unpack value).get field) .nil
  | .indexConstant value, _, .nil => .cons value .nil
  | .indexEqual, _, .cons a (.cons b .nil) => .cons (decide (a = b)) .nil
  | .indexLess, _, .cons a (.cons b .nil) => .cons (decide (a < b)) .nil
  | .indexPowerOfTwo, _, .cons n (.cons r .nil) => .cons (naturalPowerOfTwo n r) .nil
  | .multilinearRestrictPrefix _, _, .cons values (.cons point .nil) =>
      .cons (Polynomial.Multilinear.restrictPrefixValues values point) .nil
  | .vectorLength _, _, .cons values .nil => .cons values.length .nil
  | .fieldEmbed extension base, _, .cons value .nil =>
      .cons (model.embed extension base value) .nil
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
  | .collect _, total, _ | .map _, total, _ | .branch .., total, _ | .loop .., total, _ | .loopCondition .., total, _
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

variable {model : DomainModel} {laws : List LawKey} {callees : List CalleeKey}

mutual
  def Term.eval (results : LawResults model laws) {Δ : Scope} {ty : Ty} :
      Term laws Δ ty → Binders model Δ → model.Value ty
    | .var binder, binders => entryAt (V := Slot.Value model) binders binder
    | .result binder position, binders => (entryAt (V := Slot.Value model) binders binder).get position
    | .capability _ handle, _ => handle
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
  | .input binder, binders => entryAt (V := Slot.Value model) binders binder
  | .read binder position, binders => (entryAt (V := Slot.Value model) binders binder).get position

def Comps.eval (results : LawResults model laws) {Δ : Scope} :
    {types : List Ty} → Values (Comp laws Δ) types → Binders model Δ →
      Values (Component model.Value) types
  | _, .nil, _ => .nil
  | _, .cons head tail, binders => .cons (head.eval results binders) (Comps.eval results tail binders)

/-- A callee argument's value: a binder value of the callee's scope. -/
def Argument.eval (results : LawResults model laws) {Δ : Scope} :
    {slot : Slot} → Argument laws Δ slot → Binders model Δ → Slot.Value model slot
  | .value _, term, binders => Term.eval results (term : Term laws Δ _) binders
  | .component _, comp, binders => Comp.eval results (comp : Comp laws Δ _) binders
  | .results _, terms, binders => Terms.eval results terms binders
  | .tuple _, comps, binders => Comps.eval results comps binders

/-- A callee's binders from its arguments. -/
def Arguments.eval (results : LawResults model laws) {Δ : Scope} :
    {scope : Scope} → Values (Argument laws Δ) scope → Binders model Δ → Binders model scope
  | _, .nil, _ => .nil
  | _, .cons head tail, binders =>
    .cons (Argument.eval results head binders) (Arguments.eval results tail binders)

/-- The decision procedure of a compared sort. -/
def Equality.decide (model : DomainModel) : {ty : Ty} → Equality ty → DecidableEq (model.Value ty)
  | _, .field domain => model.fieldDecEq domain
  | _, .group domain => model.groupDecEq domain
  | _, .index => inferInstanceAs (DecidableEq Nat)
  | _, .boolean => inferInstanceAs (DecidableEq Bool)

/-- The plain participant interface over the model's carriers. -/
abbrev Interface (model : DomainModel) := participantInterfaceOn model.toCarriers

/-- Helper tables in the selected effect interface; helper sites remain silent. -/
abbrev Tables (model : DomainModel) (I : PIR.Signature := Interface model) :=
  Evaluation.ComponentTablesOn model.toCarriers I

/-- What a form's repeats run: the function a callback region denotes and the
repeat rule at the participant. The soundness theorem takes the participant
rules of the domain model; the uniform presentation takes the uniform ones,
which name the same constants as the readable processes. The retained repeat
site is passed to the runner; the source repeat interpreter supplies actual
dynamic induction indices. -/
structure Runs (model : DomainModel) (I : PIR.Signature := Interface model) where
  callback : (spec : RepeatSpec) → Region protocolDialect (.index :: (spec.state ++ spec.captures)) spec.state →
    RegionFunction (Component model.Value) I (.index :: (spec.state ++ spec.captures), spec.state)
  run : (spec : RepeatSpec) → Option Nat → Values (Component model.Value) spec.state →
    Values (Component model.Value) spec.captures →
    RegionFunction (Component model.Value) I (.index :: (spec.state ++ spec.captures), spec.state) →
    (site : String := "") → PIR.Process I (Values (Component model.Value) spec.state)

/-- The callees' presented processes, one per callee of the signature, at a child
context and on the callee's binders. -/
abbrev CalleeProcesses (model : DomainModel) (callees : List CalleeKey)
    (I : PIR.Signature := Interface model) :=
  (callee : Fin callees.length) → ProtocolContext → Binders model (calleeAt callees callee).pattern.scope →
    PIR.Process I (Values (Component model.Value) (calleeAt callees callee).signature.outputs)

section Denote
variable (model) {I : PIR.Signature}
  (actions : PIR.OperationInterpretation (Interface model) I) (tables : Tables model I) (results : LawResults model laws)
  (context : ProtocolContext) (runs : Runs model I) (processes : CalleeProcesses model callees I) {out : List Ty}

/-- A form's process, with the given meaning of its returned tuples. -/
def Form.denoteWithOn {A : Type}
    (leaf : {Δ : Scope} → Values (Comp laws Δ) out → Binders model Δ → PIR.Process I A) :
    {Δ : Scope} → Form laws callees Δ out → Binders model Δ → PIR.Process I A
  | _, .done values, binders => leaf values binders
  | _, .halt reason, _ => .halt reason
  | _, .send ty site peer value next, binders =>
      (actions (.send (ty := ty) (qualifyProtocolSite context.applicationPrefix site) (context.roles peer)
        (value.eval results binders))).bind fun _ => next.denoteWithOn leaf binders
  | _, .receive ty site peer next, binders =>
      (actions (.receive ty (qualifyProtocolSite context.applicationPrefix site) (context.roles peer))).bind
        fun reply => next.denoteWithOn leaf (.cons reply binders)
  | _, .query site request args next, binders =>
      (actions (.query (qualifyProtocolSite context.applicationPrefix site) request
        (Terms.eval results args binders))).bind fun reply => next.denoteWithOn leaf (.cons reply binders)
  | _, .split subject absent present, binders =>
      match subject.eval results binders with
      | none => absent.denoteWithOn leaf binders
      | some value => present.denoteWithOn leaf (.cons value binders)
  | _, .guard equality left right next, binders =>
      @ite _ (left.eval results binders = right.eval results binders)
        (equality.decide model _ _) (next.denoteWithOn leaf binders) (.halt .reject)
  | _, .strict helper args next, binders =>
      (invoke tables.closed helper (Terms.eval results args binders)).bind fun values =>
        next.denoteWithOn leaf (.cons values binders)
  | _, .compute op allowed args next, binders =>
      (Evaluation.operationOn model (.silent _) tables.closed op (Terms.eval results args binders)
        (op.calculationRegions allowed)).bind fun values =>
          next.denoteWithOn leaf (.cons values binders)
  | _, .math helper args next, binders =>
      (invoke tables.components helper (Comps.eval results args binders)).bind fun values =>
        next.denoteWithOn leaf (.cons values binders)
  | _, .byLaw _ _ next, binders => next.denoteWithOn leaf binders
  | _, .owned owner helper args next, binders =>
      (Participant.owned (context.roles owner) (context.roles owner) (invoke tables.closed helper)
        (Comps.eval results args binders)).bind fun values => next.denoteWithOn leaf (.cons values binders)
  | _, .repeat spec site callback count state captures next, binders =>
      (runs.run spec (count.eval results binders) (Comps.eval results state binders)
        (Comps.eval results captures binders) (runs.callback spec callback) site).bind fun values =>
          next.denoteWithOn leaf (.cons values binders)
  | _, .apply callee _ roles site args next, binders =>
      (processes callee (context.enter site roles) (Arguments.eval results args binders)).bind fun values =>
        next.denoteWithOn leaf (.cons values binders)

/-- A form's process, returning its tuple of components. -/
def Form.denoteOn {Δ : Scope} (form : Form laws callees Δ out) (binders : Binders model Δ) :
    PIR.Process I (Values (Component model.Value) out) :=
  form.denoteWithOn model actions tables results context runs processes
    (fun values binders => .done (Comps.eval results values binders)) binders

end Denote

/-- The plain form meaning is the silent specialization of the observation-parametric meaning. -/
def Form.denoteWith (model : DomainModel) (tables : Tables model) (results : LawResults model laws)
    (context : ProtocolContext) (runs : Runs model) (processes : CalleeProcesses model callees)
    {out : List Ty} {A : Type}
    (leaf : {Δ : Scope} → Values (Comp laws Δ) out → Binders model Δ → PIR.Process (Interface model) A)
    {Δ : Scope} (form : Form laws callees Δ out) (binders : Binders model Δ) : PIR.Process (Interface model) A :=
  form.denoteWithOn model (participantActionsOn model.toCarriers) tables results context runs processes leaf binders

/-- The plain form meaning, retaining its complete returned tuple. -/
def Form.denote (model : DomainModel) (tables : Tables model) (results : LawResults model laws)
    (context : ProtocolContext) (runs : Runs model) (processes : CalleeProcesses model callees)
    {out : List Ty} {Δ : Scope} (form : Form laws callees Δ out) (binders : Binders model Δ) :
    PIR.Process (Interface model) (Values (Component model.Value) out) :=
  form.denoteOn model (participantActionsOn model.toCarriers) tables results context runs processes binders

/-- The inputs the pattern's binders give. -/
def InputPattern.environment (model : DomainModel) : {Γ : List Ty} → (pattern : InputPattern Γ) →
    Binders model pattern.scope → Values (Component model.Value) Γ
  | [], .nil, _ => .nil
  | ty :: _, .cons .present rest, binders =>
    let binders : Values (Slot.Value model) (.value ty :: InputPattern.scope rest) := binders
    match binders with
    | .cons value binders => .cons (some value) (environment model rest binders)
  | ty :: _, .cons .optional rest, binders =>
    let binders : Values (Slot.Value model) (.component ty :: InputPattern.scope rest) := binders
    match binders with
    | .cons value binders => .cons value (environment model rest binders)
  | _ :: _, .cons .absent rest, binders => .cons none (environment model rest binders)
  | _ :: _, .cons (.capability _ handle) rest, binders =>
    .cons (some handle) (environment model rest binders)
  | _ :: _, .cons (.index value) rest, binders => .cons (some value) (environment model rest binders)
  | _ :: _, .cons (.field domain value) rest, binders =>
    .cons (some (fieldLiteral model.toFieldModel domain value)) (environment model rest binders)
  | _ :: _, .cons (.bool value) rest, binders => .cons (some value) (environment model rest binders)

/-- The sorts of the inputs a pattern leaves absent. -/
def InputPattern.absentTypes : {Γ : List Ty} → InputPattern Γ → List Ty
  | [], .nil => []
  | ty :: _, .cons .absent rest => ty :: absentTypes rest
  | _ :: _, .cons .present rest => absentTypes rest
  | _ :: _, .cons .optional rest => absentTypes rest
  | _ :: _, .cons (.capability ..) rest => absentTypes rest
  | _ :: _, .cons (.index _) rest => absentTypes rest
  | _ :: _, .cons (.field ..) rest => absentTypes rest
  | _ :: _, .cons (.bool _) rest => absentTypes rest

/-- The inputs a pattern's binders give, with `others` at the absent positions. -/
def InputPattern.fill (model : DomainModel) : {Γ : List Ty} → (pattern : InputPattern Γ) →
    Binders model pattern.scope → Values (Component model.Value) pattern.absentTypes →
      Values (Component model.Value) Γ
  | [], .nil, _, _ => .nil
  | ty :: _, .cons .present rest, binders, others =>
    let binders : Values (Slot.Value model) (.value ty :: InputPattern.scope rest) := binders
    match binders with
    | .cons value binders => .cons (some value) (fill model rest binders others)
  | ty :: _, .cons .optional rest, binders, others =>
    let binders : Values (Slot.Value model) (.component ty :: InputPattern.scope rest) := binders
    match binders with
    | .cons value binders => .cons value (fill model rest binders others)
  | ty :: _, .cons .absent rest, binders, others =>
    let others : Values (Component model.Value) (ty :: InputPattern.absentTypes rest) := others
    match others with
    | .cons other others => .cons other (fill model rest binders others)
  | _ :: _, .cons (.capability _ handle) rest, binders, others =>
    .cons (some handle) (fill model rest binders others)
  | _ :: _, .cons (.index value) rest, binders, others => .cons (some value) (fill model rest binders others)
  | _ :: _, .cons (.field domain value) rest, binders, others =>
    .cons (some (fieldLiteral model.toFieldModel domain value)) (fill model rest binders others)
  | _ :: _, .cons (.bool value) rest, binders, others => .cons (some value) (fill model rest binders others)

/-- A participant's view of a returned tuple at the given positions: the
positions whose scope contains its role; the others are absent. -/
def staticMask {V : Ty → Type} (role : Nat) {types : List Ty} (values : Values (Component V) types) :
    List (List Nat) → {kept : List Ty} → Values (Var types) kept → Values (Component V) kept
  | _, _, .nil => .nil
  | scopes, _, .cons position rest =>
    .cons (if (scopes.headD []).contains role then values.get position else none)
      (staticMask role values scopes.tail rest)

/-! Hypotheses of the soundness theorem. -/

/-- A literal's value: an index, a Boolean (`1` is true) or a field element. -/
def literalValue (model : DomainModel) : (ty : Ty) → Nat → Option (model.Value ty)
  | .index, value => some value
  | .boolean, value => some (value == 1)
  | .field domain, value => some (fieldLiteral model.toFieldModel domain value)
  | .vector _, _ => none
  | .group _, _ => none
  | .service _, _ => none
  | .sequence _, _ | .product .., _ => none

/-- The arguments a law covers: each argument pinned to an input is that
input's present value, and each argument pinned to a literal is that literal. A
pin that names no input of the argument's sort covers nothing. -/
def Pinned {Γ₀ : List Ty} (inputs : Values (Component model.Value) Γ₀) :
    {types : List Ty} → List LawPin → Values model.Value types → Prop
  | [], _, .nil => True
  | _ :: _, [], .cons _ _ => True
  | ty :: _, pin :: pins, .cons value values =>
      (match pin with
        | .free => True
        | .input index =>
          match Var.decode Γ₀ ty index with
          | some binder => inputs.get binder = some value
          | none => False
        | .literal literal => literalValue model ty literal = some value) ∧ Pinned inputs pins values

/-- A returning law's results, mirroring `lawComps`: from the result function,
from the arguments, or literals. -/
def lawValues (model : DomainModel) (helper : Helper) (results : Values model.Value helper.outputs)
    (args : Values model.Value helper.inputs) :
    (types : List Ty) → ({ty : Ty} → Var types ty → Var helper.outputs ty) → List LawOutput →
      Option (Values model.Value types)
  | [], _, _ => some .nil
  | ty :: types, position, outputs =>
    let first : Option (model.Value ty) :=
      match outputs.headD .result with
      | .result => some (results.get (position .here))
      | .argument input => (Var.decode helper.inputs ty input).map (entryAt args)
      | .literal value => literalValue model ty value
    match first with
    | none => none
    | some value => (lawValues model helper results args types (fun binder => position (.there binder))
        outputs.tail).map (.cons value)

/-- The helper behaviour a law presents, on the arguments it covers. A passing
law is about the Math helper's meaning on components, for every argument. -/
def LawHolds {Γ₀ : List Ty} {I : PIR.Signature} (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (inputs : Values (Component model.Value) Γ₀) (key : LawKey)
    (result : Values model.Value key.helper.inputs → Values model.Value key.helper.outputs) : Prop :=
  match key.shape with
  | .returns outputs => ∀ args, Pinned inputs key.pins args → ∀ values,
      lawValues model key.helper (result args) args key.helper.outputs (fun position => position) outputs =
        some values → invoke tables.closed key.helper args = .done values
  | .stops reason => ∀ args, Pinned inputs key.pins args → invoke tables.closed key.helper args = .halt reason
  | .passes positions => ∀ (args : Values (Component model.Value) key.helper.inputs) values,
      passEntries args key.helper.outputs positions = some values →
        invoke tables.components key.helper args = .done values

/-- One premise per law of the signature. -/
def LawsHold {Γ₀ : List Ty} {I : PIR.Signature} (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (results : LawResults model laws) (inputs : Values (Component model.Value) Γ₀) : Prop :=
  ∀ entry : Fin laws.length, LawHolds tables inputs laws[entry] (results.result entry)

/-- Every law use of a form presents a call of the law's own helper. -/
def Form.LawsMatch {out : List Ty} : {Δ : Scope} → Form laws callees Δ out → Prop
  | _, .done _ => True
  | _, .halt _ => True
  | _, .send _ _ _ _ next => next.LawsMatch
  | _, .receive _ _ _ next => next.LawsMatch
  | _, .query _ _ _ next => next.LawsMatch
  | _, .split _ absent present => absent.LawsMatch ∧ present.LawsMatch
  | _, .guard _ _ _ next => next.LawsMatch
  | _, .strict _ _ next => next.LawsMatch
  | _, .compute _ _ _ next => next.LawsMatch
  | _, .math _ _ next => next.LawsMatch
  | _, .byLaw entry helper next => laws[entry].helper = helper ∧ next.LawsMatch
  | _, .owned _ _ _ next => next.LawsMatch
  | _, .repeat _ _ _ _ _ _ next => next.LawsMatch
  | _, .apply callee signature _ _ _ next => (calleeAt callees callee).signature = signature ∧ next.LawsMatch

/-- The law uses of a form with their called helpers, in order. -/
def Form.lawCalls {out : List Ty} : {Δ : Scope} → Form laws callees Δ out → List (Fin laws.length × Helper)
  | _, .done _ => []
  | _, .halt _ => []
  | _, .send _ _ _ _ next => next.lawCalls
  | _, .receive _ _ _ next => next.lawCalls
  | _, .query _ _ _ next => next.lawCalls
  | _, .split _ absent present => absent.lawCalls ++ present.lawCalls
  | _, .guard _ _ _ next => next.lawCalls
  | _, .strict _ _ next => next.lawCalls
  | _, .compute _ _ _ next => next.lawCalls
  | _, .math _ _ next => next.lawCalls
  | _, .byLaw entry helper next => (entry, helper) :: next.lawCalls
  | _, .owned _ _ _ next => next.lawCalls
  | _, .repeat _ _ _ _ _ _ next => next.lawCalls
  | _, .apply _ _ _ _ _ next => next.lawCalls

/-- The applications of a form with their applied signatures, in order. -/
def Form.calleeCalls {out : List Ty} : {Δ : Scope} → Form laws callees Δ out →
    List (Fin callees.length × ProtocolSignature)
  | _, .done _ => []
  | _, .halt _ => []
  | _, .send _ _ _ _ next => next.calleeCalls
  | _, .receive _ _ _ next => next.calleeCalls
  | _, .query _ _ _ next => next.calleeCalls
  | _, .split _ absent present => absent.calleeCalls ++ present.calleeCalls
  | _, .guard _ _ _ next => next.calleeCalls
  | _, .strict _ _ next => next.calleeCalls
  | _, .compute _ _ _ next => next.calleeCalls
  | _, .math _ _ next => next.calleeCalls
  | _, .byLaw _ _ next => next.calleeCalls
  | _, .owned _ _ _ next => next.calleeCalls
  | _, .repeat _ _ _ _ _ _ next => next.calleeCalls
  | _, .apply callee signature _ _ _ next => (callee, signature) :: next.calleeCalls

/-- The law uses' helpers, as an equation of two lists: an instance checks it
by definitional equality of helper terms, so equal helpers are recognized at
once and the kernel never evaluates a comparison of their names. -/
abbrev Form.CallsMatch {out : List Ty} {Δ : Scope} (form : Form laws callees Δ out) : Prop :=
  (form.lawCalls.map (fun call => laws[call.1].helper), form.calleeCalls.map fun call => (calleeAt callees call.1).signature) =
    (form.lawCalls.map Prod.snd, form.calleeCalls.map Prod.snd)

theorem Form.lawsMatch_of_lists {out : List Ty} :
    {Δ : Scope} → (form : Form laws callees Δ out) →
      form.lawCalls.map (fun call => laws[call.1].helper) = form.lawCalls.map Prod.snd →
      form.calleeCalls.map (fun call => (calleeAt callees call.1).signature) = form.calleeCalls.map Prod.snd →
        form.LawsMatch
  | _, .done _, _, _ => trivial
  | _, .halt _, _, _ => trivial
  | _, .send _ _ _ _ next, laws, applied => next.lawsMatch_of_lists laws applied
  | _, .receive _ _ _ next, laws, applied => next.lawsMatch_of_lists laws applied
  | _, .query _ _ _ next, laws, applied => next.lawsMatch_of_lists laws applied
  | _, .split _ absent present, laws, applied => by
    simp only [Form.lawCalls, Form.calleeCalls, List.map_append] at laws applied
    have lawParts := List.append_inj laws (by simp)
    have appliedParts := List.append_inj applied (by simp)
    exact ⟨absent.lawsMatch_of_lists lawParts.1 appliedParts.1,
      present.lawsMatch_of_lists lawParts.2 appliedParts.2⟩
  | _, .guard _ _ _ next, laws, applied => next.lawsMatch_of_lists laws applied
  | _, .strict _ _ next, laws, applied => next.lawsMatch_of_lists laws applied
  | _, .compute _ _ _ next, laws, applied => next.lawsMatch_of_lists laws applied
  | _, .math _ _ next, laws, applied => next.lawsMatch_of_lists laws applied
  | _, .byLaw _ _ next, laws, applied => by
    simp only [Form.lawCalls, List.map_cons, List.cons.injEq] at laws
    exact ⟨laws.1, next.lawsMatch_of_lists laws.2 applied⟩
  | _, .owned _ _ _ next, laws, applied => next.lawsMatch_of_lists laws applied
  | _, .repeat _ _ _ _ _ _ next, laws, applied => next.lawsMatch_of_lists laws applied
  | _, .apply _ _ _ _ _ next, laws, applied => by
    simp only [Form.calleeCalls, List.map_cons, List.cons.injEq] at applied
    exact ⟨applied.1, next.lawsMatch_of_lists laws applied.2⟩

theorem Form.lawsMatch_of_callsMatch {out : List Ty} {Δ : Scope} (form : Form laws callees Δ out)
    (same : form.CallsMatch) : form.LawsMatch :=
  form.lawsMatch_of_lists (congrArg Prod.fst same) (congrArg Prod.snd same)

/-- No callees: a body without applications. -/
def noCallees (model : DomainModel) (I : PIR.Signature := Interface model) : CalleeProcesses model [] I := fun callee => callee.elim0

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

/-- A callee binder pinned to a caller input is that input's present value. -/
def pinnedSlot {Γ₀ : List Ty} (inputs : Values (Component model.Value) Γ₀) :
    (slot : Slot) → Option Nat → Slot.Value model slot → Prop
  | _, none, _ => True
  | .value ty, some input, value =>
    match Var.decode Γ₀ ty input with
    | some binder => inputs.get binder = some value
    | none => False
  | .component _, some _, _ => False
  | .results _, some _, _ => False
  | .tuple _, some _, _ => False

/-- The callee binders the pins name are the caller inputs' values. -/
def CalleePinned {Γ₀ : List Ty} (inputs : Values (Component model.Value) Γ₀) :
    {scope : Scope} → List (Option Nat) → Binders model scope → Prop
  | [], _, _ => True
  | _ :: _, [], _ => True
  | slot :: _, pin :: pins, .cons value rest => pinnedSlot inputs slot pin value ∧ CalleePinned inputs pins rest

/-- Each callee's invocation at a participant of its roster is its presented
process followed by the participant's view of the returned tuple, on every
input its pattern describes; a pinned callee only at the caller's inputs. -/
def CalleesHold {Γ₀ : List Ty} {I : PIR.Signature} (protocols : ProtocolTable model.Value I)
    (processes : CalleeProcesses model callees I) (inputs : Values (Component model.Value) Γ₀) : Prop :=
  ∀ (callee : Fin callees.length) (context : ProtocolContext)
    (binders : Binders model (calleeAt callees callee).pattern.scope)
    (others : Values (Component model.Value) (calleeAt callees callee).pattern.absentTypes),
    CalleePinned inputs (calleeAt callees callee).pins binders →
    RosterDistinct context (calleeAt callees callee).role (calleeAt callees callee).signature.roles.length →
    invokeProtocol protocols (calleeAt callees callee).signature context (context.roles (calleeAt callees callee).role)
        ((calleeAt callees callee).pattern.fill model binders others) =
      (processes callee context binders).bind fun out =>
        .done (staticMask (calleeAt callees callee).role out (calleeAt callees callee).signature.outputScopes
          (Operands.identity (calleeAt callees callee).signature.outputs))

theorem noCallees_hold {Γ₀ : List Ty} {I : PIR.Signature} (protocols : ProtocolTable model.Value I)
    (inputs : Values (Component model.Value) Γ₀) : CalleesHold protocols (noCallees model I) inputs :=
  fun callee => callee.elim0

end NormalForm
end Zkc.Source.Structured
