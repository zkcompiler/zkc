module

public import Zkc.Source.Structured.NormalForm.Normalize
public import ZkcTools.StructuredSource.OpenValues

@[expose] public section

/-! The compiled normalizer, for printing generated modules.

`structured-source normal-form SNAPSHOT REQUEST` admits the snapshot, selects a
protocol body (or the callback of one of its repeats, by site), runs the same
`normalize` the kernel evaluates, and prints the form as JSON. The run is not
trusted: a generated module states the form as a literal, and the kernel
checks the literal against the normalizer's own result. -/

namespace ZkcTools.StructuredSource.NormalForms
open Lean Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm

def nat (value : Nat) : Json := .num value

def slotJson : Slot → Json
  | .value ty => .arr #[.str "value", wireType ty]
  | .component ty => .arr #[.str "component", wireType ty]
  | .results types => .arr #[.str "results", .arr (types.map wireType).toArray]
  | .tuple types => .arr #[.str "tuple", .arr (types.map wireType).toArray]

def stopJson : PIR.Stop → Json
  | .reject => .str "reject" | .abort => .str "abort" | .exhausted => .str "exhausted"
  | .incomplete => .str "incomplete" | .refused => .str "refused"

def opJson : Op → Json
  | .indexConstant value => .arr #[.str "indexConstant", nat value]
  | .indexEqual => .arr #[.str "indexEqual"]
  | .fieldConstant domain value => .arr #[.str "fieldConstant", .str domain, nat value]
  | .fieldAdd domain => .arr #[.str "fieldAdd", .str domain]
  | .fieldSubtract domain => .arr #[.str "fieldSubtract", .str domain]
  | .fieldMultiply domain => .arr #[.str "fieldMultiply", .str domain]
  | .fieldEqual domain => .arr #[.str "fieldEqual", .str domain]
  | .groupIdentity domain => .arr #[.str "groupIdentity", .str domain]
  | .groupAdd domain => .arr #[.str "groupAdd", .str domain]
  | .groupScale group field => .arr #[.str "groupScale", .str group, .str field]
  | .groupEqual domain => .arr #[.str "groupEqual", .str domain]
  | .booleanConstant value => .arr #[.str "booleanConstant", .bool value]
  | .booleanAnd => .arr #[.str "booleanAnd"]
  | .booleanOr => .arr #[.str "booleanOr"]
  | .booleanXor => .arr #[.str "booleanXor"]
  | .booleanEqual => .arr #[.str "booleanEqual"]
  | .booleanNotEqual => .arr #[.str "booleanNotEqual"]
  | .select ty => .arr #[.str "select", wireType ty]
  | _ => .arr #[.str "unsupported"]

variable {laws : List LawKey}

mutual
  def termJson {Δ : Scope} {ty : Ty} : Term laws Δ ty → Json
    | .var binder => .arr #[.str "var", nat binder.index]
    | .result binder position => .arr #[.str "result", nat binder.index, nat position.index]
    | .index value => .arr #[.str "index", nat value]
    | .bool value => .arr #[.str "bool", .bool value]
    | .field domain value => .arr #[.str "field", .str domain, nat value]
    | .groupZero domain => .arr #[.str "groupZero", .str domain]
    | .calc op _ args position => .arr #[.str "calc", opJson op, .arr (termsJson args).toArray, nat position.index]
    | .law entry args position => .arr #[.str "law", nat entry.val, .arr (termsJson args).toArray, nat position.index]

  def termsJson {Δ : Scope} {types : List Ty} : Terms laws Δ types → List Json
    | .nil => []
    | .cons head tail => termJson head :: termsJson tail
end

def compJson {Δ : Scope} {ty : Ty} : Comp laws Δ ty → Json
  | .absent => .arr #[.str "absent"]
  | .present term => .arr #[.str "present", termJson term]
  | .input binder => .arr #[.str "input", nat binder.index]
  | .read binder position => .arr #[.str "read", nat binder.index, nat position.index]

def compsJson {Δ : Scope} : {types : List Ty} → Values (Comp laws Δ) types → List Json
  | [], .nil => []
  | _ :: _, .cons head tail => compJson head :: compsJson tail

def equalityJson {ty : Ty} : Equality ty → Json
  | .field domain => .arr #[.str "field", .str domain]
  | .group domain => .arr #[.str "group", .str domain]
  | .index => .arr #[.str "index"]

def formJson {out : List Ty} : {Δ : Scope} → Form laws Δ out → Json
  | _, .done values => .arr #[.str "done", .arr (compsJson values).toArray]
  | _, .halt reason => .arr #[.str "halt", stopJson reason]
  | _, .send ty site peer value next =>
    .arr #[.str "send", wireType ty, .str site, nat peer, termJson value, formJson next]
  | _, .receive ty site peer next => .arr #[.str "receive", wireType ty, .str site, nat peer, formJson next]
  | _, .query site request args next =>
    .arr #[.str "query", .str site, .str request, .arr (termsJson args).toArray, formJson next]
  | _, .split subject absent present =>
    .arr #[.str "split", compJson subject, formJson absent, formJson present]
  | _, .guard equality left right next =>
    .arr #[.str "guard", equalityJson equality, termJson left, termJson right, formJson next]
  | _, .strict helper args next =>
    .arr #[.str "strict", .str helper.name, .arr (termsJson args).toArray, formJson next]
  | _, .compute op _ args next => .arr #[.str "compute", opJson op, .arr (termsJson args).toArray, formJson next]

/-! Requests. -/

def decodeInput : (ty : Ty) → Json → Except String (Input ty)
  | _, .str "absent" => .ok .absent
  | _, .str "present" => .ok .present
  | _, .str "optional" => .ok .optional
  | .index, .arr #[.str "index", value] => return .index (← Format.decimal (← Format.string value))
  | .boolean, .arr #[.str "bool", .bool value] => .ok (.bool value)
  | .field domain, .arr #[.str "field", value] => return .field domain (← Format.decimal (← Format.string value))
  | _, _ => .error "normal-form-input"

def decodePattern : (types : List Ty) → List Json → Except String (InputPattern types)
  | [], [] => .ok .nil
  | ty :: types, item :: items => return .cons (← decodeInput ty item) (← decodePattern types items)
  | _, _ => .error "normal-form-input-count"

def decodeStop : Json → Except String PIR.Stop
  | .str "reject" => .ok .reject | .str "abort" => .ok .abort | .str "exhausted" => .ok .exhausted
  | .str "incomplete" => .ok .incomplete | .str "refused" => .ok .refused
  | _ => .error "normal-form-stop"

def decodePin : Json → Except String (Option Nat)
  | .null => .ok none
  | json => return some (← Format.decimal (← Format.string json))

/-- `[helper, shape, pins]`: a shape is `"returns"` or `["stops", reason]`; a pin is `null` or an input position. -/
def decodeLaw (definitions : List CheckedDefinition) (json : Json) : Except String LawKey := do
  let [name, shape, pins] ← Format.array json | throw "normal-form-law"
  let name ← Format.string name
  let some definition := definitions.find? (·.name == name) | throw "normal-form-helper"
  let shape ← match shape with
    | .str "returns" => pure LawShape.returns
    | .arr #[.str "stops", reason] => pure (LawShape.stops (← decodeStop reason))
    | _ => throw "normal-form-law-shape"
  let pins ← (← Format.array pins).mapM decodePin
  return ⟨definition.helper, shape, pins⟩

/-- A protocol body, or the callback of one of its repeats. -/
abbrev Body := Σ inputs outputs, Region protocolDialect inputs outputs

def findRepeat (site : String) : {Γ out : List Ty} → Region protocolDialect Γ out → Option Body
  | _, _, .ret _ => none
  | _, _, .stop _ => none
  | _, _, .bind body next => (findRepeat site body).orElse fun _ => findRepeat site next
  | _, _, .letOp op _ bodies next =>
    let inner : Option Body :=
      match op, bodies with
      | .repeat _ repeatSite, .cons callback .nil =>
        if repeatSite == site then some ⟨_, _, callback⟩ else findRepeat site callback
      | _, _ => none
    inner.orElse fun _ => findRepeat site next

/-- The request `[protocol, repeat, role, roster, pattern, laws, strict]`: a
protocol name, the site of the repeat whose callback is normalized (or
`null`), the role and roster size, one input pattern entry per input of the
body, the signature's laws and whether owned calls without a law are kept. -/
def run (program : Program) (request : Json) : Except String Json := do
  let [protocolName, repeatSite, role, roster, pattern, laws, strict] ← Format.array request
    | throw "normal-form-request"
  let protocolName ← Format.string protocolName
  let some definition := program.payload.protocols.find? (·.name == protocolName)
    | throw "normal-form-protocol"
  let body : Body ← match repeatSite with
    | .str site => match findRepeat site definition.body with
      | some found => pure found
      | none => throw "normal-form-repeat"
    | _ => pure ⟨_, _, definition.body⟩
  let role ← Format.decimal (← Format.string role)
  let roster ← Format.decimal (← Format.string roster)
  let laws ← (← Format.array laws).mapM (decodeLaw program.payload.definitions)
  let strict := strict == .bool true
  let ⟨inputs, _, region⟩ := body
  let pattern ← decodePattern inputs (← Format.array pattern)
  let form ← normalize ⟨laws, strict⟩ region role roster pattern
  return .mkObj [("status", .str "normalized"), ("scope", .arr (pattern.scope.map slotJson).toArray),
    ("form", formJson form)]

end ZkcTools.StructuredSource.NormalForms
