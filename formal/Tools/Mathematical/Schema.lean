import Tools.Mathematical.Codec

/-! Exact finite mathematical source schema. Bounds and canonical values are
checked before declarations are constructed. This layer rejects unknown fields
and wrong tag arities; registry resolution and typed elaboration follow it.
-/

set_option autoImplicit false
namespace Tools.Mathematical.Schema
open Zkc.Source.Mathematical

private def list : Raw.Attribute → Except String (List Raw.Attribute)
  | .array values => .ok values
  | _ => .error "math-schema"

private def string : Raw.Attribute → Except String String
  | .string text => .ok text
  | _ => .error "math-schema"

private def natural : Raw.Attribute → Except String Nat
  | .natural n => if n < Static.limit then .ok n else .error "math-natural"
  | _ => .error "math-natural"

private def reference {kind : Raw.ReferenceKind} (value : Raw.Attribute) :
    Except String (Raw.Reference kind) := return ⟨← natural value⟩

private def references {kind : Raw.ReferenceKind} (value : Raw.Attribute) :
    Except String (List (Raw.Reference kind)) := do (← list value).mapM reference

private def record (keys : List String) (value : Raw.Attribute) :
    Except String (String → Except String Raw.Attribute) := do
  let .object fields := value | throw "math-schema"
  Codec.ensure (fields.length == keys.length && keys.all (fun key => fields.any (·.1 == key)))
    "math-schema"
  return fun key => match fields.find? (·.1 == key) with
    | some (_, value) => .ok value
    | none => .error "math-schema"

private def staticAt : Nat → Raw.Attribute → Except String Static.Raw
  | 0, _ => throw "math-resource-limit"
  | fuel + 1, value => do
      match ← list value with
      | [.string "literal", value] => return .literal (← natural value)
      | [.string "parameter", value] => return .parameter (← natural value)
      | [.string "add", left, right] => return .add (← staticAt fuel left) (← staticAt fuel right)
      | [.string "multiply", left, right] =>
          return .multiply (← staticAt fuel left) (← staticAt fuel right)
      | [.string "pow2", value] => return .pow2 (← staticAt fuel value)
      | _ => throw "math-schema"

private def static := staticAt 65
private def statics (value : Raw.Attribute) := do (← list value).mapM static

private def typeUse (value : Raw.Attribute) : Except String Raw.TypeUse := do
  let field ← record ["type", "statics"] value
  return ⟨← reference (← field "type"), ← statics (← field "statics")⟩

private def typeUses (value : Raw.Attribute) := do (← list value).mapM typeUse

private def typeExpression (value : Raw.Attribute) : Except String Raw.TypeExpression := do
  match ← list value with
  | [.string "nominal", domain, name, arguments] =>
      return .nominal (← reference domain) (← string name) (← statics arguments)
  | [.string "product", elements] => return .product (← typeUses elements)
  | [.string "fin", count] => return .fin (← static count)
  | [.string "vector", element, count] => return .vector (← typeUse element) (← static count)
  | [.string "polynomial", domain, arity, degree, .string convention] =>
      let convention ← match convention with
        | "individual" => pure Raw.Degree.individual
        | "total" => pure Raw.Degree.total
        | _ => throw "math-schema"
      return .polynomial (← reference domain) (← static arity) (← static degree) convention
  | [.string "residual", domain, arity, degree] =>
      return .residual (← reference domain) (← static arity) (← static degree)
  | _ => throw "math-schema"

private def typeTemplate (value : Raw.Attribute) : Except String Raw.TypeTemplate := do
  let field ← record ["statics", "body"] value
  return ⟨← natural (← field "statics"), ← typeExpression (← field "body")⟩

private def identity (value : Raw.Attribute) : Except String Raw.Identity := do
  let field ← record ["name", "version", "digest"] value
  return ⟨← string (← field "name"), ← string (← field "version"), ← string (← field "digest")⟩

private def manifest (value : Raw.Attribute) : Except String Raw.Manifest := do
  let field ← record ["domains", "operations", "wires", "services", "laws"] value
  let table := fun key => do (← list (← field key)).mapM identity
  return ⟨← table "domains", ← table "operations", ← table "wires", ← table "services", ← table "laws"⟩

private def capabilityUse (value : Raw.Attribute) : Except String Raw.CapabilityUse := do
  let field ← record ["type", "statics"] value
  return ⟨← reference (← field "type"), ← statics (← field "statics")⟩

private def permission (value : Raw.Attribute) : Except String Raw.Permission := do
  let field ← record ["signature", "roles"] value
  return ⟨← capabilityUse (← field "signature"), ← references (← field "roles")⟩

private def capabilityType (value : Raw.Attribute) : Except String Raw.CapabilityType := do
  let field ← record ["identity", "statics", "arguments", "result"] value
  return ⟨← reference (← field "identity"), ← natural (← field "statics"),
    ← typeUses (← field "arguments"), ← typeUse (← field "result")⟩

private def port (value : Raw.Attribute) : Except String Raw.Port := do
  let field ← record ["roles", "type"] value
  return ⟨← references (← field "roles"), ← typeUse (← field "type")⟩

private def ports (value : Raw.Attribute) := do (← list value).mapM port

private def operation (value : Raw.Attribute) : Except String Raw.Operation := do
  let field ← record ["identity", "statics", "capabilities", "arguments", "result", "purity", "distinct"] value
  let purity ← match ← string (← field "purity") with
    | "total" => pure Raw.Purity.total
    | "ordered" => pure Raw.Purity.ordered
    | _ => throw "math-schema"
  let distinct ← (← list (← field "distinct")).mapM fun value => do
    let [a, b] ← list value | throw "math-schema"
    return (← natural a, ← natural b)
  return ⟨← reference (← field "identity"), ← natural (← field "statics"),
    ← (← list (← field "capabilities")).mapM capabilityUse,
    ← typeUses (← field "arguments"), ← typeUse (← field "result"), purity, distinct⟩

private def wire (value : Raw.Attribute) : Except String Raw.Wire := do
  let field ← record ["identity", "statics", "type"] value
  return ⟨← reference (← field "identity"), ← natural (← field "statics"), ← typeUse (← field "type")⟩

mutual
  private def region : Nat → Raw.Attribute → Except String Raw.Region
    | 0, _ => throw "math-resource-limit"
    | fuel + 1, value => do
        let field ← record ["captures", "nodes", "outputs"] value
        return ⟨← references (← field "captures"),
          ← (← list (← field "nodes")).mapM (node fuel), ← references (← field "outputs")⟩
  private def node : Nat → Raw.Attribute → Except String Raw.Node
    | 0, _ => throw "math-resource-limit"
    | fuel + 1, value => do
        match ← list value with
        | [.string "operation", op, parameters, attributes, arguments] =>
            return .operation (← reference op) (← statics parameters) attributes (← references arguments)
        | [.string "tuple", elements] => return .tuple (← references elements)
        | [.string "project", value, component] => return .project (← reference value) (← natural component)
        | [.string "map", count, body] => return .map (← static count) (← region fuel body)
        | [.string "fold", count, initial, body] =>
            return .fold (← static count) (← references initial) (← region fuel body)
        | _ => throw "math-schema"
end

private def relation (value : Raw.Attribute) : Except String Raw.Relation := do
  let field ← record ["statics", "public", "witness", "assumptions", "body"] value
  return ⟨← natural (← field "statics"), ← typeUses (← field "public"),
    ← typeUses (← field "witness"), ← references (← field "assumptions"), ← region 65 (← field "body")⟩

private def relationBinding (value : Raw.Attribute) : Except String Raw.RelationBinding := do
  let field ← record ["relation", "statics", "public", "witness"] value
  return ⟨← reference (← field "relation"), ← statics (← field "statics"),
    ← references (← field "public"), ← references (← field "witness")⟩

private def terminal (value : Raw.Attribute) : Except String Raw.Terminal := do
  match ← list value with
  | [.string "return", values] => return .ret (← references values)
  | [.string "stop", site, owner, .string reason] =>
      let reason ← match reason with
        | "reject" => pure PIR.Stop.reject
        | "abort" => pure PIR.Stop.abort
        | "exhausted" => pure PIR.Stop.exhausted
        | "incomplete" => pure PIR.Stop.incomplete
        | "refused" => pure PIR.Stop.refused
        | _ => throw "math-schema"
      return .stop (← natural site) (← reference owner) reason
  | _ => throw "math-schema"

mutual
  private def body : Nat → Raw.Attribute → Except String Raw.Body
    | 0, _ => throw "math-resource-limit"
    | fuel + 1, value => do
        let field ← record ["steps", "terminal"] value
        return ⟨← (← list (← field "steps")).mapM (step fuel), ← terminal (← field "terminal")⟩
  private def step : Nat → Raw.Attribute → Except String Raw.Step
    | 0, _ => throw "math-resource-limit"
    | fuel + 1, value => do
        match ← list value with
        | [.string "pure", value] => return .pure (← region 65 value)
        | [.string "local", site, owner, op, parameters, attributes, capabilities, arguments] =>
            return .local (← natural site) (← reference owner) (← reference op) (← statics parameters)
              attributes (← references capabilities) (← references arguments)
        | [.string "query", site, owner, capability, arguments] =>
            return .query (← natural site) (← reference owner) (← reference capability) (← references arguments)
        | [.string "guard", site, owner, condition] =>
            return .guard (← natural site) (← reference owner) (← reference condition)
        | [.string "message", site, wire, parameters, sender, receiver, value] =>
            return .message (← natural site) (← reference wire) (← statics parameters)
              (← reference sender) (← reference receiver) (← reference value)
        | [.string "invoke", site, definition, parameters, roles, capabilities, arguments] =>
            return .invoke (← natural site) (← reference definition) (← statics parameters)
              (← references roles) (← references capabilities) (← references arguments)
        | [.string "repeat", site, count, carried, initial, captures, nested] =>
            return .repeat (← natural site) (← static count) (← ports carried)
              (← references initial) (← references captures) (← body fuel nested)
        | _ => throw "math-schema"
end

private def definition (value : Raw.Attribute) : Except String Raw.Definition := do
  let field ← record ["statics", "roles", "capabilities", "arguments", "results", "relations", "body"] value
  return ⟨← natural (← field "statics"), ← natural (← field "roles"),
    ← (← list (← field "capabilities")).mapM permission,
    ← ports (← field "arguments"), ← ports (← field "results"),
    ← (← list (← field "relations")).mapM relationBinding, ← body 65 (← field "body")⟩

private def entry (value : Raw.Attribute) : Except String Raw.Entry := do
  let field ← record ["definition", "statics", "roles", "capabilities"] value
  return ⟨← reference (← field "definition"), ← (← list (← field "statics")).mapM natural,
    ← references (← field "roles"), ← references (← field "capabilities")⟩

private def module (value : Raw.Attribute) : Except String Raw.Module := do
  let field ← record ["roles", "types", "operations", "wires", "capabilityTypes", "roots", "relations", "definitions", "entry"] value
  return ⟨← (← list (← field "roles")).mapM string,
    ← (← list (← field "types")).mapM typeTemplate,
    ← (← list (← field "operations")).mapM operation,
    ← (← list (← field "wires")).mapM wire,
    ← (← list (← field "capabilityTypes")).mapM capabilityType,
    ← (← list (← field "roots")).mapM permission,
    ← (← list (← field "relations")).mapM relation,
    ← (← list (← field "definitions")).mapM definition, ← entry (← field "entry")⟩

def decode (value : Raw.Attribute) : Except String Raw.Subject := do
  let _ ← Codec.encode value
  let field ← record ["profile", "manifest", "module"] value
  Codec.ensure ((← string (← field "profile")) == "zkc.math.v1") "math-profile"
  return ⟨← manifest (← field "manifest"), ← module (← field "module")⟩

end Tools.Mathematical.Schema
