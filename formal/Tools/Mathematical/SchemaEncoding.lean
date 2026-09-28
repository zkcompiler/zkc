import Tools.Mathematical.Schema

/-! Explicit encoding of finite mathematical source records. Every field is
preserved; canonical byte validation runs before the encoded value is returned.
-/

set_option autoImplicit false
namespace Tools.Mathematical.SchemaEncoding
open Zkc.Source.Mathematical
open Raw.Attribute

private def refs {kind : Raw.ReferenceKind} (values : List (Raw.Reference kind)) : Raw.Attribute :=
  array (values.map fun value => natural value.index)

private def static : Static.Raw → Raw.Attribute
  | .literal n => array [string "literal", natural n]
  | .parameter n => array [string "parameter", natural n]
  | .add a b => array [string "add", static a, static b]
  | .multiply a b => array [string "multiply", static a, static b]
  | .pow2 a => array [string "pow2", static a]

private def statics (values : List Static.Raw) := array (values.map static)
private def typeUse (value : Raw.TypeUse) :=
  object [("type", natural value.type.index), ("statics", statics value.statics)]
private def typeUses (values : List Raw.TypeUse) := array (values.map typeUse)

private def typeExpression : Raw.TypeExpression → Raw.Attribute
  | .nominal domain name args => array [string "nominal", natural domain.index, string name, statics args]
  | .product elements => array [string "product", typeUses elements]
  | .fin count => array [string "fin", static count]
  | .vector element count => array [string "vector", typeUse element, static count]
  | .polynomial domain arity degree convention =>
      array [string "polynomial", natural domain.index, static arity, static degree,
        string (match convention with | .individual => "individual" | .total => "total")]
  | .residual domain arity degree => array [string "residual", natural domain.index, static arity, static degree]

private def typeTemplate (value : Raw.TypeTemplate) :=
  object [("statics", natural value.statics), ("body", typeExpression value.body)]
private def identity (value : Raw.Identity) :=
  object [("name", string value.name), ("version", string value.version), ("digest", string value.digest)]
private def manifest (value : Raw.Manifest) :=
  object [("domains", array (value.domains.map identity)), ("operations", array (value.operations.map identity)),
    ("wires", array (value.wires.map identity)), ("services", array (value.services.map identity)),
    ("laws", array (value.laws.map identity))]
private def capabilityUse (value : Raw.CapabilityUse) :=
  object [("type", natural value.type.index), ("statics", statics value.statics)]
private def permission (value : Raw.Permission) :=
  object [("signature", capabilityUse value.signature), ("roles", refs value.roles)]
private def capabilityType (value : Raw.CapabilityType) :=
  object [("identity", natural value.identity.index), ("statics", natural value.statics),
    ("arguments", typeUses value.arguments), ("result", typeUse value.result)]
private def port (value : Raw.Port) :=
  object [("roles", refs value.roles), ("type", typeUse value.type)]
private def ports (values : List Raw.Port) := array (values.map port)
private def operation (value : Raw.Operation) :=
  object [("identity", natural value.identity.index), ("statics", natural value.statics),
    ("capabilities", array (value.capabilities.map capabilityUse)), ("arguments", typeUses value.arguments),
    ("result", typeUse value.result),
    ("purity", string (match value.purity with | .total => "total" | .ordered => "ordered")),
    ("distinct", array (value.distinct.map fun (a, b) => array [natural a, natural b]))]
private def wire (value : Raw.Wire) :=
  object [("identity", natural value.identity.index), ("statics", natural value.statics), ("type", typeUse value.type)]

mutual
  private def region : Nat → Raw.Region → Except String Raw.Attribute
    | 0, _ => throw "math-resource-limit"
    | fuel + 1, .mk captures nodes outputs => return object [("captures", refs captures), ("nodes", array (← nodes.mapM (node fuel))), ("outputs", refs outputs)]
  private def node : Nat → Raw.Node → Except String Raw.Attribute
    | 0, _ => throw "math-resource-limit"
    | fuel + 1, value => do
        match value with
        | .operation op parameters attributes args =>
            return array [string "operation", natural op.index, statics parameters, attributes, refs args]
        | .tuple elements => return array [string "tuple", refs elements]
        | .project value component => return array [string "project", natural value.index, natural component]
        | .map count body => return array [string "map", static count, ← region fuel body]
        | .fold count initial body => return array [string "fold", static count, refs initial, ← region fuel body]
end

private def relation (value : Raw.Relation) : Except String Raw.Attribute := return object [("statics", natural value.statics), ("public", typeUses value.publicInputs),
    ("witness", typeUses value.witnessInputs), ("assumptions", refs value.assumptions), ("body", ← region 65 value.body)]
private def relationBinding (value : Raw.RelationBinding) :=
  object [("relation", natural value.relation.index), ("statics", statics value.statics),
    ("public", refs value.publicInputs), ("witness", refs value.witnessInputs)]

private def terminal : Raw.Terminal → Raw.Attribute
  | .ret values => array [string "return", refs values]
  | .stop site owner reason => array [string "stop", natural site, natural owner.index,
      string (match reason with
        | .reject => "reject" | .abort => "abort" | .exhausted => "exhausted"
        | .incomplete => "incomplete" | .refused => "refused")]

mutual
  private def body : Nat → Raw.Body → Except String Raw.Attribute
    | 0, _ => throw "math-resource-limit"
    | fuel + 1, .mk steps term => return object [("steps", array (← steps.mapM (step fuel))), ("terminal", terminal term)]
  private def step : Nat → Raw.Step → Except String Raw.Attribute
    | 0, _ => throw "math-resource-limit"
    | fuel + 1, value => do
        match value with
        | .pure value => return array [string "pure", ← region 65 value]
        | .local site owner op parameters attrs caps args => return array [string "local", natural site, natural owner.index, natural op.index,
              statics parameters, attrs, refs caps, refs args]
        | .query site owner cap args => return array [string "query", natural site, natural owner.index, natural cap.index, refs args]
        | .guard site owner condition => return array [string "guard", natural site, natural owner.index, natural condition.index]
        | .message site wire parameters sender receiver value => return array [string "message", natural site, natural wire.index, statics parameters,
              natural sender.index, natural receiver.index, natural value.index]
        | .invoke site definition parameters roles caps args => return array [string "invoke", natural site, natural definition.index, statics parameters, refs roles, refs caps, refs args]
        | .repeat site count carried initial captures nested => return array [string "repeat", natural site, static count, ports carried, refs initial, refs captures, ← body fuel nested]
end

private def definition (value : Raw.Definition) : Except String Raw.Attribute := return object [("statics", natural value.statics), ("roles", natural value.roles),
    ("capabilities", array (value.capabilities.map permission)), ("arguments", ports value.arguments),
    ("results", ports value.results), ("relations", array (value.relations.map relationBinding)),
    ("body", ← body 65 value.body)]
private def entry (value : Raw.Entry) :=
  object [("definition", natural value.definition.index), ("statics", array (value.statics.map natural)),
    ("roles", refs value.roles), ("capabilities", refs value.capabilities)]
private def module (value : Raw.Module) : Except String Raw.Attribute := return object [("roles", array (value.roles.map string)), ("types", array (value.types.map typeTemplate)),
    ("operations", array (value.operations.map operation)), ("wires", array (value.wires.map wire)),
    ("capabilityTypes", array (value.capabilityTypes.map capabilityType)), ("roots", array (value.roots.map permission)),
    ("relations", array (← value.relations.mapM relation)), ("definitions", array (← value.definitions.mapM definition)),
    ("entry", entry value.entry)]

def encode (source : Raw.Subject) : Except String Raw.Attribute := do
  let value := object [("profile", string "zkc.math.v1"), ("manifest", manifest source.manifest),
    ("module", ← module source.module)]
  let _ ← Codec.encode value
  return value

end Tools.Mathematical.SchemaEncoding
