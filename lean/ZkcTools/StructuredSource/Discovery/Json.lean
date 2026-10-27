module

public import ZkcTools.StructuredSource.Discovery.Search
public import ZkcTools.StructuredSource.WireTypes

@[expose] public section

namespace ZkcTools.StructuredSource.Discovery
open Lean Zkc.Source Zkc.Source.Structured

def strings (items : List String) : Json := toJson items

def addressJson (address : Address) : Json :=
  let (coordinate, index) := match address.coordinate with
    | .instruction => ("instruction", none)
    | .input i => ("input", some i) | .operand i => ("operand", some i)
    | .result i => ("result", some i)
  Json.mkObj [("snapshot", toJson address.snapshot), ("definition", toJson address.definition),
    ("carrier", toJson "admitted-raw-region"), ("region", toJson address.region),
    ("coordinate", toJson coordinate), ("index", toJson index)]

def valueJson (value : Value) : Json := Json.mkObj [
  ("address", addressJson value.address), ("type", wireType value.type),
  ("scopes", toJson value.scopes), ("dependencies", toJson (value.dependencies.map addressJson)),
  ("unknown_dependencies", toJson value.unknownDependencies)]

def primitiveJson : Primitive → Json
  | .indexConstant n => toJson ["index.constant", toString n]
  | .vectorEmpty d => toJson ["vector.empty", d]
  | .vectorLength d => toJson ["vector.length", d]
  | .vectorSum d => toJson ["vector.sum", d]
  | .vectorSplit d => toJson ["vector.split", d]
  | .vectorAppend d => toJson ["vector.append", d]
  | .vectorEqual d => toJson ["vector.equal", d]
  | .fieldEqual d => toJson ["field.equal", d]
  | .indexEqual => toJson ["index.equal"] | .indexLess => toJson ["index.less"]
  | .indexAdd => toJson ["index.add"] | .indexMul => toJson ["index.mul"]
  | .indexSub => toJson ["index.sub"] | .indexDiv => toJson ["index.div"]
  | .indexMod => toJson ["index.mod"]

def domainNodeJson {inputs : List Ty} {context : List (List Ty)} {items : List Ty} :
    DomainNode inputs context items → Json
  | .elements _ container => toJson [toJson "elements", toJson container.index]
  | .indices _ container => toJson [toJson "indices", toJson container.index, toJson (0 : Nat)]
  | .range lower upper => toJson [toJson "range", toJson lower.index, toJson upper.index]
  | .zip _ operands => toJson [toJson "zip", toJson operands.indices]
  | .product _ operands => toJson [toJson "product", toJson operands.indices]

def domainBodyJson {inputs : List Ty} : {context : List (List Ty)} → {items : List Ty} →
    DomainBody inputs context items → List Json × Nat
  | _, _, .ret value => ([], value.index)
  | _, _, .letNode node next =>
      let (nodes, result) := domainBodyJson next
      (domainNodeJson node :: nodes, result)

def domainJson (domain : DomainSpec) : Json :=
  let (constructors, result) := domainBodyJson domain.body
  Json.mkObj [("name", toJson domain.name), ("inputs", toJson (domain.inputs.map wireType)),
    ("items", toJson (domain.items.map wireType)), ("constructors", toJson constructors),
    ("result", toJson result)]

def opJson (op : Op) : Json := Json.mkObj [
  ("constructor", toJson (match op with
    | .exec _ => "exec" | .indexConstant _ => "indexConstant" | .indexEqual => "indexEqual"
    | .indexLess => "indexLess" | .indexPowerOfTwo => "indexPowerOfTwo"
    | .vectorLength _ => "vectorLength"
    | .fieldConstant .. => "fieldConstant" | .fieldAdd _ => "fieldAdd"
    | .fieldSubtract _ => "fieldSubtract" | .fieldMultiply _ => "fieldMultiply"
    | .fieldEqual _ => "fieldEqual" | .fieldEmbed .. => "fieldEmbed"
    | .groupIdentity _ => "groupIdentity" | .groupAdd _ => "groupAdd"
    | .groupScale .. => "groupScale" | .groupEqual _ => "groupEqual"
    | .booleanConstant _ => "booleanConstant" | .booleanAnd => "booleanAnd"
    | .booleanOr => "booleanOr" | .booleanXor => "booleanXor"
    | .booleanEqual => "booleanEqual" | .booleanNotEqual => "booleanNotEqual"
    | .makeProduct .. => "makeProduct" | .getProduct .. => "getProduct"
    | .select _ => "select" | .boundedAt _ => "boundedAt" | .invoke _ => "invoke"
    | .fold _ => "fold" | .collect _ => "collect" | .map _ => "map" | .branch .. => "branch"
    | .loop .. => "loop" | .loopCondition .. => "loopCondition"
    | .guard => "guard" | .mark _ => "mark")),
  ("arguments", toJson (op.arguments.map wireType)),
  ("results", toJson (op.results.map wireType)),
  ("helpers", toJson (op.helpers.map (·.name))),
  ("parameters", match op with
    | .exec primitive => primitiveJson primitive
    | .indexConstant n | .fieldConstant _ n => toJson [toString n]
    | .booleanConstant b => toJson b
    | .mark site => toJson site
    | .fold spec => Json.mkObj [("domain", domainJson spec.domain),
        ("step", toJson spec.step), ("predicate", toJson spec.predicate),
        ("state", toJson (spec.state.map wireType)), ("captures", toJson (spec.captures.map wireType)),
        ("kind", toJson (if spec.kind == .math then "math" else "local"))]
    | .collect spec => Json.mkObj [("domain", domainJson spec.domain),
        ("body", toJson spec.body), ("predicate", toJson spec.predicate),
        ("collection", wireType spec.collection.type), ("captures", toJson (spec.captures.map wireType)),
        ("kind", toJson (if spec.kind == .math then "math" else "local"))]
    | .map spec => Json.mkObj [("helper", toJson spec.helperName), ("field", toJson spec.field), ("rowwise", toJson spec.rowwise)]
    | _ => .null)]

mutual
  def rawJson (body : RawRegion Ty Op) : Json := match body with
    | .ret indices => toJson [toJson "ret", toJson indices]
    | .stop reason => toJson [toJson "stop", toJson (reprStr reason)]
    | .bind types body next => toJson [toJson "bind", toJson (types.map wireType), rawJson body, rawJson next]
    | .letOp op arguments types bodies next => toJson [toJson "letOp", opJson op,
        toJson arguments, toJson (types.map wireType), bodiesJson bodies, rawJson next]
  def bodiesJson (bodies : RawRegions Ty Op) : Json := match bodies with
    | .nil => toJson ([] : List Json)
    | .cons inputs outputs body tail => Json.arr (#[Json.mkObj [
        ("inputs", toJson (inputs.map wireType)), ("outputs", toJson (outputs.map wireType)),
        ("body", rawJson body)]] ++ (bodiesJson tail).getArr?.toOption.getD #[])
end

def nodeJson (node : Node) : Json := Json.mkObj [
  ("address", addressJson node.address), ("context", toJson (node.context.map addressJson)),
  ("selected_role", toJson node.selectedRole), ("tag", toJson node.tag),
  ("calculation", node.calculation.map opJson |>.getD .null),
  ("helper", toJson node.helper),
  ("operand_selections", toJson (node.operandPositions.map fun index =>
    addressJson { node.address with coordinate := .operand index })), ("arguments", toJson (node.arguments.map valueJson)),
  ("results", toJson (node.results.map valueJson)), ("role_map", toJson node.roleMap),
  ("private_result_positions", toJson node.privateResults)]

def viewJson (view : View) : Json := Json.mkObj [
  ("snapshot", toJson view.snapshot), ("entry", toJson view.entry),
  ("arm", toJson (reprStr view.arm)), ("role", toJson view.role), ("steps", toJson view.steps),
  ("nodes", toJson (view.nodes.map nodeJson)), ("inputs", toJson (view.inputs.map valueJson)),
  ("cuts", toJson (view.cuts.map fun cut => Json.mkObj [
    ("receive", addressJson cut.receive), ("type", wireType cut.type),
    ("sender", toJson cut.sender), ("receiver", toJson cut.receiver),
    ("honest_source", cut.honestSource.map addressJson |>.getD .null)])),
  ("relations", toJson (view.relations.map fun relation => Json.mkObj [
    ("name", toJson relation.name), ("formula", toJson relation.formula)])),
  ("helpers", toJson (view.helperBodies.map fun helper => Json.mkObj [
    ("name", toJson helper.name), ("kind", toJson (if helper.kind == .math then "math" else "local")), ("inputs", toJson (helper.inputs.map wireType)),
    ("outputs", toJson (helper.outputs.map wireType)), ("body", rawJson helper.raw)]))]

def candidateJson (candidate : Candidate) : Json := Json.mkObj [
  ("template", toJson (if candidate.template == .table then "table-total-restriction" else "separate-factor-product")),
  ("occurrence", addressJson candidate.occurrence), ("context", toJson (candidate.context.map addressJson)),
  ("state", toJson (candidate.state.map addressJson)), ("message", toJson (candidate.message.map addressJson)),
  ("updates", toJson (candidate.updates.map addressJson)), ("helpers", strings candidate.helpers),
  ("helper_selections", toJson (candidate.helpers.map fun name => addressJson
    { snapshot := candidate.occurrence.snapshot, definition := name })),
  ("degree", toJson candidate.degree), ("obligations", strings candidate.obligations)]

def outcomeJson (outcome : Outcome) : Json := Json.mkObj [
  ("status", toJson outcome.status), ("candidates", toJson (outcome.candidates.map candidateJson)),
  ("reasons", strings outcome.reasons), ("steps", toJson outcome.steps),
  ("evidence", toJson "none; all candidates untrusted")]

end ZkcTools.StructuredSource.Discovery
