module

public import Zkc.Source.Structured.ClosedProfile
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Bounded executable specialization. The logical semantics is fuel-free;
this CLI conservatively refuses work whose structural upper bound is too large. -/

namespace ZkcTools.StructuredSource
open Lean Zkc.Source Zkc.Source.Structured

abbrev Scalar := ZMod scalarModulus

def scalar (json : Json) : Except String Scalar := do
  let value ← Format.decimal (← Format.string json)
  if value ≥ scalarModulus then throw "structured-input-field-canonical"
  return (value : Scalar)

def input : (type : Ty) → Json → Except String (assignment Scalar Scalar type)
  | .boolean, json => do
    let [.str "bool", .bool value] ← Format.array json | throw "structured-input-type"
    return value
  | .index, json => do
    let [.str "index", value] ← Format.array json | throw "structured-input-type"
    Structured.Format.natural value (indexLimit - 1)
  | .field domain, json => do
    let [.str "field", .str actual, value] ← Format.array json | throw "structured-input-type"
    if actual != domain then throw "structured-input-domain"
    scalar value
  | .vector domain, json => do
    let [.str "vector", .str actual, values] ← Format.array json | throw "structured-input-type"
    if actual != domain then throw "structured-input-domain"
    (← Format.array values 4096).mapM scalar
  | .group domain, json => do
    let [.str "group", .str actual, value] ← Format.array json | throw "structured-input-type"
    if actual != domain then throw "structured-input-domain"
    scalar value
  | .service _, _ => throw "structured-open-profile"

def inputs : (types : List Ty) → List Json → Except String (Values (assignment Scalar Scalar) types)
  | [], [] => return .nil
  | type :: types, value :: values => return .cons (← input type value) (← inputs types values)
  | _, _ => throw "structured-input-count"

def output : (type : Ty) → assignment Scalar Scalar type → Except String Json
  | .boolean, value => .ok (.arr #[.str "bool", .bool value])
  | .index, value => .ok (.arr #[.str "index", toJson value])
  | .field domain, value => .ok (.arr #[.str "field", .str domain, .str (toString value.val)])
  | .vector domain, values =>
      .ok (.arr #[.str "vector", .str domain,
        .arr (values.map (fun value => .str (toString value.val))).toArray])
  | .group domain, value => .ok (.arr #[.str "group", .str domain, .str (toString value.val)])
  | .service _, _ => .error "structured-open-profile"

def outputs {types : List Ty} : Values (assignment Scalar Scalar) types → Except String (List Json)
  | .nil => .ok []
  | .cons (ty := type) value rest => return (← output type value) :: (← outputs rest)

def outcome {types : List Ty} : PIR.Outcome (Values (assignment Scalar Scalar) types) → Except String Json
  | .returned values => return .arr #[.str "returned", .arr (← outputs values).toArray]
  | .stopped reason => .ok (.arr #[.str "stopped", Zkc.Source.Format.stop.encode reason])

structure InputBounds where
  vectorLength : Nat := 0
  index : Nat := 0

def inputBounds {types : List Ty} : Values (assignment Scalar Scalar) types → InputBounds
  | .nil => {}
  | .cons (ty := type) value rest =>
    let tail := inputBounds rest
    match type with
    | .index => { tail with index := max tail.index value }
    | .vector _ => { tail with vectorLength := max tail.vectorLength value.length }
    | _ => tail

def workLimit : Nat := 1000000
def capped (value : Nat) : Nat := min (workLimit + 1) value
abbrev Costs := List (String × Nat)

def helperCost (costs : Costs) (name : String) : Nat :=
  match costs.find? (·.1 == name) with
  | some (_, cost) => cost
  | none => workLimit + 1

def operationCost (bounds : InputBounds) (costs : Costs) (op : Op) (bodies : List Nat) : Nat :=
  match op with
  | .invoke helper => helperCost costs helper.name
  | .fold spec => capped (1 + bounds.vectorLength *
      (helperCost costs spec.step + if spec.predicate.isEmpty then 1 else helperCost costs spec.predicate))
  | .branch .. => 1 + bodies.foldl max 0
  | .loop .. | .loopCondition .. =>
      let upper := max bounds.index bounds.vectorLength
      if upper > 2 ^ 20 then workLimit + 1
      else capped (1 + upper * (1 + bodies.foldl max 0))
  | _ => 1

mutual
  def regionCost (bounds : InputBounds) (costs : Costs) : RawRegion Ty Op → Nat
    | .ret _ | .stop _ => 1
    | .letOp op _ _ bodies next =>
        capped (1 + operationCost bounds costs op (regionsCost bounds costs bodies) + regionCost bounds costs next)
    | .bind _ body next => capped (1 + regionCost bounds costs body + regionCost bounds costs next)
  def regionsCost (bounds : InputBounds) (costs : Costs) : RawRegions Ty Op → List Nat
    | .nil => []
    | .cons _ _ body rest => regionCost bounds costs body :: regionsCost bounds costs rest
end

/-- All supported operations preserve existing vector values; there are no
vector constructors. Domain-generated indices are below the input vector bound.
This conservative estimate includes untaken arms and skipped predicates. -/
def evaluationCost (payload : Payload) (bounds : InputBounds) : Nat :=
  let costs := payload.definitions.foldl (fun costs definition =>
    (definition.name, regionCost bounds costs definition.raw) :: costs) []
  regionCost bounds costs payload.entry.raw

def evaluate (program : Program) (json : Json) : Except String Json := do
  let payload ← program.closedPayload
  let values ← inputs payload.entry.inputs (← Format.array json)
  if evaluationCost payload (inputBounds values) > workLimit then
    throw "structured-evaluation-work-limit"
  outcome (closedOutcome (payload.denote Scalar Scalar values))

end ZkcTools.StructuredSource
