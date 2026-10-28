module

public import ZkcTools.StructuredSource.Bounds
public import ZkcTools.StructuredSource.WireTypes
public import Zkc.Source.Structured.DomainTransfer
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-! Bounded executable specialization. The logical semantics is fuel-free;
this CLI conservatively refuses work whose structural upper bound is too large. -/

namespace ZkcTools.StructuredSource
open Lean Zkc.Source Zkc.Source.Structured

abbrev Scalar := ZMod scalarModulus

/-- The executable domain model: every field identity and every group identity
read in `Scalar`, with its computable inverse. -/
abbrev scalarModel : DomainModel :=
  (ringModel Scalar Scalar).withInverse fun _ => some (·⁻¹)

def scalar (json : Json) : Except String Scalar := do
  let value ← Format.decimal (← Format.string json)
  if value ≥ scalarModulus then throw "structured-input-field-canonical"
  return (value : Scalar)

mutual
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
    | .groups domain, json => do
      let [.str "groups", .str actual, values] ← Format.array json | throw "structured-input-type"
      if actual != domain then throw "structured-input-domain"
      (← Format.array values 4096).mapM scalar
    | .indices, json => do
      let [.str "indices", values] ← Format.array json | throw "structured-input-type"
      (← Format.array values 4096).mapM fun value => Structured.Format.natural value (indexLimit - 1)
    | .oracle _, _ | .oracleSequence .., _ => throw "structured-oracle-profile"
    | .service _, _ => throw "structured-open-profile"
    | .sequence element, json => do
      let [.str "sequence", elementType, values] ← Format.array json | throw "structured-input-type"
      if (← Structured.Format.type elementType) != element then throw "structured-input-domain"
      (← Format.array values 4096).mapM (input element)
    | .product identity constructor fields, json => do
      let [.str "product", .str actual, .str alternative, values] ← Format.array json
        | throw "structured-input-type"
      if actual != identity || alternative != constructor then throw "structured-input-domain"
      inputProduct fields (← Format.array values)

  def inputProduct : (fields : ProductFields) → List Json →
      Except String ((uniformCarriers Scalar Scalar).ProductValue fields)
    | .nil, [] => return ()
    | .cons type rest, value :: values => return (← input type value, ← inputProduct rest values)
    | _, _ => throw "structured-input-count"
end

def inputs : (types : List Ty) → List Json → Except String (Values (assignment Scalar Scalar) types)
  | [], [] => return .nil
  | type :: types, value :: values => return .cons (← input type value) (← inputs types values)
  | _, _ => throw "structured-input-count"

def scalarJson (value : Scalar) : Json := .str (toString value.val)

mutual
  def output : (type : Ty) → assignment Scalar Scalar type → Except String Json
    | .boolean, value => .ok (.arr #[.str "bool", .bool value])
    | .index, value => .ok (.arr #[.str "index", toJson value])
    | .field domain, value => .ok (.arr #[.str "field", .str domain, scalarJson value])
    | .vector domain, values =>
        .ok (.arr #[.str "vector", .str domain,
          .arr ((show List Scalar from values).map scalarJson).toArray])
    | .group domain, value => .ok (.arr #[.str "group", .str domain, scalarJson value])
    | .groups domain, values => .ok (.arr #[.str "groups", .str domain,
        .arr ((show List Scalar from values).map scalarJson).toArray])
    | .indices, values => .ok (.arr #[.str "indices", .arr (values.map toJson).toArray])
    | .oracle _, _ | .oracleSequence .., _ => .error "structured-oracle-profile"
    | .service _, _ => .error "structured-open-profile"
    | .sequence element, values => do
        return .arr #[.str "sequence", wireType element, .arr (← values.mapM (output element)).toArray]
    | .product identity constructor fields, value => do
        return .arr #[.str "product", .str identity, .str constructor,
          .arr (← outputProduct fields value).toArray]

  def outputProduct : (fields : ProductFields) →
      (uniformCarriers Scalar Scalar).ProductValue fields → Except String (List Json)
    | .nil, () => return []
    | .cons type rest, (value, values) =>
      return (← output type value) :: (← outputProduct rest values)
end

def outputs {types : List Ty} : Values (assignment Scalar Scalar) types → Except String (List Json)
  | .nil => .ok []
  | .cons (ty := type) value rest => return (← output type value) :: (← outputs rest)

def outcome {types : List Ty} : PIR.Outcome (Values (assignment Scalar Scalar) types) → Except String Json
  | .returned values => return .arr #[.str "returned", .arr (← outputs values).toArray]
  | .stopped reason => .ok (.arr #[.str "stopped", Zkc.Source.Format.stop.encode reason])

/-- Capacity analysis specializes each SSA input and checked helper call. The
result is a tool policy check, not a theorem about the logical interpreter. -/
def preflight (payload : Payload) {types : List Ty}
    (values : Values (assignment Scalar Scalar) types) : Except String Unit := do
  let _ ← (Bounds.closed payload (Bounds.values values)).mapError (Bounds.Failure.code false)
  return ()

def evaluate (program : Program) (json : Json) : Except String Json := do
  let payload ← program.closedPayload
  let values ← inputs payload.entry.inputs (← Format.array json)
  preflight payload values
  outcome (closedOutcome (payload.denoteOn scalarModel values))

end ZkcTools.StructuredSource
