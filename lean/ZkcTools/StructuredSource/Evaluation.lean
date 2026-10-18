module

public import ZkcTools.StructuredSource.Bounds
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
