module

public import ZkcTools.StructuredSource.Evaluation
public import Zkc.Source.Structured.OpenMeaning

@[expose] public section

/-! Wire values for the explicit additive scalar test model. The open tool
replays the uniform participant semantics at `Scalar`, which is the generic one
at the uniform model (`Program.participant_eq_participantOn`). -/

namespace ZkcTools.StructuredSource
open Lean Zkc.Source Zkc.Source.Structured

abbrev OpenValue := assignment Scalar Scalar
abbrev OptionalValues := Values (Component OpenValue)

def wireNatural (json : Json) : Except String Nat := do
  let value ← Format.decimal (← Format.string json)
  if value ≥ indexLimit then throw "structured-input-natural-range"
  return value

mutual
  def wireInput : (type : Ty) → Json → Except String (OpenValue type)
    | .boolean, .bool value => .ok value
    | .boolean, _ => .error "structured-input-type"
    | .index, json | .service _, json => wireNatural json
    | .field _, json | .group _, json => scalar json
    | .vector _, json | .groups _, json => do (← Format.array json 4096).mapM scalar
    | .indices, json => do (← Format.array json 4096).mapM wireNatural
    | .oracle _, _ | .oracleSequence .., _ => throw "structured-oracle-profile"
    | .sequence element, json => do
      if element.isHandle then throw "structured-input-handle"
      (← Format.array json 4096).mapM (wireInput element)
    | .product _ _ fields, json => do
      if fields.hasHandle then throw "structured-input-handle"
      wireProductInput fields (← Format.array json)

  def wireProductInput : (fields : ProductFields) → List Json →
      Except String ((uniformCarriers Scalar Scalar).ProductValue fields)
    | .nil, [] => return ()
    | .cons type rest, value :: values => return (← wireInput type value, ← wireProductInput rest values)
    | _, _ => throw "structured-input-count"
end

/-- Direct service ports retain their checked ownership discipline. Aggregate
handles and logical oracle sorts cannot be supplied even as absent ports. -/
def wireValueAllowed : Ty → Bool
  | .service _ => true
  | type => !type.isHandle

def optionalInputs : (types : List Ty) → List Json → Except String (OptionalValues types)
  | [], [] => .ok .nil
  | type :: types, .null :: values => do
    unless wireValueAllowed type do throw "structured-open-value-type"
    return .cons none (← optionalInputs types values)
  | type :: types, value :: values => do
    unless wireValueAllowed type do throw "structured-open-value-type"
    return .cons (some (← wireInput type value)) (← optionalInputs types values)
  | _, _ => .error "structured-input-count"

mutual
  def wireOutput : (type : Ty) → OpenValue type → Except String Json
    | .boolean, value => return .bool value
    | .index, value | .service _, value => return .str (toString value)
    | .field _, value | .group _, value => return scalarJson value
    | .vector _, values | .groups _, values =>
      return .arr ((show List Scalar from values).map scalarJson).toArray
    | .indices, values => return .arr (values.map (fun value => .str (toString value))).toArray
    | .oracle _, _ | .oracleSequence .., _ => throw "structured-oracle-profile"
    | .sequence element, values => do
      if element.isHandle then throw "structured-input-handle"
      return .arr (← values.mapM (wireOutput element)).toArray
    | .product _ _ fields, value => do
      if fields.hasHandle then throw "structured-input-handle"
      return .arr (← wireProductOutput fields value).toArray

  def wireProductOutput : (fields : ProductFields) →
      (uniformCarriers Scalar Scalar).ProductValue fields → Except String (List Json)
    | .nil, () => return []
    | .cons type rest, (value, values) =>
      return (← wireOutput type value) :: (← wireProductOutput rest values)
end

def optionalOutputs {types : List Ty} : OptionalValues types → Except String (List Json)
  | .nil => return []
  | .cons (ty := type) value rest => do
    unless wireValueAllowed type do throw "structured-open-value-type"
    return (← value.elim (pure .null) (wireOutput type)) :: (← optionalOutputs rest)

/-- Validate supplied service ports before role masking, including unowned ports.
Admission already ensures each service port has one resolved owner. -/
def validateServiceAliases : {types : List Ty} → List (List Nat) → OptionalValues types →
    List (Nat × Nat) → Except String Unit
  | [], _, .nil, _ => .ok ()
  | type :: _, scopes, .cons value rest, seen => do
    let seen ← match type, value with
      | .service _, some handle => do
        let [owner] := scopes.headD [] | throw "structured-service-owner"
        if seen.any (fun entry => entry.1 == handle && entry.2 != owner) then
          throw "structured-service-alias"
        pure ((handle, owner) :: seen)
      | _, _ => pure seen
    validateServiceAliases scopes.tail rest seen

end ZkcTools.StructuredSource
