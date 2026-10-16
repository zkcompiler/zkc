module

public import ZkcTools.StructuredSource.Evaluation
public import Zkc.Source.Structured.OpenMeaning

@[expose] public section

/-! Wire values for the explicit additive scalar test model. The logical
participant semantics remains parameterized independently by F and G. -/

namespace ZkcTools.StructuredSource
open Lean Zkc.Source Zkc.Source.Structured

abbrev OpenValue := assignment Scalar Scalar
abbrev OptionalValues := Values (Component OpenValue)

def wireType : Ty → Json
  | .boolean => .arr #[.str "bool"]
  | .index => .arr #[.str "index"]
  | .field domain => .arr #[.str "field", .str domain]
  | .vector domain => .arr #[.str "vector", .str domain]
  | .group domain => .arr #[.str "group", .str domain]
  | .service contract => .arr #[.str "service", .str contract]

def wireNatural (json : Json) : Except String Nat := do
  let value ← Format.decimal (← Format.string json)
  if value ≥ indexLimit then throw "structured-input-natural-range"
  return value

def wireInput : (type : Ty) → Json → Except String (OpenValue type)
  | .boolean, .bool value => .ok value
  | .boolean, _ => .error "structured-input-type"
  | .index, json | .service _, json => wireNatural json
  | .field _, json | .group _, json => scalar json
  | .vector _, json => do (← Format.array json 4096).mapM scalar

def optionalInputs : (types : List Ty) → List Json → Except String (OptionalValues types)
  | [], [] => .ok .nil
  | _ :: types, .null :: values => return .cons none (← optionalInputs types values)
  | type :: types, value :: values =>
    return .cons (some (← wireInput type value)) (← optionalInputs types values)
  | _, _ => .error "structured-input-count"

def wireOutput : (type : Ty) → OpenValue type → Json
  | .boolean, value => .bool value
  | .index, value | .service _, value => .str (toString value)
  | .field _, value | .group _, value => .str (toString value.val)
  | .vector _, values => .arr (values.map (fun value => .str (toString value.val))).toArray

def optionalOutputs {types : List Ty} : OptionalValues types → List Json
  | .nil => []
  | .cons (ty := type) value rest =>
    value.elim .null (wireOutput type) :: optionalOutputs rest

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

def valueBounds : (type : Ty) → OpenValue type → InputBounds → InputBounds
  | .index, value, bounds => { bounds with index := max bounds.index value }
  | .vector _, value, bounds => { bounds with vectorLength := max bounds.vectorLength value.length }
  | _, _, bounds => bounds

def optionalInputBounds {types : List Ty} : OptionalValues types → InputBounds
  | .nil => {}
  | .cons (ty := type) value rest =>
    let bounds := optionalInputBounds rest
    value.elim bounds (fun value => valueBounds type value bounds)

end ZkcTools.StructuredSource
