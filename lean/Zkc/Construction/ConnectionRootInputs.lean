module

public import Zkc.Construction.ConnectionRootCertificate

@[expose] public section

/-! Finite proposals for a root's source input locations and symbolic frame.
These functions confer no authority: the input-shape, nominal-sort, visibility
and cell certificates independently check their output. Service capabilities
are explicit source-input associations, never guessed from a field value.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionRootInputs
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction ConnectionFrame

/-- Source input coordinates give distinct internal capability labels. These
labels are used only by the source interpretation: native service ports and
transcript identities remain determined by the checked source/export binding.
No author chooses numeric handles for an ordinary generated root. -/
def serviceCapabilities (inputs : List Ty) : List (Nat × Nat) :=
  inputs.zipIdx.filterMap fun (ty, input) =>
    match ty with
    | .service _ => some (input, input)
    | _ => none

def inputLocations (role : Nat) (capabilities : List (Nat × Nat)) :
    List Ty → List (List Nat) → Nat → Nat → Except String (List Original.Location)
  | [], [], _, _ => .ok []
  | ty :: types, scope :: scopes, input, physical => do
    if !scope.contains role then
      return .absent :: (← inputLocations role capabilities types scopes (input + 1) physical)
    else match ty with
      | .service _ =>
        let some handle := capabilities.lookup input | throw "connection-missing-service-capability"
        return .capability handle :: (← inputLocations role capabilities types scopes (input + 1) physical)
      | _ =>
        if ty.isHandle then throw "connection-input-not-data"
        return .data physical :: (← inputLocations role capabilities types scopes (input + 1) (physical + 1))
  | _, _, _, _ => .error "connection-input-scope-arity"

def locations (signature : ProtocolSignature) (role : Nat) (capabilities : List (Nat × Nat)) :
    Except String (List Original.Location) := do
  unless (capabilities.map Prod.fst).Nodup do throw "connection-duplicate-service-capability"
  inputLocations role capabilities signature.inputs signature.inputScopes 0 0

def dataCells {scope : Scope} : {types : List Ty} →
    Values (Comp [] scope) types → List Original.Location → List (Nat × Cell scope)
  | [], .nil, _ => []
  | _ :: _, .cons value values, .data reference :: locations =>
      (reference, .data value) :: dataCells values locations
  | _ :: _, .cons _ values, _ :: locations => dataCells values locations
  | _ :: _, .cons _ _, [] => []

def layout {types : List Ty} (pattern : InputPattern types) (locations : List Original.Location)
    (suite : String) (history : Option Nat) (sorts : List ValueSort) : Layout pattern.scope :=
  let data := dataCells pattern.initial locations
  (List.range sorts.length).map fun reference =>
    if history == some reference then .history suite else (data.lookup reference).getD .unused

end Zkc.Construction.ConnectionRootInputs
