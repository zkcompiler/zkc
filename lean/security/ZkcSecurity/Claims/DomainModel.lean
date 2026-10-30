module

public import ZkcSecurity.Bindings.Subjects.Domain
public import ZkcSecurity.Claims.Resolution
public import ZkcSecurity.Bindings.Models.Capabilities

@[expose] public section

/-! Model capabilities are selected before evidence. Finite cardinalities are
required only at admitted field identities. Uniform sampling laws are carried
by SampleableType at the actual event-dependent reply types. -/
set_option autoImplicit false
namespace ZkcSecurity.Claims.Domain
open Zkc.Claims Zkc.Source.Structured Zkc.Construction

def Capabilities.cardinality {model : DomainModel} {snapshot : Snapshot}
    (capabilities : Capabilities model snapshot) (identity : String) : Except Incomplete Nat :=
  if admitted : snapshot.catalogue.identitySort identity = some .field then
    .ok (@Fintype.card (model.Field identity) (capabilities.finite identity admitted))
  else .error ⟨["unsupported or unadmitted finite field: " ++ identity]⟩

structure ModelExport : Type 1 where
  elaborate : Wire.Application → Except ResolutionError (Except Incomplete Model)
abbrev ModelRegistry := Registry ModelExport

def modelSchema {model : DomainModel} {snapshot : Snapshot}
    (capabilities : Capabilities model snapshot) (context : ModelContext) (application : Wire.Application) :
    Except ResolutionError (Except Incomplete Model) := do
  let keys ← premiseKeys application
  if !keys.isEmpty then throw (.schema "dependent verifier has no conditional premise schemas")
  modelSchemaWith capabilities.cardinality context .idealMeaning application

def modelEntry {model : DomainModel} {snapshot : Snapshot}
    (capabilities : Capabilities model snapshot) (context : ModelContext) : Export ModelExport :=
  ⟨exactUniform, "zkc.model.fiat-shamir/0", some ⟨modelSchema capabilities context⟩⟩

def resolveModel (registry : ModelRegistry) (application : Wire.Application) :
    Except ResolutionError (Except Incomplete Model) :=
  match registry.lookup application.identifier with
  | .error error => .error error
  | .ok entry => match entry.definition with
    | none => .ok (.error ⟨["dependent model definition: " ++ application.identifier.name]⟩)
    | some payload => payload.elaborate application

end ZkcSecurity.Claims.Domain
