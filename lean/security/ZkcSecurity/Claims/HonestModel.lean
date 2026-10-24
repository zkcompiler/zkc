module

public import Zkc.Claims.Registry
public import Zkc.Source.Structured.DomainLaws
public import ZkcSecurity.Claims.AuthoredPair

@[expose] public section

/-! Fixed honest-execution policy. It has no adversary, query allowance or
evidence-selected handler. Private field draws use the admitted owner-local service ports. Public
queries share one typed-history ROM cache across both participants. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims.HonestPair
open Zkc.Claims Zkc.Source.Structured

inductive HonestExecutionModel where
  | privateUniform
  deriving DecidableEq, Repr

def honestModelIdentifier : Identifier := ⟨"models.honest_fiat_shamir", 1⟩

def honestModelSchema (application : Wire.Application) :
    Except ResolutionError HonestExecutionModel :=
  if application.arguments.isEmpty then .ok .privateUniform
  else .error (.schema "honest private-uniform model accepts no arguments")

abbrev HonestModelRegistry := Registry (Wire.Application → Except ResolutionError HonestExecutionModel)

def honestModelEntry : Export (Wire.Application → Except ResolutionError HonestExecutionModel) :=
  ⟨honestModelIdentifier, "honest-private-uniform/1", some honestModelSchema⟩

def resolveHonestModel (registry : HonestModelRegistry) (application : Wire.Application) :
    Except ResolutionError HonestExecutionModel := do
  let entry ← registry.lookup application.identifier
  let some schema := entry.definition | throw (.schema "undefined honest model")
  schema application

/-- Association is with the complete selected export. A same-name replacement
handler does not implement the canonical honest model. -/
structure HonestModelAdmission (registry : HonestModelRegistry) (application : Wire.Application) : Prop where
  selected : registry.lookup application.identifier = .ok honestModelEntry
  admitted : resolveHonestModel registry application = .ok .privateUniform

/-- Capabilities belong to the actual model and admitted catalogue. These
mathematical laws do not assert producer success or source/native execution. -/
structure LawfulHonestModel (model : DomainModel) (original : Snapshot) : Prop where
  algebra : DomainLaws original.catalogue model
  characteristic : CharacteristicLaws original.catalogue model.toFieldModel

end ZkcSecurity.Claims.HonestPair
