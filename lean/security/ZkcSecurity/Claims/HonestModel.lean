module

public import Zkc.Claims.Registry
public import Zkc.Source.Structured.DomainLaws
public import ZkcSecurity.Claims.AuthoredPair
public import ZkcSecurity.Claims.PrimitiveDependencies

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

def honestModelIdentifier : Identifier := ⟨"models.honest", 0⟩

def compiledProducerIdentifier : Identifier := ⟨"producers.compiled", 0⟩

/-- The selector means the subject's admitted producer, not a second artifact
identity. Compiled subjects admit no source-role or author-supplied producer. -/
def honestModelApplication : Wire.Application :=
  ⟨honestModelIdentifier, [(some "producer", .application compiledProducerIdentifier.name
    (some compiledProducerIdentifier.version) [])]⟩

def honestModelSchema (application : Wire.Application) :
    Except ResolutionError HonestExecutionModel :=
  if application.identifier = honestModelIdentifier then
    match application.arguments with
    | [(some "producer", .application "producers.compiled" (some 0) [])] => .ok .privateUniform
    | _ => .error (.schema "compiled honest model requires exactly producer=producers.compiled@0()")
  else .error (.unknownIdentifier application.identifier)

def encodeHonestModel (_model : HonestExecutionModel) : Wire.Application := honestModelApplication

theorem honestModel_roundtrip (model : HonestExecutionModel) :
    honestModelSchema (encodeHonestModel model) = .ok model := by cases model; rfl

theorem honestModel_canonical (application : Wire.Application) (model : HonestExecutionModel)
    (accepted : honestModelSchema application = .ok model) :
    application = encodeHonestModel model := by
  rcases application with ⟨identifier, arguments⟩
  unfold honestModelSchema at accepted
  split at accepted
  · next same =>
    change identifier = honestModelIdentifier at same
    subst identifier
    split at accepted
    · cases model
      simp_all [encodeHonestModel, honestModelApplication, compiledProducerIdentifier]
    · cases accepted
  · cases accepted

abbrev HonestModelRegistry := Registry (Wire.Application → Except ResolutionError HonestExecutionModel)

def honestModelEntry : Export (Wire.Application → Except ResolutionError HonestExecutionModel) :=
  ⟨honestModelIdentifier, "zkc.model.honest/0", some honestModelSchema⟩

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
