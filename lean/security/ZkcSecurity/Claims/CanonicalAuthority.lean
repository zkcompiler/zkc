module

public import ZkcSecurity.Claims.DomainSoundness
public import ZkcSecurity.Claims.CanonicalAuthorityPair
public import ZkcSecurity.Claims.ReceiptAdmission

@[expose] public section

/-! Closed security authority indexed by supported semantic subject shapes.
The dispatcher contains no protocol identifiers or author-installed callbacks.
All elaborators, meanings, capabilities and links precede proof selection. -/
set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims Zkc.Source.Structured ZkcSecurity.Endpoint

inductive CanonicalAuthority : Type 1 → Type 2 where
  | uniform {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
      [DecidableEq G] [SampleableType F] [Fintype F] [Inhabited F]
      (art : Artifacts) (endpoint : Semantics) : CanonicalAuthority (Subject F G art endpoint)
  | domains {model : DomainModel} (art : Endpoint.Domain.Artifacts)
      (capabilities : Domain.Capabilities model art.original) : CanonicalAuthority (Domain.Subject model art)
  | authoredPair {model : DomainModel} {original : Snapshot} (imported : Imported original)
      (selected : Zkc.Construction.AuthoredPair.Selection original)
      (capabilities : Domain.Capabilities model original) :
      CanonicalAuthority (HonestPair.CanonicalSubject model original imported selected)

namespace CanonicalAuthority

/-- Finite field data already determines an exact uniform sampler. This also
serves author receipts whose proposition does not mention sampling. -/
@[reducible] noncomputable def finiteFieldSampling (F : Type) [Field F] [Fintype F] : SampleableType F :=
  @SampleableType.ofFintype F inferInstance ⟨0⟩

@[reducible] def fieldInhabited (F : Type) [Field F] : Inhabited F := ⟨0⟩

/-- Infer the uniform subject's artifact index before elaborating registries. -/
def ofUniformSubject {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]
    [DecidableEq G] [SampleableType F] [Fintype F] [Inhabited F]
    {art : Artifacts} {endpoint : Semantics} (_subject : Subject F G art endpoint) :
    CanonicalAuthority (Subject F G art endpoint) := .uniform art endpoint

def reference : {S : Type 1} → CanonicalAuthority S → S → SubjectRef
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ _, subject => subject.reference
  | _, .domains _ _, subject => subject.reference
  | _, .authoredPair _ _ _, subject => subject.down.reference

def check : {S : Type 1} → CanonicalAuthority S → S → Wire.Request → Except ResolutionError Unit
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ _, subject => subject.check
  | _, .domains _ _, subject => subject.check
  | _, .authoredPair _ _ _, subject => subject.down.check

abbrev Context : {S : Type 1} → CanonicalAuthority S → Type
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ _ | _, .domains _ _ => ModelContext
  | _, .authoredPair _ _ _ => Unit

abbrev ModelExport : {S : Type 1} → CanonicalAuthority S → Type 1
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ _ => (F : Type) → Fintype F → Snapshot → Semantics →
      Wire.Application → Except ResolutionError (Except Incomplete Model)
  | _, .domains _ _ => Domain.ModelExport
  | _, .authoredPair _ _ _ => HonestPair.ModelExport

abbrev ModelValue : {S : Type 1} → CanonicalAuthority S → Type
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ _ | _, .domains _ _ => Model
  | _, .authoredPair _ _ _ => HonestPair.HonestExecutionModel

def modelEntry : {S : Type 1} → (authority : CanonicalAuthority S) →
    authority.Context → Export authority.ModelExport
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ endpoint, context => (models context endpoint).exports.head (by simp [models])
  | _, .domains _ capabilities, context => Domain.modelEntry capabilities context
  | _, .authoredPair _ _ _, _ => HonestPair.modelEntry

def resolveModel : {S : Type 1} → (authority : CanonicalAuthority S) →
    Registry authority.ModelExport → S → Wire.Application →
    Except ResolutionError (Except Incomplete authority.ModelValue)
  | _, @uniform F _ _ _ _ _ _ _ finite _ art endpoint, registry, _, application =>
      @Claims.resolveModel registry F finite art.original endpoint application
  | _, .domains _ _, registry, _, application => Domain.resolveModel registry application
  | _, .authoredPair _ _ _, registry, _, application =>
      Except.ok <$> HonestPair.resolveModel registry application

def modelMeaning : {S : Type 1} → (authority : CanonicalAuthority S) →
    authority.Context → S → Wire.Application →
    Except ResolutionError (Except Incomplete authority.ModelValue)
  | _, @uniform F _ _ _ _ _ _ _ finite _ art endpoint, context, _, application =>
      @modelSchema F finite art.original context endpoint application
  | _, .domains _ capabilities, context, _, application => Domain.modelSchema capabilities context application
  | _, .authoredPair _ _ _, _, _, application => Except.ok <$> HonestPair.honestModelSchema application

noncomputable def propertyEntry : {S : Type 1} → (authority : CanonicalAuthority S) →
    Registry authority.ModelExport → PropertyKey → Export (PropertyExport S)
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ _, registry, key => canonicalPropertyEntry registry key
  | _, .domains _ capabilities, registry, key => ⟨key.identifier, key.schema, match key with
      | .soundness => some (Domain.soundnessProperty capabilities registry)
      | _ => none⟩
  | _, .authoredPair _ _ capabilities, registry, key => ⟨key.identifier, key.schema, match key with
      | .completeness => some (HonestPair.completenessProperty capabilities registry)
      | _ => none⟩

noncomputable def properties {S : Type 1} (authority : CanonicalAuthority S)
    (registry : Registry authority.ModelExport) : Registry (PropertyExport S) :=
  ⟨PropertyKey.all.map (authority.propertyEntry registry)⟩

def links : {S : Type 1} → CanonicalAuthority S → S → List Obligation
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ _, subject => subject.stageLinks
  | _, .domains _ _, subject => subject.stageLinks
  | _, .authoredPair _ _ _, subject => subject.down.stageLinks

def linkProofs : {S : Type 1} → (authority : CanonicalAuthority S) → (subject : S) →
    (index : Fin (authority.links subject).length) →
    Option (PLift ((authority.links subject).get index).goal)
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ _, subject, index => subject.stageLinkProofs index
  | _, .domains _ _, subject, index => subject.stageLinkProofs index
  | _, .authoredPair _ _ _, subject, index => subject.down.stageLinkProofs index

def kind : {S : Type 1} → CanonicalAuthority S → String
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ _ => "uniform-verifier"
  | _, .domains _ _ => "domain-verifier"
  | _, .authoredPair _ _ _ => "authored-pair"

def product : {S : Type 1} → CanonicalAuthority S → String
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ _ | _, .domains _ _ => "certified_verifier"
  | _, .authoredPair _ _ _ => "compiled_ideal_completeness"

def coveredEndpoint : {S : Type 1} → CanonicalAuthority S → String
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ .idealMeaning | _, .domains _ _ => "ideal-meaning"
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ .executableBytes => "interpreted-executable-bytes"
  | _, .authoredPair _ _ _ => "compiled-ideal-honest-pair"

/-- Physical pipeline keys are exported alongside semantic policy. -/
def artifactRoles : {S : Type 1} → CanonicalAuthority S → List (String × String)
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ .idealMeaning | _, .domains _ _ => [("constructed-participant", "constructed_export")]
  | _, @uniform _ _ _ _ _ _ _ _ _ _ _ .executableBytes => [("constructed-participant", "constructed_export"),
      ("verifier-program", "program")]
  | _, .authoredPair _ _ _ => [("producer", "producer_export"), ("validator", "constructed_export")]

/-- Each fixed adapter owns exactly its stage/source/pair obligations. -/
theorem propertyLinks {S : Type 1} (authority : CanonicalAuthority S)
    (registry : Registry authority.ModelExport) (key : PropertyKey)
    (property : PropertyExport S) (defined : (authority.propertyEntry registry key).definition = some property)
    (subject : S) (arguments : property.Arguments subject) :
    property.requiredLinks subject arguments = authority.links subject := by
  cases authority with
  | uniform art endpoint =>
    cases key <;> simp only [propertyEntry, canonicalPropertyEntry] at defined
    all_goals cases defined
    all_goals rfl
  | domains art capabilities =>
    cases key <;> simp only [propertyEntry] at defined
    all_goals cases defined
    all_goals rfl
  | authoredPair imported selected capabilities =>
    cases key <;> simp only [propertyEntry] at defined
    all_goals cases defined
    all_goals rfl

end CanonicalAuthority
end ZkcSecurity.Claims
