module

public import ZkcSecurity.Claims.CanonicalAuthority

@[expose] public section

/-! Complete selected-entry association shared by all closed authority shapes.
Unrelated registry entries remain legal. Core receipts retain their generic type. -/
set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims Zkc.Source.Structured ZkcSecurity.Endpoint

/-- Lookup relates the complete selected entry to the requested identifier. -/
theorem selectedIdentifier {α : Type 1} {registry : Registry α} {identifier : Identifier}
    {entry : Export α} (registered : registry.lookup identifier = .ok entry) :
    entry.identifier = identifier := by
  have member : entry ∈ registry.exports.filter (fun value => value.identifier == identifier) := by
    cases filtered : registry.exports.filter (fun value => value.identifier == identifier) with
    | nil => simp [Registry.lookup, filtered] at registered
    | cons head tail =>
      cases tail with
      | nil =>
        have same : head = entry := by simpa [Registry.lookup, filtered] using registered
        subst entry
        simp
      | cons next rest => simp [Registry.lookup, filtered] at registered
  exact eq_of_beq (List.mem_filter.mp member).2

structure CanonicalModelAdmission {S : Type 1} (authority : CanonicalAuthority S)
    (registry : Registry authority.ModelExport) (context : authority.Context)
    (subject : S) (application : Wire.Application) : Prop where
  selected : registry.lookup application.identifier = .ok (authority.modelEntry context)
  admitted : ∃ actual, authority.resolveModel registry subject application = .ok (.ok actual)

/-- Selected entry association determines the full canonical elaboration. -/
theorem CanonicalModelAdmission.canonical_resolution {S : Type 1} {authority : CanonicalAuthority S}
    {registry : Registry authority.ModelExport} {context : authority.Context}
    {subject : S} {application : Wire.Application}
    (admission : CanonicalModelAdmission authority registry context subject application) :
    authority.resolveModel registry subject application = authority.modelMeaning context subject application := by
  cases authority with
  | uniform art endpoint =>
    simp only [CanonicalAuthority.resolveModel, Claims.resolveModel]
    rw [admission.selected]
    simp [CanonicalAuthority.modelEntry, models, CanonicalAuthority.modelMeaning]
  | domains art capabilities =>
    simp only [CanonicalAuthority.resolveModel, Domain.resolveModel]
    rw [admission.selected]
    rfl
  | authoredPair imported selected capabilities =>
    simp only [CanonicalAuthority.resolveModel, HonestPair.resolveModel]
    rw [admission.selected]
    rfl

section
variable {S : Type 1} {authority : CanonicalAuthority S}
  {propertyRegistry : Registry (PropertyExport S)} {reference : S → SubjectRef}
  {subject : S} {request : Wire.Request}
  {resolved : Resolved propertyRegistry reference subject request}

structure CanonicalAdmission (authority : CanonicalAuthority S)
    (registry : Registry authority.ModelExport) (key : PropertyKey)
    (resolved : Resolved propertyRegistry reference subject request) : Prop where
  checked : authority.check subject request = .ok ()
  selected : resolved.entry = authority.propertyEntry registry key

theorem CanonicalAdmission.propertyKey {registry : Registry authority.ModelExport} {key : PropertyKey}
    (admission : CanonicalAdmission authority registry key resolved) : request.property = key.identifier := by
  have same := selectedIdentifier resolved.registered
  rw [admission.selected] at same
  have identifier : (authority.propertyEntry registry key).identifier = key.identifier := by
    cases authority <;> rfl
  exact same.symm.trans identifier

theorem CanonicalAdmission.meaning {registry : Registry authority.ModelExport} {key : PropertyKey}
    (admission : CanonicalAdmission authority registry key resolved) (meaning : Evaluated resolved) :
    ∃ property, (authority.propertyEntry registry key).definition = some property ∧
      ∃ arguments, property.elaborate request subject = .ok arguments ∧
        property.meaning subject arguments = .ok meaning.proposition ∧
        property.requiredLinks subject arguments = resolved.requiredLinks :=
  ⟨resolved.property, (congrArg Export.definition admission.selected).symm.trans resolved.defined,
    resolved.arguments, resolved.elaborated, meaning.evaluated, rfl⟩

theorem CanonicalAdmission.requiredLinks {registry : Registry authority.ModelExport} {key : PropertyKey}
    (admission : CanonicalAdmission authority registry key resolved) :
    resolved.requiredLinks = authority.links subject :=
  authority.propertyLinks registry key resolved.property
    ((congrArg Export.definition admission.selected).symm.trans resolved.defined) subject resolved.arguments

structure AuthorExtensionAdmission (authority : CanonicalAuthority S)
    (resolved : Resolved propertyRegistry reference subject request) : Prop where
  checked : authority.check subject request = .ok ()
  unreserved : reservedIdentifier request.property = false

structure CanonicalReceipt (authority : CanonicalAuthority S)
    (registry : Registry authority.ModelExport) (context : authority.Context)
    (key : PropertyKey) (meaning : Evaluated resolved) where
  receipt : Receipt meaning
  modelAdmission : CanonicalModelAdmission authority registry context subject request.model
  association : CanonicalAdmission authority registry key resolved

structure AuthorExtensionReceipt (authority : CanonicalAuthority S)
    (registry : Registry authority.ModelExport) (context : authority.Context)
    (meaning : Evaluated resolved) where
  receipt : Receipt meaning
  modelAdmission : CanonicalModelAdmission authority registry context subject request.model
  association : AuthorExtensionAdmission authority resolved

end

section Uniform
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] [Fintype F] [Inhabited F] {art : Artifacts} {endpoint : Semantics}
  {propertyRegistry : Registry (PropertyExport (Subject F G art endpoint))}
  {reference : Subject F G art endpoint → SubjectRef}
  {subject : Subject F G art endpoint} {request : Wire.Request}
  {resolved : Resolved propertyRegistry reference subject request}

def subjectSnapshot (_subject : Subject F G art endpoint) : Snapshot := art.original

def canonicalModelEntry (context : ModelContext) (endpoint : Semantics) :=
  (models context endpoint).exports.head (by simp [models])

/-- The old admitted view is available only for the uniform adapter. -/
def CanonicalReceipt.toAdmittedReceipt {registry : ModelRegistry} {context : ModelContext}
    {key : PropertyKey} {meaning : Evaluated resolved}
    (value : CanonicalReceipt (.uniform (F := F) (G := G) art endpoint) registry context key meaning) :
    AdmittedReceipt registry meaning :=
  ⟨value.receipt, value.association.checked, value.modelAdmission.admitted⟩

def AuthorExtensionReceipt.toAdmittedReceipt {registry : ModelRegistry} {context : ModelContext}
    {meaning : Evaluated resolved}
    (value : AuthorExtensionReceipt (.uniform (F := F) (G := G) art endpoint) registry context meaning) :
    AdmittedReceipt registry meaning :=
  ⟨value.receipt, value.association.checked, value.modelAdmission.admitted⟩
end Uniform
end ZkcSecurity.Claims
