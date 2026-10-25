module

public import ZkcSecurity.Examples.EmbeddingEqualitySoundness
public import ZkcSecurity.Examples.EmbeddingEqualityCapabilities
public import ZkcSecurity.Tools.ClaimConstruction

@[expose] public section

/-! The closed canonical domain authority selects the model and property before
the endpoint theorem is applied. Physical hashes identify the actual exports;
the imported source, construction and occurrence checks supply typed binding. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ZkcSecurity.Examples.EmbeddingEqualityClaims
open Zkc Zkc.Claims Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Claims ZkcSecurity.Examples.EmbeddingEquality
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcExamples.Construction.EmbeddingEqualityBinding (retained)
open ZkcSecurity.Examples.EmbeddingEqualityCapabilities (capabilities)

def subject : Claims.Domain.Subject model artifacts where
  compiled := checked
  target := retained
  originalExport := "sha256:198a275c8dc1a3b5e7ef78b30676d63ff0f07b151b292a0a486269b8bb0c15ea"
  participantExport := "sha256:51686b3d9ce3db7cf5e84aa1657cc0204fcbe9bd5c9666931b98423612bdc71b"

theorem target_read (a b : Base) (witness : subject.Witness) :
    subject.target.application.read {} (subject.boundary (statement a b))
      (subject.assignments (statement a b) witness) = some (.cons a (.cons b .nil)) := by
  rfl

/-- The canonical retained relation reads exactly the two public base scalars.
Witness choices do not introduce a hidden equality assumption. -/
theorem holds_iff (a b : Base) (witness : subject.Witness) :
    subject.Holds (statement a b) witness ↔ a = b := by
  constructor
  · rintro ⟨arguments, read, holds⟩
    rw [target_read] at read
    cases Option.some.inj read
    exact (target_iff a b).mp holds
  · intro equal
    exact ⟨.cons a (.cons b .nil), target_read a b witness, (target_iff a b).mpr equal⟩

def selectedModel : Claims.Model :=
  ⟨.fixed, .symbolic "Q", "Q", "", .constant 0, none⟩

/-- No mathematical-model capability, correspondence equation or adversary
restriction is supplied by the author as a theorem premise. -/
theorem soundness : Claims.Domain.Soundness capabilities subject selectedModel
    (Claims.Bound.constant 0).value := by
  classical
  intro input falseStatement initial prover queries _ _
  obtain ⟨a, b, rfl⟩ := statement_shape input
  have different : a ≠ b := by
    intro equal
    apply falseStatement
    exact ⟨fun _ _ => none, (holds_iff a b _).mpr equal⟩
  have zero := compiled_ideal_soundness a b different initial prover
  unfold ZkcSecurity.Examples.EmbeddingEquality.verifier at zero
  simpa only [subject, Bound.value, ennreal_nnrat_zero] using zero.le

def authority := CanonicalAuthority.domains artifacts capabilities
def modelContext : ModelContext := .empty
def models : Registry authority.ModelExport := ⟨[authority.modelEntry modelContext]⟩
noncomputable def properties := authority.properties models

def library : ZkcSecurity.Tools.ClaimConstruction.Library where
  subject := ``subject
  authority := some ``authority
  context := some ``modelContext
  properties := ``properties
  models := ``models
  normalization := [``subject, ``authority, ``modelContext, ``properties, ``models, ``selectedModel]
  methods := [(⟨"fs.keyed_soundness", 0⟩, ``soundness)]

end ZkcSecurity.Examples.EmbeddingEqualityClaims
