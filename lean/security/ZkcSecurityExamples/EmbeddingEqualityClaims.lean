module

public import ZkcSecurityExamples.EmbeddingEqualitySoundness
public import ZkcSecurityExamples.EmbeddingEqualityCapabilities
public import ZkcSecurityTools.ClaimConstruction
public import ZkcSecurity.Bindings.Subjects.ABI

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
  relations := .ofChecked .empty (by decide +kernel)
  meaning := .formula ZkcExamples.Construction.EmbeddingEqualityBinding.formula
  originalExport := "sha256:4b55a9463b0e4e2a42451a5a44e0f88db1f647a810f2c6ec2229d15cbb604e4e"
  participantExport := "sha256:794c90d4922179daaad83fe2db3161ef1cfd70f79ce7fdb0febc86414b0c441f"

theorem target_read (a b : Base) (witness : subject.Witness) :
    subject.target.application.read {} (subject.boundary (statement a b))
      (subject.assignments (statement a b) witness) = some (.cons a (.cons b .nil)) := by
  rfl

/-- The canonical retained relation reads exactly the two public base scalars.
Witness choices do not introduce a hidden equality assumption. -/
theorem holds_iff (a b : Base) (witness : subject.Witness) :
    subject.Holds (statement a b) witness ↔ a = b := by
  exact (subject.holds_iff_of_read _ witness _ (target_read a b witness)).trans (target_iff a b)

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
