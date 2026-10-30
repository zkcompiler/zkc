module

public import TestsSecurity.RootComposition.FourEndpoints
public import ZkcSecurityExamples.Sumcheck.SourcePublicPrimeField
public import ZkcSecurity.Bindings.Source.RootPublic
public import ZkcSecurity.Claims.Methods.RootConnectionLossless
public import ZkcSecurity.Claims.CompiledSoundness

@[expose] public section

/-! Fixed FourSums soundness from the same generated validator root used
by honest-pair completeness. All nominal statements, adversarial replies,
incoming histories and the existing adaptive model remain in scope.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.RootComposition.Four.Endpoints.Soundness
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Source ZkcSecurity.Families.Sumcheck
open ZkcSecurity ZkcSecurity.Claims ZkcSecurity.Obligations ZkcSecurity.Domains.PrimeField
open TestsSecurity.RootComposition.Four.Endpoints
open ZkcSecurity.Examples.Generated.FourSums
open ZkcSecurity.Examples.Generated.Components.FourSumsABI
open ZkcExamples.Structured.Generated.Connections.FourSums

abbrev Statement := validatorArtifacts.Statement model
local instance : Fact (IsField (model.Field SumcheckReferenceInstallation.field)) := ⟨Field.toIsField Scalar⟩
local instance sourceField : Field (model.Field SumcheckReferenceInstallation.field) :=
  SourceFamilyPublic.fieldStructure model
def claimCapabilities := blsCapabilities original (by decide +kernel)
local instance : ∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event) := claimCapabilities.samples

def price : ENNReal := 1 / (Fintype.card Scalar : ENNReal)
def budget : Nat := 16

def installation := RootConnection.claimsInstallation validatorSubject validatorRouting rfl validator _ rfl noLocal

theorem supported : PublicSourceSupport.check program = true := by decide +kernel

/-- Evaluate only the generated ABI; the checked body certificate stays opaque. -/
theorem source_inputs (a b c d : List Scalar) (sa sb sc sd : Scalar) (count : Nat) (initial : Domain.History model.toCarriers) :
    validator.inputs.abi.read (Domain.inputFrame validatorRouting.context
      ((Domain.encodeValues (statement a b c d sa sb sc sd count)).getD []) initial) program.payload.entry.inputs =
      some (NormalizedRoot.inputs model (Source.arguments model a b c d sa sb sc sd count serviceHandle)) := by kernel_rfl

attribute [local irreducible] validator Occurrence.participant RootConnection.publicPresentation

theorem false_inputs (a b c d : List Scalar) (sa sb sc sd : Scalar) (count : Nat)
    (falseStatement : validatorSubject.FalseStatement (statement a b c d sa sb sc sd count)) :
    ¬ (count ≤ Source.installation.maximum ∧ a.length = 2^count ∧ b.length = 2^count ∧
      c.length = 2^count ∧ d.length = 2^count ∧ sa = a.sum ∧ sb = b.sum ∧ sc = c.sum ∧ sd = d.sum) := by
  rintro ⟨bounded, shapeA, shapeB, shapeC, shapeD, ha, hb, hc, hd⟩
  have small : count < 64 := lt_of_le_of_lt bounded Source.installation.maximum_small
  have finiteA : a.length < indexLimit := by rw [shapeA]; exact ReferenceLibrary.Multilinear.Admission.power_bound count small
  have finiteB : b.length < indexLimit := by rw [shapeB]; exact ReferenceLibrary.Multilinear.Admission.power_bound count small
  have finiteC : c.length < indexLimit := by rw [shapeC]; exact ReferenceLibrary.Multilinear.Admission.power_bound count small
  have finiteD : d.length < indexLimit := by rw [shapeD]; exact ReferenceLibrary.Multilinear.Admission.power_bound count small
  apply falseStatement
  refine ⟨fun _ _ => none, ?_⟩
  apply (Claims.Domain.Subject.holds_iff_of_read _ _ _ _
    (validator_application_read a b c d sa sb sc sd count _)).mpr
  rw [RelationMeaning.formula_exact _ TestsSecurity.RootComposition.Four.Formula.formula]
  rw [TestsSecurity.RootComposition.Four.Formula.equation a b c d sa sb sc sd finiteA finiteB finiteC finiteD]
  simp [ha, hb, hc, hd]

/-- The existing uniform field law, fixed once before root installation. -/
theorem sampling (origin : Origin) (request : origin.request = some (.draw SumcheckReferenceInstallation.field))
    (p q : Polynomial (model.Field SumcheckReferenceInstallation.field)) (different : p ≠ q)
    (left : p.natDegree ≤ 1) (right : q.natDegree ≤ 1) :
    letI : SampleableType (Domain.Raw (carriers := model.toCarriers) (.challenge origin)) :=
      claimCapabilities.samples (.challenge origin)
    Pr{let raw ← $ᵗ (Domain.Raw (carriers := model.toCarriers) (.challenge origin))}[
      p.eval (Original.fieldReply (carriers := model.toCarriers) origin SumcheckReferenceInstallation.field request raw) =
        q.eval (Original.fieldReply (carriers := model.toCarriers) origin SumcheckReferenceInstallation.field request raw)] ≤ price :=
  SourcePublicPrimeField.polynomial_agreement blsModulus
    (algebra := SourceFamilyPublic.fieldStructure model) SumcheckReferenceInstallation.field
    origin request p q different left right

def sourceRejected (a b c d : List Scalar) (sa sb sc sd : Scalar) (count : Nat)
    (wrong : ¬ (count ≤ Source.installation.maximum ∧ a.length = 2^count ∧ b.length = 2^count ∧
      c.length = 2^count ∧ d.length = 2^count ∧ sa = a.sum ∧ sb = b.sum ∧ sc = c.sum ∧ sd = d.sum)) :=
  Source.rejected model price sampling a b c d sa sb sc sd count serviceHandle wrong []

def rejectedInputs (a b c d : List Scalar) (sa sb sc sd : Scalar) (count : Nat)
    (falseStatement : validatorSubject.FalseStatement (statement a b c d sa sb sc sd count))
    (initial : Domain.History model.toCarriers) :
    Zkc.Obligations.Derivation installation.absorb (boundedEscape (fun _ _ => price))
      (fun _ result => installation.acceptance result ≠ some true) initial
      (installation.presented (statement a b c d sa sb sc sd count) initial) := by
  have wrong := false_inputs a b c d sa sb sc sd count falseStatement
  have source := sourceRejected a b c d sa sb sc sd count wrong
  exact Installation.rejected validator rfl model
    (NormalizedRoot.inputs model (Source.arguments model a b c d sa sb sc sd count serviceHandle)) price
    ((Domain.encodeValues (statement a b c d sa sb sc sd count)).getD []) initial _ rfl
    (source_inputs a b c d sa sb sc sd count initial)
    validatorCompiled.selection.output _ (by decide +kernel) [] source

theorem inputCosts (a b c d : List Scalar) (sa sb sc sd : Scalar) (count : Nat)
    (initial : Domain.History model.toCarriers) :
    Typed.ChargedCostBound installation.absorb (fun _ _ => price)
      (installation.presented (statement a b c d sa sb sc sd count) initial) initial (budget • price) := by
  have source := Source.costs model price a b c d sa sb sc sd count serviceHandle []
  exact RootPublic.cost_inputFrame validator rfl model
    (NormalizedRoot.inputs model (Source.arguments model a b c d sa sb sc sd count serviceHandle)) price
    ((Domain.encodeValues (statement a b c d sa sb sc sd count)).getD []) initial _ rfl
    (source_inputs a b c d sa sb sc sd count initial) [] _ source

def rejected (statement : Statement) (falseStatement : validatorSubject.FalseStatement statement)
    (initial : Domain.History model.toCarriers) :
    Zkc.Obligations.Derivation installation.absorb (boundedEscape (fun _ _ => price))
      (fun _ result => installation.acceptance result ≠ some true) initial
      (installation.presented statement initial) := by bind_subject_abi using rejectedInputs

theorem costs (statement : Statement) (initial : Domain.History model.toCarriers) :
    Typed.ChargedCostBound installation.absorb (fun _ _ => price)
      (installation.presented statement initial) initial (budget • price) := by bind_subject_abi using inputCosts

def priceBound : Claims.Bound := .div (.constant 1) (Fintype.card Scalar : ℚ≥0)
theorem priceBound_value (queries : Nat) : priceBound.value queries = price := by
  simp only [priceBound, Bound.value, ennreal_nnrat_one, ennreal_nnrat_natural, price]
def schedule : Claims.Domain.ChargeSchedule validatorSubject :=
  Claims.CompiledSoundness.uniformSchedule validatorSubject priceBound (by decide +kernel) (by decide +kernel)
theorem schedule_prices (queries : Nat) : ∀ entry ∈ schedule.entries, entry.2.value queries = price := by
  intro entry member
  exact (Claims.CompiledSoundness.uniformSchedule_prices priceBound _ _ queries entry member).trans (priceBound_value queries)

def reductionExport (queries : Nat) : Claims.Domain.ChargedExport validatorSubject schedule queries (budget • price) :=
  RootConnection.losslessChargedExport validatorSubject validatorRouting rfl validator supported _ rfl noLocal
    schedule queries (budget • price)
    (by rw [Claims.CompiledSoundness.charge_constant schedule queries price (by decide +kernel) (schedule_prices queries)]; exact rejected)
    (by rw [Claims.CompiledSoundness.charge_constant schedule queries price (by decide +kernel) (schedule_prices queries)]; exact costs)

def validatorCost (_queries : Nat) : ENNReal := budget • price
def scalarBound : Nat → ENNReal := fun queries => ((queries : ENNReal) + budget) / (Fintype.card Scalar : ENNReal)
theorem scalar_bound (queries : Nat) :
    (queries : ENNReal) * schedule.maximum queries + validatorCost queries ≤ scalarBound queries := by
  rw [Claims.CompiledSoundness.maximum_constant schedule queries price (by decide +kernel) (schedule_prices queries)]
  simp only [validatorCost, scalarBound, price, nsmul_eq_mul, div_eq_mul_inv, one_mul, add_mul]
  exact le_rfl

theorem scalar_meaning (selected : Model) (adaptiveForm : selected.form = .adaptive) :
    Claims.Domain.Soundness claimCapabilities validatorSubject selected
      (fun queries => scalarBound queries) :=
  Claims.CompiledSoundness.scalar_meaning (model := model) (art := validatorArtifacts)
    (subject := validatorSubject) claimCapabilities schedule validatorCost scalarBound
    reductionExport scalar_bound selected adaptiveForm

theorem charged_meaning (selected : Model) (adaptiveForm : selected.form = .adaptive)
    (costLaw : ∀ queries, selected.validatorCost.value queries = validatorCost queries) :
    Claims.Domain.SoundnessArguments.meaning claimCapabilities
      (⟨selected, .charged schedule⟩ : Claims.Domain.SoundnessArguments validatorSubject) :=
  Claims.CompiledSoundness.charged_meaning (model := model) (art := validatorArtifacts)
    (subject := validatorSubject) claimCapabilities schedule validatorCost reductionExport selected adaptiveForm costLaw

#print axioms rejectedInputs
#print axioms costs
#print axioms scalar_meaning
#print axioms charged_meaning
end TestsSecurity.RootComposition.Four.Endpoints.Soundness
