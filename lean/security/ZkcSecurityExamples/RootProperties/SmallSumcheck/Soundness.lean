module

public import ZkcSecurityExamples.RootProperties.SmallSumcheck
public import ZkcSecurity.Bindings.Sumcheck.SourcePublicPrimeField
public import ZkcSecurityExamples.Sumcheck.SourcePublicInstallations
public import ZkcSecurity.Bindings.Source.RootPublic
public import ZkcSecurity.Claims.Methods.RootConnectionLossless
public import ZkcSecurity.Claims.CompiledSoundness

@[expose] public section

/-! Fixed SmallSumcheck soundness from the same generated validator root used
by honest-pair completeness. All nominal statements, adversarial replies,
incoming histories and the existing adaptive model remain in scope.
-/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.RootProperties.SmallSumcheck.Soundness
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Source ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Claims ZkcSecurity.Obligations ZkcSecurity.Domains.PrimeField
open ZkcSecurity.Examples.Generated.SmallSumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
open ZkcExamples.Structured.Generated.Connections.SmallSumcheck

abbrev Statement := validatorArtifacts.Statement model
local instance : Fact (IsField (model.Field SumcheckReferenceInstallation.field)) := ⟨Field.toIsField Scalar⟩
def claimCapabilities := blsCapabilities original (by decide +kernel)
local instance : ∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event) := claimCapabilities.samples

def price : ENNReal := 1 / (Fintype.card Scalar : ENNReal)
def budget : Nat := 2

def installation := RootConnection.claimsInstallation validatorSubject validatorRouting rfl validator _ rfl noLocal

theorem supported : PublicSourceSupport.check program = true := by decide +kernel

/-- Evaluate only the generated ABI; the checked body certificate stays opaque. -/
theorem source_inputs (original : List Scalar) (scalar : Scalar) (count : Nat) (initial : Domain.History model.toCarriers) :
    validator.inputs.abi.read (Domain.inputFrame validatorRouting.context
      ((Domain.encodeValues (statement original scalar count)).getD []) initial) program.payload.entry.inputs =
      some (SourceRootReference.rootInputs model .small (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some serviceHandle) .nil))))) := by kernel_rfl

attribute [local irreducible] validator Occurrence.participant RootConnection.publicPresentation

theorem false_inputs (original : List Scalar) (scalar : Scalar) (count : Nat)
    (falseStatement : validatorSubject.FalseStatement (statement original scalar count)) :
    ¬ (count ≤ SumcheckSourceSelections.maximum .small ∧ original.length = 2^count ∧ scalar = original.sum) := by
  intro valid
  have finite : original.length < indexLimit := by
    rw [valid.2.1]
    exact ReferenceLibrary.Multilinear.Admission.power_bound count (lt_of_le_of_lt valid.1 (by decide +kernel))
  apply falseStatement
  refine ⟨fun _ _ => none, ?_⟩
  prove_retained_target [Scalar, Scalar] reading (validator_application_read original scalar count _)
    evaluating ZkcSecurity.Examples.Components.SmallSumcheck.Formula.equation
    solving (first | exact finite | simp [valid.2.2])

def rejectedInputs (original : List Scalar) (scalar : Scalar) (count : Nat)
    (falseStatement : validatorSubject.FalseStatement (statement original scalar count))
    (initial : Domain.History model.toCarriers) :
    Zkc.Obligations.Derivation installation.absorb (boundedEscape (fun _ _ => price))
      (fun _ result => installation.acceptance result ≠ some true) initial
      (installation.presented (statement original scalar count) initial) := by
  have wrong := false_inputs original scalar count falseStatement
  have source := SourcePublicInstallations.small_no model price
    (SourcePublicPrimeField.polynomial_agreement blsModulus
      (algebra := SourcePublicInstallations.fieldStructure model)
      SumcheckReferenceInstallation.field)
    original scalar count serviceHandle wrong []
  exact Installation.rejected validator rfl model
    (SourceRootReference.rootInputs model .small (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some serviceHandle) .nil))))) price
    ((Domain.encodeValues (statement original scalar count)).getD []) initial _ rfl
    (source_inputs original scalar count initial)
    validatorCompiled.selection.output _ (by decide +kernel) [] source

theorem inputCosts (original : List Scalar) (scalar : Scalar) (count : Nat)
    (initial : Domain.History model.toCarriers) :
    Typed.ChargedCostBound installation.absorb (fun _ _ => price)
      (installation.presented (statement original scalar count) initial) initial (budget • price) := by
  have source := SourcePublicInstallations.small_cost model price original scalar count serviceHandle []
  exact RootPublic.cost_inputFrame validator rfl model
    (SourceRootReference.rootInputs model .small (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some serviceHandle) .nil))))) price
    ((Domain.encodeValues (statement original scalar count)).getD []) initial _ rfl
    (source_inputs original scalar count initial) [] _ source

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
end ZkcSecurity.Examples.RootProperties.SmallSumcheck.Soundness
