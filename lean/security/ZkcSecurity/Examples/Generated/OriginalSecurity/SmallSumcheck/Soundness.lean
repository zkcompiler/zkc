module

public import ZkcSecurity.Families.Sumcheck.TableComponentPrimeField
public import ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Installation
public import ZkcSecurity.Examples.Components.SmallSumcheckFormula

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Realizations.Sumcheck.OriginalRoot
open Zkc.Claims OracleComp OracleSpec
open ZkcSecurity.Claims ZkcSecurity.Obligations ZkcSecurity.Domains.PrimeField
open ZkcSecurity.Examples.Generated.SmallSumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
open ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Installation
abbrev Scalar := ZMod blsModulus
abbrev Group := ZMod blsModulus
abbrev carriers := uniformCarriers Scalar Group
abbrev Statement := validatorArtifacts.Statement model
local instance : DecidableEq (Domain.Event carriers) := Classical.decEq _
local instance : ∀ event : Domain.Event carriers, SampleableType (Domain.Raw event) := rawSampleable blsModulus

def budget : Nat := 2
def price : ENNReal := 1 / (Fintype.card Scalar : ENNReal)

set_option linter.unusedSimpArgs false in
/-- The formula is an explicit mathematical selection. This implication is
checked against the unchanged retained target, separately from the ABI. -/
def rejectedInputs (input0 : List Scalar) (input1 : Scalar) (input2 : Nat)
    (falseStatement : validatorSubject.FalseStatement (statement input0 input1 input2))
    (initial : Domain.History carriers) :
    Zkc.Obligations.Derivation (NominalField.interface (G := Group) "bls12-381.fr")
      (boundedEscape (fun _ _ => price)) (fun _ result => acceptance result ≠ some true) initial
      (presentedInputs input0 input1 input2 initial) := by
  apply composition_rejected
    (PrimeField.conditionalWithFrame blsModulus "bls12-381.fr"
      (TableComponent.Execution.frameUpdate (F := Scalar) (G := Group) "bls12-381.fr"))
    2 (ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.calls input0 input1 input2 0) ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.terminalTree
    (ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.terminal_coverage input0 input1 input2 0) ⟨[], initial⟩ initial
  intro all
  obtain ⟨bounded0, shape0, equal0⟩ := all ⟨⟨input0, input1, input2⟩, ⟨ZkcExamples.Structured.OriginalArtifacts.SmallSumcheck.occurrence0.protocol, 0⟩, ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.schedule0⟩ (by simp only [ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.calls, List.mem_cons]; tauto)
  apply falseStatement
  refine ⟨fun _ _ => none, ?_⟩
  prove_retained_target [Scalar, Group] reading (validator_application_read input0 input1 input2 _)
    evaluating ZkcSecurity.Examples.Components.SmallSumcheck.Formula.equation solving (first | assumption | simp [equal0])

theorem inputCosts (input0 : List Scalar) (input1 : Scalar) (input2 : Nat) (initial : Domain.History carriers) :
    Typed.ChargedCostBound (NominalField.interface (G := Group) "bls12-381.fr") (fun _ _ => price)
      (presentedInputs input0 input1 input2 initial) initial (budget • price) :=
  composition_cost price (fun _ _ => le_rfl) 2 (ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.calls input0 input1 input2 0) ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Sources.terminalTree ⟨[], initial⟩ initial

def rejected (statement : Statement) (falseStatement : validatorSubject.FalseStatement statement)
    (initial : Domain.History carriers) :
    Zkc.Obligations.Derivation installation.absorb (boundedEscape (fun _ _ => price))
      (fun _ result => installation.acceptance result ≠ some true) initial
      (installation.presented statement initial) := by bind_subject_abi using rejectedInputs

theorem costs (statement : Statement) (initial : Domain.History carriers) :
    Typed.ChargedCostBound installation.absorb (fun _ _ => price)
      (installation.presented statement initial) initial (budget • price) := by bind_subject_abi using inputCosts

def capabilities := blsCapabilities original (by decide +kernel)
def priceBound : Claims.Bound := .div (.constant 1) (Fintype.card Scalar : ℚ≥0)
theorem priceBound_value (queries : Nat) : priceBound.value queries = price := by
  simp only [priceBound, Bound.value, ennreal_nnrat_one, ennreal_nnrat_natural, price]
def schedule : Claims.Domain.ChargeSchedule validatorSubject :=
  Claims.CompiledSoundness.uniformSchedule validatorSubject priceBound
    (by decide +kernel) (by decide +kernel)
theorem schedule_prices (queries : Nat) : ∀ entry ∈ schedule.entries, entry.2.value queries = price := by
  intro entry member
  exact (Claims.CompiledSoundness.uniformSchedule_prices priceBound _ _ queries entry member).trans (priceBound_value queries)

def reductionExport (queries : Nat) :
    Claims.Domain.ChargedExport validatorSubject schedule queries (budget • price) :=
  installation.losslessChargedExport (NominalField.lossless "bls12-381.fr") schedule queries (budget • price)
    (by rw [Claims.CompiledSoundness.charge_constant schedule queries price (by decide +kernel) (schedule_prices queries)]; exact rejected)
    (by rw [Claims.CompiledSoundness.charge_constant schedule queries price (by decide +kernel) (schedule_prices queries)]; exact costs)

/-- The installed degree-one method owns its cost and scalar conversion. -/
def validatorCost (_queries : Nat) : ENNReal := budget • price
def scalarBound : Nat → ENNReal := fun queries =>
  ((queries : ENNReal) + budget) / (Fintype.card Scalar : ENNReal)
theorem scalar_bound (queries : Nat) :
    (queries : ENNReal) * schedule.maximum queries + validatorCost queries ≤ scalarBound queries := by
  rw [Claims.CompiledSoundness.maximum_constant schedule queries price (by decide +kernel) (schedule_prices queries)]
  simp only [validatorCost, scalarBound, price, nsmul_eq_mul, div_eq_mul_inv, one_mul, add_mul]
  exact le_rfl

theorem scalar_meaning (selected : Model) (adaptiveForm : selected.form = .adaptive) :
    Claims.Domain.Soundness capabilities validatorSubject selected
      (fun queries => scalarBound queries) :=
  Claims.CompiledSoundness.scalar_meaning (model := model) (art := validatorArtifacts)
    (subject := validatorSubject) capabilities schedule validatorCost scalarBound
    reductionExport scalar_bound selected adaptiveForm

theorem charged_meaning (selected : Model) (adaptiveForm : selected.form = .adaptive)
    (costLaw : ∀ queries, selected.validatorCost.value queries = validatorCost queries) :
    Claims.Domain.SoundnessArguments.meaning capabilities
      (⟨selected, .charged schedule⟩ : Claims.Domain.SoundnessArguments validatorSubject) :=
  Claims.CompiledSoundness.charged_meaning (model := model) (art := validatorArtifacts)
    (subject := validatorSubject) capabilities schedule validatorCost
    reductionExport selected adaptiveForm costLaw

end ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Soundness
