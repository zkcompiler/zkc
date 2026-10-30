module

public import ZkcSecurity.Realizations.Sumcheck.SourceFamily
public import ZkcExamples.Structured.SumcheckSourceSelections

@[expose] public section

/-! Existing clients select checked family installations. This adapter owns the
two retained program selections; the family itself has no source enumeration. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceProducerReduction
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
variable (model : DomainModel)
theorem actual_bodies (selection : SumcheckSourceSelections.Selection) :
    Bodies model (SumcheckSourceSelections.source selection).payload.definitions :=
  ⟨(SumcheckReductionReference.actual_bodies model selection).width,
    (SumcheckReductionReference.actual_bodies model selection).dimension,
    (SumcheckSourceSelections.roundBodies selection).less,
    (SumcheckSourceSelections.wrappers model selection).empty⟩

end ZkcSecurity.Realizations.Sumcheck.SourceProducerReduction

namespace ZkcSecurity.Realizations.Sumcheck.SourceFamilySelections
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured SumcheckSourceSelections

def small : SourceFamily.Installation (source .small) where
  maximum := maximum .small
  maximum_small := by decide +kernel
  reductionName := Generated.Bindings.SmallSumcheckInputs.protocol0Signature.name
  reduction := by derive_source_association
  roundBodies := roundBodies .small
  admissionBodies := admissionBodies .small
  validatorBodies := fun model => SumcheckReductionReference.actual_bodies model .small
  producerBodies := fun model => SourceProducerReduction.actual_bodies model .small
  initial := fun model => (wrappers model .small).initial

def twoSums : SourceFamily.Installation (source .twoSums) where
  maximum := maximum .twoSums
  maximum_small := by decide +kernel
  reductionName := Generated.Bindings.TwoSumsInputs.protocol0Signature.name
  reduction := by derive_source_association
  roundBodies := roundBodies .twoSums
  admissionBodies := admissionBodies .twoSums
  validatorBodies := fun model => SumcheckReductionReference.actual_bodies model .twoSums
  producerBodies := fun model => SourceProducerReduction.actual_bodies model .twoSums
  initial := fun model => (wrappers model .twoSums).initial

/-- Compatibility is a selector of checked installation data. All component
and root correctness arguments are independent of this selector. -/
def installed (selection : Selection) : SourceFamily.Installation (source selection) where
  maximum := maximum selection
  maximum_small := match selection with
    | .small => small.maximum_small
    | .twoSums => twoSums.maximum_small
  reductionName := match selection with
    | .small => small.reductionName
    | .twoSums => twoSums.reductionName
  reduction := match selection with
    | .small => small.reduction
    | .twoSums => twoSums.reduction
  roundBodies := roundBodies selection
  admissionBodies := admissionBodies selection
  validatorBodies := fun model => SumcheckReductionReference.actual_bodies model selection
  producerBodies := fun model => SourceProducerReduction.actual_bodies model selection
  initial := fun model => (wrappers model selection).initial

end ZkcSecurity.Realizations.Sumcheck.SourceFamilySelections
