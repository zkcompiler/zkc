module

public import Tests.ReusableAggregateTwoBatchesSource
public meta import ZkcTools.StructuredSource.NamedValues
public meta import ZkcTools.StructuredSource.HelperPresentation
public meta import ZkcTools.Companions

@[expose] public section

/-! Source-derived complete interfaces. This module imports no companion.
Field labels name the retained ABI order; they do not choose a reference. -/
set_option autoImplicit false
noncomputable section
namespace Tests.MathematicalCompanionGoals
open Zkc.Source Zkc.Source.Structured
open Tests.ReusableAggregateTwoBatchesSource

named_values BatchInputs
  [firstPoint, firstValue, firstBatch, secondPoint, secondValue, secondBatch] :=
  program.payload.entry.inputs

named_values BatchOutputs [firstDecision, firstBatch, secondDecision, secondBatch] :=
  program.payload.entry.outputs

named_values OpeningInputs [accepted, point, value, expectedPoint, expectedValue] :=
  Tests.ReusableAggregateTwoBatchesBodies.checkOpeningHelper.inputs

helper_presentation Opening
  inputs [accepted, point, value, expectedPoint, expectedValue] outputs [decision] :=
  Tests.ReusableAggregateTwoBatchesBodies.checkOpeningBody

end Tests.MathematicalCompanionGoals
