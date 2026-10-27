module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.SumcheckReduceData
public import ZkcExamples.Structured.SumcheckRepackedData
public import ZkcExamples.Structured.SumcheckRepackedBodies
public import ZkcExamples.Structured.SumcheckRelationContract

@[expose] public section

/-! Complete checked payload and named kernel admission phases of the repacked
Reduction export. Every helper and the child Reduce use the retained
Reduction's bodies; only the root is new. Admission is checked against the
repacked snapshot itself. -/
namespace ZkcExamples.Structured.SumcheckRepackedViews
open Zkc.Source Zkc.Source.Structured SumcheckReduceBodies

set_option smartUnfolding false

structured_views SumcheckRepackedData.snapshot
  helpers [less, rows, shape, table, pending, width, values, «variables»,
    tableShapeFormula, sumAdd, sumStep, sumTotal, pendingFormula, empty, openClaim,
    halves, sums, interpolate, append, atPrefix, interpolateRealization,
    mapCallback, map, first]
  protocols [reduce, run := SumcheckRepackedBodies.run]

/-- The two exports differ in source digest, so they are distinct subjects
although their root declaration symbol is the same. -/
theorem distinct_subjects :
    SumcheckRepackedData.snapshot.source ≠ SumcheckReduceData.snapshot.source ∧
    SumcheckRepackedData.snapshot.entry = SumcheckReduceData.snapshot.entry := by
  constructor
  · decide
  · rfl

end ZkcExamples.Structured.SumcheckRepackedViews
