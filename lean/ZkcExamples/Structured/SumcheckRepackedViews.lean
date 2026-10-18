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
  helpers [sumAdd := (SumcheckRelationContract.addHelper, SumcheckRelationContract.addBody),
    sumStep := (SumcheckRelationContract.foldSpec.stepHelper, SumcheckRelationContract.stepBody),
    sumTotal := SumcheckRelationContract.total, tableSumFormula := SumcheckRelationContract.tableSum,
    less, rows, shape, table, values, width, «variables», empty, halves, sums, interpolate, map, first,
    append]
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
