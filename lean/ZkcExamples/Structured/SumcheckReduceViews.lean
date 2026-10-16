module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.SumcheckReduceData
public import ZkcExamples.Structured.SumcheckReduceBodies
public import ZkcExamples.Structured.SumcheckRelationContract

@[expose] public section

/-! Complete checked payload and named kernel admission phases. The four formula
helpers reuse the relation-contract bodies; every other body is authored in
`SumcheckReduceBodies`. -/
namespace ZkcExamples.Structured.SumcheckReduceViews
open Zkc.Source Zkc.Source.Structured SumcheckReduceBodies

set_option smartUnfolding false

structured_views SumcheckReduceData.snapshot
  helpers [sumAdd := (SumcheckRelationContract.addHelper, SumcheckRelationContract.addBody),
    sumStep := (SumcheckRelationContract.foldSpec.stepHelper, SumcheckRelationContract.stepBody),
    sumTotal := SumcheckRelationContract.total, tableSumFormula := SumcheckRelationContract.tableSum,
    less, rows, shape, table, values, width, «variables», empty, halves, sums, interpolate, map, first,
    append]
  protocols [reduce, run]

end ZkcExamples.Structured.SumcheckReduceViews
