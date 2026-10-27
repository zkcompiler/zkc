module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.SumcheckReduceData
public import ZkcExamples.Structured.SumcheckReduceBodies
public import ZkcExamples.Structured.SumcheckRelationContract

@[expose] public section

/-! Complete checked payload and named kernel admission phases. The four formula
helpers reuse the relation-contract bodies; every other body is named in
`SumcheckReduceBodies`, whose shared helper bodies abbreviate
`SumcheckHelperBodies`. -/
namespace ZkcExamples.Structured.SumcheckReduceViews
open Zkc.Source Zkc.Source.Structured SumcheckReduceBodies

set_option smartUnfolding false

structured_views SumcheckReduceData.snapshot
  helpers [less, rows, shape, table, pending, width, values, «variables»,
    tableShapeFormula, sumAdd, sumStep, sumTotal, pendingFormula, empty, openClaim,
    halves, sums, interpolate, append, atPrefix, interpolateRealization,
    mapCallback, map, first]
  protocols [reduce, run]

end ZkcExamples.Structured.SumcheckReduceViews
