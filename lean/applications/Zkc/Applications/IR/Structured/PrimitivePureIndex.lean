module

public import Zkc.IR.Source.Structured.UnitViews
public import Zkc.Applications.IR.Structured.PrimitivePureIndexData
public import Zkc.Applications.IR.Structured.PrimitivePureIndexBodies
public import Zkc.IR.Source.Structured.OpenMeaning

@[expose] public section

/-! The complete original two-role pure-index consumer. The equality consumes
its actual optional input; a public constant does not create knowledge of it. -/
namespace ZkcExamples.Structured.PrimitivePureIndex
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false

structured_views PrimitivePureIndexData.snapshot
  helpers [] protocols [pureIndex := PrimitivePureIndexBodies.pureIndex]

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The owning participant computes from its real index input. -/
theorem owner_equation (position : Nat) :
    program.participant F G 0 (.cons (some position) .nil) =
      .done (.cons (some (decide (position = 0))) .nil) := rfl

/-- The other participant has no value even though zero itself is public. -/
theorem other_equation :
    program.participant F G 1 (.cons none .nil) =
      .done (.cons none .nil) := rfl

/-- Missing input remains absent in the owning component as well. -/
theorem missing_equation :
    program.participant F G 0 (.cons none .nil) =
      .done (.cons none .nil) := rfl

end ZkcExamples.Structured.PrimitivePureIndex
