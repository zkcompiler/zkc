module

public import ZkcExamples.Structured.PrimitivePureIndexData
public import Zkc.Source.Structured.OpenMeaning

@[expose] public section

/-! The complete original two-role pure-index consumer. The equality consumes
its actual optional input; a public constant does not create knowledge of it. -/
namespace ZkcExamples.Structured.PrimitivePureIndex
open Zkc.Source Zkc.Source.Structured
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option smartUnfolding false

def program : Program := (check PrimitivePureIndexData.snapshot).toOption.get (by decide +kernel)
def imported : Imported PrimitivePureIndexData.snapshot := ⟨program, rfl⟩

theorem exact_subject : imported.program.snapshot = PrimitivePureIndexData.snapshot :=
  imported.exactSubject

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
