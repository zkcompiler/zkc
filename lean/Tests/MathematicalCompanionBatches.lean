module

public import Tests.MathematicalCompanionGoals
public import Zkc.Protocols.TableMembership.ReferenceBodies

@[expose] public section

/-! Author mathematics: ordinary library application, named values, no source
positions, typed AST, physical slots or transcript strings. -/
set_option autoImplicit false
noncomputable section
namespace Tests.MathematicalCompanionBatches
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.TableMembership
open Tests.MathematicalCompanionGoals
open Tests.ReusableAggregateTwoBatchesSource (names)

def openingReference (model : DomainModel) (accepted : Bool)
    (point value expectedPoint expectedValue : model.Field "koala-bear") :
    PIR.Outcome (Opening.Output model) :=
  .returned ⟨accepted && decide (point = expectedPoint) && decide (value = expectedValue)⟩

companion_goal OpeningGoal for theorem opening (model : DomainModel) :
  Opening.Goal model (openingReference model) (fun _ _ _ _ _ _ => True)

@[zkc "mathematical-companion/batch-opening"]
theorem opening_companion : OpeningGoal := by
  intro model
  apply Opening.of_law model _ _ (BatchSource.checkOpeningLaw model "koala-bear" names) rfl
  · intro accepted point value expectedPoint expectedValue; rfl
  · intro table accepted point value expectedPoint expectedValue _; trivial

end Tests.MathematicalCompanionBatches
