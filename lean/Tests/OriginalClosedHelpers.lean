module

public import Zkc.Construction.OriginalHelpers
public import Tests.StructuredOriginFixture

@[expose] public section
/-! An independent admitted-source client of the closed-helper certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Tests.OriginalClosedHelpers
open Zkc.Source Zkc.Source.Structured Zkc.Construction

def entry (model : DomainModel) : HelperDefinition model.Value closedInterface :=
  (Domain.helperTable model StructuredOriginFixture.program)[0]'(by change 0 < 1; omega)

theorem found (model : DomainModel) :
    (Domain.helperTable model StructuredOriginFixture.program).find?
      (fun candidate => candidate.helper.name == (entry model).helper.name) = some (entry model) := by
  kernel_rfl

/-- The closure is the one in the existing admitted fixture, with its entire
ABI checked. Source state and every captured physical slot are unchanged. -/
def certificate (model : DomainModel) (routing : Original.Routing)
    (state : Original.State model.toCarriers) (environment : Domain.Environment model.toCarriers) :
    Original.Simulation (Original.HelperReturns (fun _ => []) state environment)
      (fun _ frame => frame = environment)
      (Original.fold routing (((entry model).invoke .nil).interpret
        (closedLift (I := Occurrence.signature model.toCarriers))) state)
      (Domain.View.helper model StructuredOriginFixture.program "helper" [] [] environment) := by
  exact Original.Simulation.closedHelper model StructuredOriginFixture.program routing
    (entry model) (found model) .nil [] rfl (fun _ => [])
    (fun result => by cases result; rfl) (fun _ => rfl) state environment [] rfl

/-- Changing the declaration cannot turn the same zero-output helper into a
one-output success. No helper-success assumption is supplied to the rule. -/
theorem wrong_output_arity (model : DomainModel) (environment : Domain.Environment model.toCarriers) :
    Domain.View.helper model StructuredOriginFixture.program "helper" [] [.data .index] environment =
      .halt .refused := by
  kernel_rfl

end Tests.OriginalClosedHelpers
