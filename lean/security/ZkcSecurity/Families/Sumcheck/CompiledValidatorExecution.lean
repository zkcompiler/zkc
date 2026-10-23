module

public import ZkcSecurity.Families.Sumcheck.TableComponentExecution
public import ZkcSecurity.FiatShamir.DomainReduction
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Unary structural execution reuses the installed component normalizer.
The actual generated view supplies its spine and reached immutable frame;
only source mathematical equations are supplied by clients. -/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.CompiledValidator.Execution
open Zkc.Construction
open TableComponent.Execution

macro "normalize_table_validator " "[" laws:term,* "]"
    " unfolding " "[" definitions:term,* "]" : tactic =>
  `(tactic| normalize_component_process
    [FiatShamir.DomainReduction.ReadingTo.checkpoint,
      FiatShamir.DomainReduction.CoherentTo.checkpoint,
      FiatShamir.DomainReduction.Bridge.checkpoint]
    [$laws,*] unfolding [$definitions,*])

meta section
open Lean Meta Elab Tactic

/-- Name the actual captured SSA environment at a reached validator loop. -/
elab "validator_capture " name:ident : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let args := target.getAppArgs
  let process ← if target.isAppOf ``FiatShamir.DomainReduction.ReadingTo ||
        target.isAppOf ``FiatShamir.DomainReduction.Bridge then
      pure args[args.size - 2]!
    else if target.isAppOf ``FiatShamir.DomainReduction.CoherentTo then
      pure args.back!
    else throwError "validator_capture expects an actual Domain bridge, reading or coherence goal"
  let some value := TableComponent.Execution.firstCapture process
    | throwError "validator has not reached an actual iterate application"
  let goal ← getMainGoal
  let goal ← goal.define name.getId (← inferType value) value
  let (_, goal) ← goal.intro1P
  replaceMainGoal [goal]
end
end ZkcSecurity.Families.Sumcheck.CompiledValidator.Execution
