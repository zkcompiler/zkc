module

public import ZkcSecurity.Families.Sumcheck.TableComponentExecution
public import ZkcSecurity.Families.Sumcheck.CompiledValidator
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


open Zkc.Source Zkc.Source.Structured TableComponent

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Adapt the installed loop bridge to its exact generated source-body equation.
The capture size and complete carry/return maps remain checked arguments. -/
theorem sourceLoop (field : String) (program : Structured.Program) (context : Zkc.Construction.Context)
    (plan : CompiledRound.Plan) (sites : Nominal.Schedule field)
    (connection : CompiledValidator.RoundConnection (F := F) (G := G) field program context plan sites)
    (body : Domain.Environment (uniformCarriers F G) → PIR.Process (Domain.effects (uniformCarriers F G))
      (Domain.Environment (uniformCarriers F G)))
    (offset : Nat) (body_eq : body = CompiledRound.block plan program context field offset)
    (captured : Domain.Environment (uniformCarriers F G)) (size : captured.length = offset)
    (indices : List Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :
    FiatShamir.DomainReduction.Bridge (Nominal.interface (G := G) field)
      (CompiledValidator.LoopPost (field := field) (context := context) point.length indices.length)
      history
      (Domain.iterate body captured [offset + 21, offset + 26, offset + 20]
        [.data (.vector field), .data (.field field), .transcript context.suite]
        indices (CompiledValidator.carried field context.suite ⟨point, scalar, history⟩))
      ((CompiledValidator.run field sites indices ⟨point, scalar, history⟩).bind
        (fun final => .done (CompiledValidator.carried field context.suite final))) := by
  rw [body_eq, ← size]
  exact CompiledValidator.loop_bridge connection captured indices ⟨point, scalar, history⟩


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
