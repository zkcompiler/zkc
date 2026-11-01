module

public import ZkcSecurity.Bindings.Source.LoopContracts
public import ZkcSecurity.ProgramLogic.RepeatedComponent
public meta import ZkcSecurityTools.SourceProperties.Builder
public meta import ZkcTools.StructuredSource.CountedShape

public meta section

/-! Install separate No and pathwise-cost obligations at an actual counted
Process. The checked recursion equation selects the full callback. Zero,
successor and continuation shape are rechecked by the generic loop theorem;
selected mathematical rules must prove the remaining callback obligation. -/
set_option autoImplicit false
namespace ZkcSecurity.Tools.SourceProperties
open Lean Meta Elab Tactic

private structure LoopShape where
  reference : TSyntax `term
  step : TSyntax `term
  zero : TSyntax `term
  succ : TSyntax `term

private def countedShape (process : Expr) : TacticM LoopShape := do
  let shape ← ZkcTools.StructuredSource.CountedShape.extract process
  return {
    reference := ← Term.exprToSyntax shape.reference
    step := ← Term.exprToSyntax shape.step
    zero := ← Term.exprToSyntax shape.zero
    succ := ← Term.exprToSyntax shape.succ }

private def loopShape (cost : Bool) : TacticM LoopShape := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  let args := target.getAppArgs
  let index ← if cost && target.isAppOf ``ZkcSecurity.FiatShamir.Typed.ChargedCostBound then
      pure (args.size - 3)
    else if !cost && target.isAppOf ``Zkc.Obligations.Derivation then pure (args.size - 1)
    else throwError "expected a source rejection or charged-cost loop obligation"
  countedShape args[index]!

private def callback (rules : Array (TSyntax `term)) : TacticM Unit := do
  for rule in rules do
    let saved ← saveState
    try
      evalTactic (← `(tactic| apply $rule:term))
      evalTactic (← `(tactic| all_goals (first | assumption | rfl | omega)))
      unless (← getGoals).isEmpty do throwError "open callback premise"
      return
    catch error =>
      if error.isRuntime then throw error
      if let .internal _ _ := error then throw error
      saved.restore
  throwError "open counted source callback at the actual typed process: {← getMainTarget}"

elab "source_loop_callback " "[" rules:term,* "]" : tactic => callback rules.getElems

/-- Install the existing history-dependent cost contract without replacing it
by a uniform per-iteration envelope. The frame is an independent all-replies
law; the remaining initial-frame premise stays visible to the companion. The
component body and complete repeated process must match the fixed goal. -/
syntax "install_source_loop_cost " "using_component " term
  " using_frame " term " using_steps " term : tactic
elab_rules : tactic
  | `(tactic| install_source_loop_cost using_component $component
      using_frame $frame using_steps $steps) => do
    evalTactic (← `(tactic| apply ZkcSecurity.Obligations.RepeatedComponent.cost_repeatN
      (component := $component) (preserves := $frame) (steps := $steps)))

/-- No carries the actual history, current index and remaining-state invariant.
Selected callback rules are consumed by the existing property assembler.
Unsupported mathematics remains a typed callback goal. -/
syntax "install_source_loop_no " "using_invariant " term " using_rules " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| install_source_loop_no using_invariant $invariant using_rules [$rules:term,*]) => do
    let shape ← loopShape false
    let pending := (← getGoals).tail
    setGoals [(← getMainGoal)]
    evalTactic (← `(tactic| apply ZkcSecurity.Source.LoopContracts.counted_no
      (reference := $(shape.reference)) (step := $(shape.step)) (invariant := $invariant)
      (zero := $(shape.zero)) (succ := $(shape.succ))))
    let obligations ← getGoals
    let mut remaining : List MVarId := []
    for goal in obligations do
      setGoals [goal]
      evalTactic (← `(tactic| first
        | assumption
        | (intros; first
            | (solve | source_loop_callback [$rules,*])
            | (solve | assemble_source_no [$rules,*] simplifying [])
            | (apply ZkcSecurity.Source.OccurrenceProperties.within; intro reached;
                first | (solve | source_loop_callback [$rules,*])
                      | assemble_source_no [$rules,*] simplifying [])
            | skip)))
      remaining := remaining ++ (← getGoals)
    setGoals (remaining ++ pending)

/-- Cost has no No or honest premise. The uniform per-iteration price must hold
for every typed callback reply, full state and reached history. -/
syntax "install_source_loop_cost " "per_iteration " term " using_rules " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| install_source_loop_cost per_iteration $price using_rules [$rules:term,*]) => do
    let shape ← loopShape true
    let pending := (← getGoals).tail
    setGoals [(← getMainGoal)]
    let target := (← getMainTarget).consumeMData
    let process := target.getAppArgs[target.getAppNumArgs - 3]!
    let count ← Term.exprToSyntax process.getAppArgs[process.getAppNumArgs - 2]!
    evalTactic (← `(tactic| apply ZkcSecurity.FiatShamir.CostComposition.mono
      (small := ($count : ENNReal) * $price) (large := _) ?_ ?_))
    let obligations ← getGoals
    let some bounded := obligations[0]? | throwError "missing counted cost obligation"
    setGoals [bounded]
    evalTactic (← `(tactic| apply ZkcSecurity.Source.LoopContracts.counted_cost
      (reference := $(shape.reference)) (step := $(shape.step)) (price := $price)
      (zero := $(shape.zero)) (succ := $(shape.succ))))
    evalTactic (← `(tactic| intros; first
      | (solve | source_loop_callback [$rules,*])
      | (solve | assemble_source_cost [$rules,*] simplifying [])
      | (apply ZkcSecurity.Source.OccurrenceProperties.within_cost; intro reached;
          first | (solve | source_loop_callback [$rules,*])
                | assemble_source_cost [$rules,*] simplifying [])
      | skip))
    let mut remaining ← getGoals
    for goal in obligations.tail do
      unless ← goal.isAssigned do
        setGoals [goal]
        evalTactic (← `(tactic| try (solve | first | exact le_rfl |
          (simp only [mul_zero, zero_mul]; exact le_rfl))))
        remaining := remaining ++ (← getGoals)
    setGoals (remaining ++ pending)

/-- Select both complete counted bodies from their checked equations. Pairing
requires the honest callback and terminal invariant, independently of unary
return, No and budget properties. The shared theorem checks the two counters,
full continuations and full returned states. -/
syntax "install_source_loop_pair " "using_invariant " term " using_rules " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| install_source_loop_pair using_invariant $invariant using_rules [$rules:term,*]) => withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``ZkcSecurity.Source.Pair do
      throwError "expected a paired source loop obligation"
    let args := target.getAppArgs
    let left ← countedShape args[args.size - 2]!
    let right ← countedShape args.back!
    let pending := (← getGoals).tail
    setGoals [(← getMainGoal)]
    evalTactic (← `(tactic| apply ZkcSecurity.Source.LoopContracts.counted_pair
      (left := $(left.reference)) (right := $(right.reference))
      (stepLeft := $(left.step)) (stepRight := $(right.step))
      (zeroLeft := $(left.zero)) (zeroRight := $(right.zero))
      (succLeft := $(left.succ)) (succRight := $(right.succ))
      (invariant := $invariant)))
    let obligations ← getGoals
    let mut remaining : List MVarId := []
    for goal in obligations do
      setGoals [goal]
      evalTactic (← `(tactic| first
        | assumption
        | (solve | rfl)
        | (solve | intros; first | assumption | source_loop_callback [$rules,*])
        | (solve | intros; apply ZkcSecurity.Source.Pair.within; source_loop_callback [$rules,*])
        | intros))
      remaining := remaining ++ (← getGoals)
    setGoals (remaining ++ pending)

end ZkcSecurity.Tools.SourceProperties
