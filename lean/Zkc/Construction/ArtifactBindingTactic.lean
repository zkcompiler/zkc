module

public import Zkc.Construction.ArtifactBinding
public meta import Lean.Elab.Tactic
public meta import Zkc.Construction.TransportReduction

@[expose] public meta section

/-! Structural proof search for a fixed original/compiled process pair.
Normalization and all side conditions are supplied as scoped tactics. There
is no protocol registry, instruction-count recognizer, or trusted evaluator. -/
set_option autoImplicit false
namespace Zkc.Construction.ArtifactBinding
open Lean Meta Elab Tactic

partial def startsCheckpoint (expression : Expr) : Bool :=
  if expression.isAppOf ``PIR.Process.call then
    expression.getAppArgs[expression.getAppArgs.size - 2]!.isAppOf ``Domain.Effect.checkpoint
  else if expression.isAppOf ``PIR.Process.bind then
    startsCheckpoint expression.getAppArgs[expression.getAppArgs.size - 2]!
  else false

partial def derive (goal : MVarId) (rules : Array (TSyntax `term))
    (normalize side : TSyntax `tactic) : TacticM Unit :=
  goal.withContext <| Term.withoutErrToSorry <| withoutRecover do
    setGoals [goal]
    evalTactic (← `(tactic| intros))
    let [reached] ← getGoals | throwError "expected one reached simulation"
    let reachedType ← instantiateMVars (← reached.getType)
    if reachedType.isAppOf ``Original.Simulation then
      let actual := reachedType.getAppArgs.back!
      if startsCheckpoint actual then
          let obligations ← reached.apply (← mkConstWithFreshMVarLevels ``Original.Simulation.checkpoint)
          for obligation in obligations do
            let simulation ← obligation.withContext do
              pure ((← obligation.getType).isAppOf ``Original.Simulation)
            if simulation then derive obligation rules normalize side
            else
              setGoals [obligation]
              evalTactic side
              unless (← getGoals).isEmpty do
                throwError "reached checkpoint obligation remains: {MessageData.ofGoal (← getMainGoal)}"
          return
    evalTactic (← `(tactic| try simp_all only [ite_true, ite_false,
      Bool.false_eq_true, Bool.true_eq_false]))
    evalTactic normalize
    if (← getGoals).isEmpty then return
    let [current] ← getGoals | throwError "normalizer must leave one simulation goal"
    current.withContext do
      let target ← instantiateMVars (← current.getType)
      unless target.isAppOf ``Original.Simulation do
        throwError "expected a structural simulation: {target}"
      let saved ← saveState
      let mut applied : Option (List MVarId) := none
      for rule in rules do
        saved.restore
        try
          let proof ← Term.elabTerm rule none
          let obligations ← current.apply proof
          applied := some obligations
          break
        catch _ => pure ()
      for rule in [``Original.Simulation.done, ``Original.Simulation.halt,
          ``Original.Simulation.checkpoint, ``Original.Simulation.call] do
        if applied.isSome then break
        saved.restore
        try
          let obligations ← current.apply (← mkConstWithFreshMVarLevels rule)
          applied := some obligations
          break
        catch _ => pure ()
      if let some obligations := applied then
        for obligation in obligations do
          let simulation ← obligation.withContext do
            forallTelescope (← obligation.getType) fun _ body =>
              pure (body.isAppOf ``Original.Simulation)
          if simulation then derive obligation rules normalize side
          else
            setGoals [obligation]
            evalTactic side
            unless (← getGoals).isEmpty do
              throwError "local frame or return obligation remains: {MessageData.ofGoal (← getMainGoal)}"
        return
      saved.restore
      let args := target.getAppArgs
      let source := args[args.size - 2]!
      let actual := args.back!
      let condition := if source.isAppOf ``ite then some source.getAppArgs[1]!
        else if actual.isAppOf ``ite then some actual.getAppArgs[1]! else none
      if let some condition := condition then
        let condition ← Term.exprToSyntax condition
        evalTactic (← `(tactic| by_cases artifactCondition : $condition))
        for branch in ← getGoals do derive branch rules normalize side
        return
      throwError "no structural rule applies; inspect the exact operation, stop, or local condition: {MessageData.ofGoal current}"

elab "derive_artifact_binding" " normalizing " normalize:tactic " solving " side:tactic : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let pending := (← getGoals).tail
    derive goal #[] normalize side
    setGoals pending

elab "derive_artifact_binding " "[" rules:term,* "]"
    " normalizing " normalize:tactic " solving " side:tactic : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let pending := (← getGoals).tail
    derive goal rules.getElems normalize side
    setGoals pending

/-- Reduce a reached operation using public equations. Helper bodies and loop
bodies remain opaque unless the caller explicitly supplies their equations.
The macro neither erases a guard nor rewrites a nominal event identity. -/
macro "normalize_artifact_operations " "[" laws:term,* "]"
    " unfolding " "[" definitions:term,* "]" : tactic => do
  let lemmas ← (definitions.getElems ++ laws.getElems).mapM fun term =>
    `(Parser.Tactic.simpLemma| $term:term)
  `(tactic| simp only [$lemmas,*,
    Domain.View.participant, Domain.View.sequence, Domain.View.calculation,
    Domain.View.helper, Domain.View.guard, Domain.View.append, Domain.View.empty,
    Domain.View.receive, Domain.View.send, Domain.View.indicesEmpty,
    Domain.View.indicesAppend, Domain.View.observe, Domain.View.challenge,
    Domain.read, List.mapM_cons, List.mapM_nil, Bind.bind, Option.bind, Option.pure_def,
    Option.map_some, Option.map_none,
    Option.getD_some, Option.getD_none, List.getD_cons_zero, List.getD_cons_succ,
    List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.cons_append, List.nil_append, Domain.sortsMatch, Domain.Value.sort,
    Domain.Payload.ty, Domain.Value.encode, Domain.Payload.ofValue, Domain.dataType,
    ↓reduceTransport,
    List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    List.filter_cons, List.filter_nil, List.all_cons, List.all_nil,
    List.length_cons, List.length_nil, List.length_append,
    Function.comp_apply, id_eq, PIR.Process.bind, PIR.Process.bind_assoc,
    Domain.Calculations.fieldAdd, Domain.Calculations.fieldSubtract,
    Domain.Calculations.fieldMultiply, Domain.Calculations.fieldEqual,
    Domain.Calculations.fieldConstant, Domain.Calculations.indexConstant,
    Domain.Calculations.indexEqual, Domain.Calculations.booleanConstant,
    Domain.Calculations.booleanEqual,
    String.reduceEq, String.reduceBEq, String.reduceAppend,
    Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false,
    Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
    beq_self_eq_true, ite_true, ite_false, ↓reduceDIte,
    decide_true, decide_false, Bool.false_beq, Bool.true_eq_false,
    Nat.zero_le, and_true, true_and, and_self,
    not_false_eq_true, decide_eq_true_eq, decide_eq_false_iff_not])

end Zkc.Construction.ArtifactBinding
