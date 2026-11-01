module

public import Zkc.Construction.ArtifactBinding
public import Zkc.Construction.OriginalHeadReduction
public meta import Lean.Elab.Tactic
public meta import ZkcTools.ConstructionBindings.TransportReduction

@[expose] public meta section

/-! Structural proof search for a fixed original/compiled process pair.
Normalization and all side conditions are supplied as scoped tactics. There
is no protocol registry, instruction-count recognizer, or trusted evaluator. -/
set_option autoImplicit false
namespace Zkc.Construction.ArtifactBinding
open Lean Meta Elab Tactic

/-- Saturate explicit local equations, retaining reductions that expose a head
constructor even when they are definitionally equal. Errors are not hidden as
an unsupported structural case. The supplied pass must also succeed at rest. -/
elab "saturate_artifact " body:tacticSeq : tactic => do
  let mut changed := true
  while changed do
    let beforeGoals ← getGoals
    let before ← beforeGoals.mapM fun goal => do instantiateMVars (← goal.getType)
    evalTactic body
    let afterGoals ← getGoals
    let after ← afterGoals.mapM fun goal => do instantiateMVars (← goal.getType)
    changed := before != after && !afterGoals.isEmpty

partial def startsCheckpoint (expression : Expr) : Bool :=
  if expression.isAppOf ``PIR.Process.call then
    expression.getAppArgs[expression.getAppArgs.size - 2]!.isAppOf ``Domain.Effect.checkpoint
  else if expression.isAppOf ``PIR.Process.bind then
    startsCheckpoint expression.getAppArgs[expression.getAppArgs.size - 2]!
  else false

/-- A supplied component certificate can close a reached prefix. Composition
uses the ordinary Simulation.bind rule and retains its frame and return laws. -/
def applyComponent (goal : MVarId) (rule : TSyntax `term) : TacticM (List MVarId) := do
  let target ← instantiateMVars (← goal.getType)
  let indices := target.getAppArgs
  unless indices.size ≥ 2 && indices[indices.size - 2]!.isAppOf ``PIR.Process.bind &&
      indices.back!.isAppOf ``PIR.Process.bind do
    throwError "expected two reached component prefixes"
  let proof ← Term.elabTerm rule none
  let (arguments, _, type) ← forallMetaTelescopeReducing (← inferType proof)
  let type ← whnf type
  unless type.isAppOf ``Original.Simulation do
    throwError "expected a structural component certificate"
  let application := mkAppN proof arguments
  let obligations ← goal.apply (← mkConstWithFreshMVarLevels ``Original.Simulation.bind)
  let head :: remaining := obligations
    | throwError "component composition did not expose its prefix certificate"
  let conditions ← head.apply application
  let mut pending := conditions ++ remaining
  for argument in arguments do
    if let .mvar id := argument then
      unless (← id.isAssigned) || pending.contains id do
        pending := pending ++ [id]
  return pending

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
            if ← obligation.isAssigned then continue
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
      let target ← whnf (← instantiateMVars (← current.getType))
      unless target.isAppOf ``Original.Simulation do
        throwError "expected a structural simulation: {target}"
      let args := target.getAppArgs
      let source := args[args.size - 2]!
      let actual := args.back!
      let condition := if source.isAppOf ``ite then some source.getAppArgs[1]!
        else if actual.isAppOf ``ite then some actual.getAppArgs[1]! else none
      if source.isAppOf ``ite && actual.isAppOf ``ite then
       if let some condition := condition then
        let condition ← Term.exprToSyntax condition
        evalTactic (← `(tactic| by_cases artifactCondition : $condition))
        for branch in ← getGoals do derive branch rules normalize side
        return
      let saved ← saveState
      let mut applied : Option (List MVarId) := none
      -- Normalization can expose a checkpoint that was hidden by a view
      -- wrapper. Discharge that reached frame before matching components.
      if startsCheckpoint actual then
        try
          applied := some (← current.apply (← mkConstWithFreshMVarLevels ``Original.Simulation.checkpoint))
        catch _ => pure ()
      let processes := target.getAppArgs
      let source := processes[processes.size - 2]!
      let actual := processes.back!
      -- A reached concrete constructor needs no component unification. In
      -- particular, do not unfold an unrelated closed helper while matching
      -- an already exposed nominal call and its universally quantified reply.
      for (constructor, rule) in [(``PIR.Process.done, ``Original.Simulation.done),
          (``PIR.Process.halt, ``Original.Simulation.halt),
          (``PIR.Process.call, ``Original.Simulation.call)] do
        if applied.isSome then break
        if source.isAppOf constructor && actual.isAppOf constructor then
          saved.restore
          try
            applied := some (← current.apply (← mkConstWithFreshMVarLevels rule))
          catch _ => pure ()
      for rule in rules do
        if applied.isSome then break
        saved.restore
        try
          let proof ← Term.elabTerm rule none
          let obligations ← current.apply proof
          applied := some obligations
          break
        catch _ => pure ()
      if applied.isNone then
        for rule in rules do
          saved.restore
          try
            applied := some (← applyComponent current rule)
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
        -- Equations can determine witnesses hidden by an opaque component certificate.
        -- Solve them before asking the side tactic to construct an unconstrained witness.
        let mut primary : List MVarId := []
        let mut witnesses : List MVarId := []
        for obligation in obligations do
          if ← obligation.isAssigned then continue
          let primaryGoal ← obligation.withContext do
            let type ← instantiateMVars (← obligation.getType)
            let simulation ← forallTelescope type fun _ body => pure (body.isAppOf ``Original.Simulation)
            return simulation || (← isProp type)
          if primaryGoal then primary := primary ++ [obligation]
          else witnesses := witnesses ++ [obligation]
        for obligation in primary ++ witnesses do
          if ← obligation.isAssigned then continue
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
  `(tactic| simp (config := { failIfUnchanged := false }) only [↓Original.stopAtCall, $lemmas,*,
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
