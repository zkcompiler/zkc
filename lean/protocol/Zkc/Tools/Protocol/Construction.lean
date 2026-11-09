module

public import Zkc.Protocol.Construction.Control
public import Std.Tactic.Do
public meta import Lean.Elab.Tactic.VCGen.RuleConstruction
public meta import Lean.Elab.Tactic.VCGen.SpecDB
public meta import Lean.Meta.Tactic.SplitIf
public meta import Lean.Meta.Tactic.Rewrite
public meta import Zkc.Tools.Program.Companions.Report

/-! Checked construction uses upstream VC generation and its specification database.

Dependent Region arguments sometimes require the ordinary Lean elaborator's unification,
rather than the symbolic matcher's restricted unification. This adapter applies the same
upstream-generated backward rule with `Meta.apply`; it introduces no semantic rule or visitor.
-/

public meta section
open Lean Meta Elab Tactic
open Lean.Elab.Tactic.VCGen

namespace ProtocolProof.Tools.Construction

initialize registerTraceClass `Zkc.construction

/-- Reuse a named law with the actual postcondition before general consequence rules.
This preserves inferable mathematical parameters instead of turning them into choice holes. -/
def applyExactPostSpec (goal : MVarId) (candidate : SpecAttr.SpecTheorem)
    (info : WPApp) : MetaM (Option (List MVarId)) := do
  let (parameters, _, proof, type) ← candidate.instantiate
  let_expr Lean.Order.PartialOrder.rel _ _ pre rhs := type | return none
  let some supplied := isWPApp? rhs | return none
  -- A named Region law only targets that body; do not unfold an unrelated callee
  -- while checking whether it can prove a structural return or a different call.
  if supplied.prog.isAppOf ``Zkc.Source.Region.denote &&
      info.prog.isAppOf ``Zkc.Source.Region.denote then
    let expectedBody := info.prog.getAppArgs[info.prog.getAppNumArgs - 2]!
    let suppliedBody := supplied.prog.getAppArgs[supplied.prog.getAppNumArgs - 2]!
    if suppliedBody.getAppFn.isConst && expectedBody.getAppFn.isConst &&
        suppliedBody.getAppFn != expectedBody.getAppFn then return none
  -- Bind the actual meaning before matching its projected value type and WP instance.
  -- An unknown RegionMeaning cannot be recovered by inverting its Value projection.
  unless ← isDefEq supplied.prog info.prog do return none
  unless ← isDefEq supplied.instWP info.instWP do return none
  unless ← isDefEq supplied.post info.post do
    trace[Zkc.construction] "no exact postcondition"
    return none
  unless ← isDefEq supplied.args[9]! info.args[9]! do
    trace[Zkc.construction] "no exact stop"
    return none
  let mut obligations := []
  for parameter in parameters do
    let parameter ← instantiateMVars parameter
    if parameter.isMVar then
      let type ← instantiateMVars (← inferType parameter)
      if type.hasMVar || !(← isProp type) then
        trace[Zkc.construction] "unfixed parameter {parameter}: {type}"
        return none
      obligations := obligations ++ [parameter.mvarId!]
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ expected _ := target | return none
  let premise ← mkFreshExprSyntheticOpaqueMVar
    (← mkAppM ``Lean.Order.PartialOrder.rel #[expected, (← instantiateMVars pre).beta info.excessArgs])
  let result ← mkAppM ``Lean.Order.PartialOrder.rel_trans #[premise, mkAppN proof info.excessArgs]
  unless ← isDefEq (← inferType result) target do return none
  goal.assign result
  return some (premise.mvarId! :: obligations)

/-- Expose a structural continuation before applying a law to the preceding operation.
Only the intermediate bound is synthesized; the actual program, interpretation, final event
and requested bound remain fixed. Monotonicity of the same WP interpretation composes them. -/
def prepareContinuation (goal : MVarId) : MetaM (Option (List MVarId × MVarId)) :=
    goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ expected rhs := target | return none
  let some info := isWPApp? rhs | return none
  let prepared ← withLocalDeclD (← mkFreshBinderNameForTactic `result) info.Value fun value => do
    let continuation ← whnfR (mkApp info.post value)
    let continuation := if continuation.isAppOf ``binderNameHint then
      continuation.getAppArgs.back! else continuation
    let some _ := isWPApp? continuation | return none
    let middle ← mkFreshExprSyntheticOpaqueMVar info.Pred
    let continuationGoal ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``Lean.Order.PartialOrder.rel #[middle, continuation])
    let post ← mkLambdaFVars #[value] middle
    let postProof ← mkLambdaFVars #[value] continuationGoal
    let postProof ← mkExpectedTypeHint postProof
      (← mkAppM ``Lean.Order.PartialOrder.rel #[post, info.post])
    return some (post, postProof, continuationGoal.mvarId!, middle.mvarId!)
  let some (post, postProof, continuationGoal, middle) := prepared | return none
  let arguments := info.args.set! 8 post
  let nextTarget ← mkAppM ``Lean.Order.PartialOrder.rel
    #[expected, mkAppN info.head (arguments ++ info.excessArgs)]
  let nextGoal ← mkFreshExprSyntheticOpaqueMVar nextTarget
  let consequence ← mkAppM ``Std.WP.WP.wp_consequence
    #[info.prog, post, info.post, info.args[9]!, postProof]
  let proof ← mkAppM ``Lean.Order.PartialOrder.rel_trans
    #[nextGoal, mkAppN consequence info.excessArgs]
  unless ← isDefEq (← inferType proof) target do return none
  goal.assign proof
  return some ([continuationGoal, nextGoal.mvarId!], middle)

/-- The marker is private to this construction run; no author choice can acquire it. -/
def isDerived (value : Expr) (derived : Array MVarId) : MetaM Bool := do
  unless value.getAppFn.isMVar && value.getAppArgs.all Expr.isFVar do return false
  unless value.getAppArgs.toList.eraseDups.length == value.getAppNumArgs do return false
  let wanted ← getDelayedMVarRoot value.getAppFn.mvarId!
  return derived.contains wanted

/-- Preserve dependency on branch hypotheses and on generalized state parameters.
Lean's delayed assignments record the exact abstraction map; substitute its arguments back
before assigning the owned bound. Author choices are never added to the owned marker set. -/
partial def assignDerived (value result : Expr) : MetaM Unit := do
  let marker := value.getAppFn.mvarId!
  if let some delayed ← getDelayedMVarAssignment? marker then
    let arguments := value.getAppArgs
    unless arguments.size ≥ delayed.fvars.size do
      throwError "incomplete application of a derived continuation bound"
    let actual := arguments.extract 0 delayed.fvars.size
    let result := result.replaceFVars actual delayed.fvars
    let remaining := (arguments.extract delayed.fvars.size arguments.size).map
      (·.replaceFVars actual delayed.fvars)
    assignDerived (mkAppN (mkMVar delayed.mvarIdPending) remaining) result
  else
    marker.assign (← mkLambdaFVars value.getAppArgs result)

def prepareConditional (goal : MVarId) (derived : Array MVarId) :
    MetaM (Option (List MVarId × Array MVarId)) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ left right := target | return none
  let selected := match isWPApp? right with | some info => info.prog | none => right
  unless selected.isAppOf ``ite || selected.isAppOf ``dite do return none
  let mut added := #[]
  if ← isDerived left derived then
    let condition := selected.getAppArgs[1]!
    let predicate ← inferType left
    let yes ← mkFreshExprSyntheticOpaqueMVar (← mkArrow condition predicate)
    let no ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (← mkAppM ``Not #[condition]) predicate)
    let selectedBound ← mkAppOptM ``dite
      #[some predicate, some condition, some selected.getAppArgs[2]!, some yes, some no]
    assignDerived left selectedBound
    added := #[yes.mvarId!, no.mvarId!]
  if let some (yes, no) ← SplitIf.splitIfAt? goal selected none then
    return some ([← simpIfTarget yes.mvarId (useNewSemantics := true),
      ← simpIfTarget no.mvarId (useNewSemantics := true)], added)
  return none

/-- Only structural intermediate bounds can be inferred from a checked law. A residual WP
is not silently accepted as a mathematical premise or exported to a protocol author. -/
def finishDerived (goal : MVarId) (derived : Array MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ left right := target | return false
  unless ← isDerived left derived do return false
  if right.hasMVar || (right.find? fun expression => (isWPApp? expression).isSome).isSome then
    return false
  assignDerived left right
  goal.assign (← mkAppOptM ``Lean.Order.PartialOrder.rel_refl #[none, none, some right])
  return true

def applyDependentSpec (goal : MVarId) (regionOnly : Bool := false) :
    TacticM (Option (List MVarId)) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .app _ rhs := target | return none
  let some info := isWPApp? rhs | return none
  if regionOnly && !info.prog.isAppOf ``Zkc.Source.Region.denote then return none
  if info.prog.isAppOf ``ite || info.prog.isAppOf ``dite then
    if let some (yes, no) ← SplitIf.splitIfAt? goal info.prog none then
      return some [← simpIfTarget yes.mvarId (useNewSemantics := true),
        ← simpIfTarget no.mvarId (useNewSemantics := true)]
  if info.prog.isAppOf ``Zkc.Source.Region.denote then
    trace[Zkc.construction]
      "region body head {info.prog.getAppArgs[info.prog.getAppNumArgs - 2]!.getAppFn}"
  let database ← SpecAttr.getSpecTheorems
  let indexed ← Sym.SymM.run (database.findSpecs info.prog)
  -- Definitional expansion of a dependent meaning can change discrimination-tree keys.
  -- Discovery may over-approximate; application still checks the actual complete program.
  let contextual := database.specs.values.filter fun candidate =>
    candidate.pattern.pattern.getAppFn == info.prog.getAppFn &&
      !database.erased.contains candidate.proof && !indexed.contains candidate
  let candidates := (indexed ++ contextual).insertionSort (·.priority > ·.priority)
  for candidate in candidates do
    trace[Zkc.construction] "candidate {candidate.proof} for {info.prog.getAppFn}"
    let saved ← saveState
    try
      if let some goals ← applyExactPostSpec goal candidate info then
        return some goals
      saved.restore
      let pattern := candidate.pattern.pattern
      if pattern.isAppOf ``Zkc.Source.Region.denote &&
          info.prog.isAppOf ``Zkc.Source.Region.denote then
        let given := pattern.getAppArgs[pattern.getAppNumArgs - 2]!.getAppFn
        let wanted := info.prog.getAppArgs[info.prog.getAppNumArgs - 2]!.getAppFn
        if given.isConst && wanted.isConst && given != wanted then continue
      let some rule ← (tryMkBackwardRuleFromSpec candidate info).run |
        saved.restore
        continue
      let goals ← goal.apply rule.expr
      return some goals
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      let message ← error.toMessageData.toString
      trace[Zkc.construction] "application failed: {message.take 600}"
      for failure in [Kernel.Exception.deterministicTimeout, .deepRecursion, .excessiveMemory] do
        if message == (← (failure.toMessageData (← getOptions)).toString) then throw error
      saved.restore
  return none

/-- Give reply-dependent primitive continuations to the same monadic construction path.
The atomic call rule leaves no residual execution fold for an author to assemble. -/
def prepareCall (goal : MVarId) : MetaM (Option (List MVarId)) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let_expr Lean.Order.PartialOrder.rel _ _ _ rhs := target | return none
  let some info := isWPApp? rhs | return none
  unless info.prog.isAppOf ``PIR.Process.call do return none
  let arguments := info.prog.getAppArgs
  let next := arguments.back!
  if next.eta.getAppFn.isConstOf ``PIR.Process.done then return none
  let equality ← mkAppOptM ``ProtocolProof.Construction.processCallBind
    #[some arguments[0]!, some arguments[1]!, some arguments[2]!, some next]
  let rewritten ← goal.rewrite target equality (config := { occs := .pos [1] })
  let child ← goal.replaceTargetEq rewritten.eNew rewritten.eqProof
  return some (child :: rewritten.mvarIds)

def construct (choices : Array (TSyntax `term)) : TacticM Unit := do
  for goal in ← getGoals do
    let fixed ← goal.withContext <| instantiateMVars (← goal.getType)
    if fixed.hasMVar then
      throwError "source construction requires a fixed request before rule or choice selection"
  let mut derived : Array MVarId := #[]
  let mut choiceIndex := 0
  let mut pending ← getGoals
  let mut remaining : List MVarId := []
  let mut steps : Nat := 0
  while !pending.isEmpty do
    checkSystem "source proof construction"
    steps := steps + 1
    if steps > 4096 then throwError "source construction exceeded its step limit"
    let goal := pending.head!
    pending := pending.tail!
    setGoals [goal]
    evalTactic (← `(tactic| all_goals simp (config := { failIfUnchanged := false }) only
      [binderNameHint, Zkc.Source.Regions.denote, Zkc.Source.Operands.eval,
       Zkc.Source.Values.get_here, Zkc.Source.Values.get_there,
       Zkc.Source.Values.get, Zkc.Source.Values.singleton,
       Zkc.Source.Environment.push_here, Zkc.Source.Environment.push_there,
       Zkc.Source.Environment.prepend_weakenPrefix, Zkc.Source.Environment.prepend_here,
       Zkc.Source.Environment.prepend_weakenSuffix,
       Zkc.Source.Environment.prepend, Zkc.Source.Environment.push]))
    if (← getGoals).isEmpty then continue
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    trace[Zkc.construction] "step {steps}: {target.getAppFn}"
    let structural ← goal.withContext <| forallTelescope target fun _ body => do
      if body.isAppOf ``Std.WP.Triple then return true
      let_expr Lean.Order.PartialOrder.rel _ _ _ rhs := body | return false
      return (isWPApp? rhs).isSome
    if target.isAppOf ``Std.WP.Triple then
      let unfolded ← goal.withContext <| goal.apply (← mkConstWithFreshMVarLevels ``Std.WP.Triple.intro)
      pending := unfolded ++ pending
      continue
    if target.isForall then
      let .forallE name _ _ _ := target | unreachable!
      let name ← goal.withContext <| mkFreshBinderNameForTactic name
      let (_, child) ← goal.intro name
      setGoals [child]
      pending := (← getGoals) ++ pending
      continue
    if let some children ← prepareCall goal then
      pending := children ++ pending
      continue
    if let some (children, middle) ← prepareContinuation goal then
      derived := derived.push middle
      pending := children ++ pending
      continue
    if let some (children, added) ← prepareConditional goal derived then
      derived := derived ++ added
      pending := children ++ pending
      continue
    if ← finishDerived goal derived then continue
    if let some children ← applyDependentSpec goal true then
      pending := children ++ pending
      continue
    if structural then
      let saved ← saveState
      evalTactic (← `(tactic| vcgen (stepLimit := 1) (errorOnMissingSpec := false)))
      let children ← getGoals
      let unchanged ← match children with
        | [child] => do pure ((← instantiateMVars (← child.getType)) == target)
        | _ => pure false
      if !unchanged then
        pending := children ++ pending
        continue
      saved.restore
    evalTactic (← `(tactic| all_goals try simp only [Zkc.Source.Regions.denote,
      Zkc.Source.Operands.eval, Zkc.Source.Values.get_here, Zkc.Source.Values.get_there,
       Zkc.Source.Values.get, Zkc.Source.Values.singleton,
      Zkc.Source.Environment.push_here, Zkc.Source.Environment.push_there,
       Zkc.Source.Environment.prepend_weakenPrefix, Zkc.Source.Environment.prepend_here,
       Zkc.Source.Environment.prepend_weakenSuffix,
      Zkc.Source.Environment.prepend, Zkc.Source.Environment.push]))
    evalTactic (← `(tactic| all_goals try exact Lean.Order.PartialOrder.rel_refl))
    for current in ← getGoals do
      let type ← current.withContext <| instantiateMVars (← current.getType)
      if Do.SpecAttr.isSpecInvariantType (← getEnv) type && choiceIndex < choices.size then
        if type.hasMVar then throwError "mathematical choice type is not fixed: {type}"
        let value ← current.withContext do
          let value ← Term.withoutErrToSorry <| Term.elabTermEnsuringType choices[choiceIndex]! type
          Term.synthesizeSyntheticMVarsNoPostponing
          let value ← instantiateMVars value
          if value.hasMVar then throwError "mathematical choice leaves unsolved arguments"
          return value
        current.assign value
        choiceIndex := choiceIndex + 1
      else if ← finishDerived current derived then
        pure ()
      else if let some children ← applyDependentSpec current then
        pending := children ++ pending
      else
        remaining := remaining ++ [current]
  if choiceIndex < choices.size then throwError "unused mathematical choice"

  setGoals remaining
  evalTactic (← `(tactic| all_goals simp (config := { failIfUnchanged := false }) only [
    ProtocolProof.OperationSpec.wp_upper, ProtocolProof.OperationSpec.wp_lower,
    ProtocolProof.wpFold_done, ProtocolProof.wpFold_halt, ProtocolProof.wpFold_bind,
    ProtocolProof.wpFold_call, ProtocolProof.wpFold_ite,
    ProtocolProof.OperationSpec.outcomePost, ProtocolProof.upper_entailment,
    ProtocolProof.lower_entailment, OrderDual.ofDual_toDual, OrderDual.toDual_ofDual, binderNameHint,
    Zkc.Source.Regions.denote,
    Zkc.Source.Values.get_here, Zkc.Source.Values.get_there,
       Zkc.Source.Values.get, Zkc.Source.Values.singleton,
    Zkc.Source.Operands.eval, Zkc.Source.Environment.push_here, Zkc.Source.Environment.push_there,
       Zkc.Source.Environment.prepend_weakenPrefix, Zkc.Source.Environment.prepend_here,
    Zkc.Source.Environment.prepend_weakenSuffix, Zkc.Source.Environment.prepend,
    Zkc.Source.Environment.push]))
  evalTactic (← `(tactic| all_goals try exact Lean.Order.PartialOrder.rel_refl))

  for goal in ← getGoals do
    let type ← goal.withContext <| instantiateMVars (← goal.getType)
    if type.hasMVar then
      throwError "construction left an unfixed mathematical choice or intermediate bound:\n{type}"
    let isProp ← goal.withContext <| Meta.isProp type
    unless isProp do
      throwError "missing typed mathematical choice:\n{type}"
    if (type.find? fun expression =>
        (isWPApp? expression).isSome || expression.isAppOf ``Std.WP.Triple ||
        expression.isAppOf ``ProtocolProof.wpFold ||
        expression.isAppOf ``Zkc.Source.Region.denote).isSome then
      throwError "missing common construction rule; execution structure is not a mathematical obligation:\n{type}"

/-- Reuse the existing obligation record with the actual local context on demand.
An open authoring goal is not evidence that a request or security endpoint holds. -/
elab "report_construction_goals" : tactic => do
  for goal in ← getGoals do
    let record ← goal.withContext do
      let expected ← instantiateMVars (← goal.getType)
      if expected.hasMVar then throwError "cannot report an unfixed construction obligation"
      ZkcTools.Companions.report {
        identity := (← goal.getTag).toString,
        responsibility := "mathematical construction obligation", expected := expected }
        (.openObligation "mathematical proof remains required" #[])
    logInfo m!"{record.compress}"

elab "construct_region" : tactic => construct #[]

elab "construct_region" " with_invariants " "[" choices:term,* "]" : tactic =>
  construct choices.getElems

end ProtocolProof.Tools.Construction
