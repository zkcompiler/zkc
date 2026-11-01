module

public meta import Lean.Elab.Tactic
public import ZkcSecurity.Bindings.Source.PropertyAssembly

public meta section

/-! An untrusted application assembler. Supplied rules are component laws,
not a theorem for the assembled root. Every attempted head must unify with
the actual process, including its arguments and full returned relation. The
continuation is assembled using Pair.bind; no parallel induction calculus or
execution semantics is introduced. Unsupported seams remain ordinary goals.
-/
set_option autoImplicit false
namespace ZkcSecurity.Tools.SourceProperties
open Lean Meta Elab Tactic

/-- Only the internal composition may infer intermediate relations and costs.
The caller fixes the complete property before any selected rule is elaborated. -/
private def requireFixedProperty : TacticM Unit := withMainContext do
  if (← instantiateMVars (← getMainTarget)).hasExprMVar then
    throwError "source property assembly requires a fixed process, relation and requested bound"

/-- Instantiate a selected contract against the actual typed process heads.
Remaining proposition arguments are ordinary local seam goals; search never
registers them as assumptions. -/
private def selectedLaw (rule : TSyntax `term) (judgment : Name)
    (heads : Array Expr) (rewrites : Array (TSyntax `term)) : TacticM Expr := withMainContext do
  let value ← Term.elabTerm rule none
  let (arguments, _, result) ← forallMetaTelescope (← inferType value)
  let result := result.headBeta.consumeMData
  let parts := result.getAppArgs
  unless result.isAppOf judgment && parts.size ≥ heads.size do
    throwError "selected source rule does not conclude the required property"
  for index in [:heads.size] do
    unless ← withTransparency .default <|
        isDefEq parts[parts.size - heads.size + index]! heads[index]! do
      throwError "selected source rule does not match the actual typed component"
  if judgment == ``Zkc.Obligations.Derivation then
    let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
    unless ← isDefEq parts[parts.size - 2]! target.getAppArgs[target.getAppNumArgs - 2]! do
      throwError "source component uses a different reached history"
  let pending ← getGoals
  let lemmas ← rewrites.mapM fun term => `(Parser.Tactic.simpLemma| $term:term)
  for argument in arguments do
    let argument ← instantiateMVars argument
    if argument.isMVar && (← isProp (← inferType argument)) then
      setGoals [argument.mvarId!]
      withTransparency .default <| evalTactic (← `(tactic| first
        | assumption
        | (solve | solve_by_elim (config := { transparency := .default }))
        | decide +kernel
        | (solve | simp_all only [$lemmas,*])))
      unless (← getGoals).isEmpty do throwError "open typed source component seam"
  setGoals pending
  instantiateMVars (mkAppN value arguments)

private def bindHead (process : Expr) : MetaM Expr := do
  let some bound ← whnfUntil process ``PIR.Process.bind
    | throwError "expected a source application followed by its continuation"
  let args := bound.getAppArgs
  return args[args.size - 2]!

/-- Expose the checked composition's process heads by definitional equality.
This discards selector projections before property-method elaboration; it does
not inspect source names or prove a property. -/
elab "expose_source_composition" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).headBeta.consumeMData
  let mut args := target.getAppArgs
  let indices ← if target.isAppOf ``ZkcSecurity.Source.Pair then pure #[args.size - 2, args.size - 1]
    else if target.isAppOf ``Zkc.Obligations.Derivation then pure #[args.size - 1]
    else if target.isAppOf ``ZkcSecurity.FiatShamir.Typed.ChargedCostBound then pure #[args.size - 3]
    else throwError "expected a source Pair, rejection or cost obligation"
  for index in indices do
    let process ← whnfHeadPred args[index]! fun e => pure
      (!(e.isAppOf ``PIR.Process.bind || e.isAppOf ``PIR.Process.done))
    args := args.set! index process
  let exposed ← withTransparency .default <| goal.change (mkAppN target.getAppFn args)
  replaceMainGoal [exposed]

private partial def assemblePairs (rules rewrites : Array (TSyntax `term)) (depth : Nat) : TacticM Unit := withMainContext do
  if depth == 0 then throwError "source pair assembly exceeded its structural search depth"
  let lemmas ← rewrites.mapM fun term => `(Parser.Tactic.simpLemma| $term:term)
  for rewrite in rewrites do
    let rule ← `(Parser.Tactic.rwRule| $rewrite:term)
    evalTactic (← `(tactic| try rw [$rule]))
  let saved ← saveState
  try
    let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
    let parts := target.getAppArgs
    unless parts.size ≥ 2 && parts[parts.size - 2]!.headBeta.consumeMData.isAppOf ``PIR.Process.done &&
        parts[parts.size - 1]!.headBeta.consumeMData.isAppOf ``PIR.Process.done do
      throwError "the current application is not a pure paired return"
    evalTactic (← `(tactic| exact ZkcSecurity.Source.Pair.done (by
      first | rfl | (solve | repeat' first | assumption | constructor) | (simp_all only [$lemmas,*]; aesop))))
    return
  catch error =>
    if error.isRuntime then throw error
    if let .internal _ _ := error then throw error
    saved.restore
  let mut lastReason := "no selected head matched"
  for rule in rules do
    let saved ← saveState
    try
      let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
      let args := target.getAppArgs
      let selected ← selectedLaw rule ``ZkcSecurity.Source.Pair
        #[← bindHead args[args.size - 2]!, ← bindHead args.back!] rewrites
      let left ← whnfUntil args[args.size - 2]! ``PIR.Process.bind
      let right ← whnfUntil args.back! ``PIR.Process.bind
      let some left := left | throwError "source pair left continuation is missing"
      let some right := right | throwError "source pair right continuation is missing"
      let applied ← mkAppOptM ``ZkcSecurity.Source.Pair.bind
        #[none, none, none, some args[1]!, some args[2]!, none, none, some args[4]!,
          none, none, some selected, some left.getAppArgs.back!, some right.getAppArgs.back!]
      let type ← whnf (← inferType applied)
      let suffix ← mkFreshExprSyntheticOpaqueMVar type.bindingDomain!
      let proof := mkApp applied suffix
      unless ← isDefEq (← inferType proof) target do
        throwError "selected Pair law does not compose at the complete source processes"
      (← getMainGoal).assign proof
      setGoals [suffix.mvarId!]
      evalTactic (← `(tactic| intro a b related; try simp only [related, $lemmas,*]))
      if (← getGoals).isEmpty then return
      assemblePairs rules rewrites (depth - 1)
      return
    catch error =>
      if error.isRuntime then throw error
      if let .internal _ _ := error then throw error
      let reason ← error.toMessageData.toString
      saved.restore
      lastReason := lastReason ++ "\n" ++ reason
  throwError "open source pair seam: {lastReason}\nExpected: {← getMainTarget}"

syntax "assemble_source_pairs " "[" term,* "]" " simplifying " "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| assemble_source_pairs [$rules:term,*] simplifying [$rewrites:term,*]) => do
      requireFixedProperty
      assemblePairs rules.getElems rewrites.getElems 64

private partial def assembleNo (rules rewrites : Array (TSyntax `term)) (depth : Nat) : TacticM Unit := withMainContext do
  if depth == 0 then throwError "source No assembly exceeded its structural search depth"
  let lemmas ← rewrites.mapM fun term => `(Parser.Tactic.simpLemma| $term:term)
  evalTactic (← `(tactic| try simp only [$lemmas,*]))
  let saved ← saveState
  let mut terminalReason := ""
  try
    let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
    let parts := target.getAppArgs
    unless !parts.isEmpty && parts[parts.size - 1]!.headBeta.consumeMData.isAppOf ``PIR.Process.done do
      throwError "the current application is not a pure source return"
    evalTactic (← `(tactic| exact Zkc.Obligations.Derivation.done (by
      first | rfl | (solve | repeat' first | assumption | constructor) | (simp_all only [$lemmas,*]; aesop))))
    return
  catch error =>
    if error.isRuntime then throw error
    if let .internal _ _ := error then throw error
    terminalReason ← error.toMessageData.toString
    saved.restore
  let mut lastReason := terminalReason
  for rule in rules do
    let saved ← saveState
    try
      withTransparency .reducible <| evalTactic (← `(tactic| exact ($rule _)))
      return
    catch error =>
      if error.isRuntime then throw error
      if let .internal _ _ := error then throw error
      saved.restore
    try
      let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
      let selected ← selectedLaw rule ``Zkc.Obligations.Derivation
        #[← bindHead target.getAppArgs.back!] rewrites
      let selected ← Term.exprToSyntax selected
      withTransparency .default <| evalTactic
        (← `(tactic| refine Zkc.Obligations.Derivation.bind $selected _ ?_))
      evalTactic (← `(tactic| intro reached value residual))
      evalTactic (← `(tactic| first | (obtain ⟨accepted, rfl, valid⟩ := residual; try simp only [$lemmas,*]) | (try simp only [residual, $lemmas,*])))
      if (← getGoals).isEmpty then return
      assembleNo rules rewrites (depth - 1)
      return
    catch error =>
      if error.isRuntime then throw error
      if let .internal _ _ := error then throw error
      let reason ← error.toMessageData.toString
      saved.restore
      lastReason := lastReason ++ "\n" ++ reason
  throwError "open source No seam: {lastReason}\nExpected: {← getMainTarget}"

syntax "assemble_source_no " "[" term,* "]" " simplifying " "[" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| assemble_source_no [$rules:term,*] simplifying [$rewrites:term,*]) => do
      requireFixedProperty
      assembleNo rules.getElems rewrites.getElems 64

private partial def assembleCost (rules rewrites : Array (TSyntax `term)) (depth : Nat) : TacticM Unit := withMainContext do
  if depth == 0 then throwError "source cost assembly exceeded its structural search depth"
  let lemmas ← rewrites.mapM fun term => `(Parser.Tactic.simpLemma| $term:term)
  evalTactic (← `(tactic| try simp only [$lemmas,*]))
  let saved ← saveState
  try
    evalTactic (← `(tactic| exact ZkcSecurity.FiatShamir.CostComposition.done _))
    return
  catch error =>
    if error.isRuntime then throw error
    if let .internal _ _ := error then throw error
    saved.restore
  let mut reasons := ""
  for rule in rules do
    let saved ← saveState
    try
      let target := (← instantiateMVars (← getMainTarget)).headBeta.consumeMData
      let args := target.getAppArgs
      let bound ← mkFreshExprMVar (← inferType args.back!)
      let selected ← selectedLaw rule ``ZkcSecurity.FiatShamir.Typed.ChargedCostBound
        #[← bindHead args[args.size - 3]!, args[args.size - 2]!, bound] rewrites
      let law := selected
      let lawArgs := (← inferType law).getAppArgs
      let first := lawArgs.back!
      let second ← mkFreshExprMVar (← inferType first)
      let boundProcess ← whnfUntil args[args.size - 3]! ``PIR.Process.bind
      let some boundProcess := boundProcess | throwError "source cost continuation is missing"
      let next := boundProcess.getAppArgs.back!
      let applied ← mkAppM ``ZkcSecurity.FiatShamir.CostComposition.bind
        #[← bindHead args[args.size - 3]!, next, first, second, law]
      let type ← whnf (← inferType applied)
      let suffix ← mkFreshExprSyntheticOpaqueMVar type.bindingDomain!
      let proof := mkApp applied suffix
      unless ← isDefEq (← inferType proof) target do
        throwError "source cost does not compose at the requested complete process"
      (← getMainGoal).assign proof
      setGoals [suffix.mvarId!]
      evalTactic (← `(tactic| intro value reached))
      assembleCost rules rewrites (depth - 1)
      return
    catch error =>
      if error.isRuntime then throw error
      if let .internal _ _ := error then throw error
      reasons := reasons ++ "\n" ++ (← error.toMessageData.toString)
      saved.restore
  throwError "open source cost seam: {reasons}\nExpected: {← getMainTarget}"

syntax "assemble_source_cost " "[" term,* "]" " simplifying " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| assemble_source_cost [$rules:term,*] simplifying [$rewrites:term,*]) => do
      requireFixedProperty
      evalTactic (← `(tactic| apply ZkcSecurity.FiatShamir.CostComposition.mono (large := _) ?_ ?_))
      let goals ← getGoals
      let mut bounded := none
      for goal in goals do
        if (← goal.getType).isAppOf ``ZkcSecurity.FiatShamir.Typed.ChargedCostBound then
          bounded := some goal
      let some boundedGoal := bounded | throwError "source cost bound goal was not exposed"
      setGoals [boundedGoal]
      assembleCost rules.getElems rewrites.getElems 64
      let mut remaining := []
      for goal in goals do
        unless ← goal.isAssigned do remaining := remaining ++ [goal]
      setGoals remaining
      let lemmas ← rewrites.getElems.mapM fun term => `(Parser.Tactic.simpLemma| $term:term)
      evalTactic (← `(tactic| simp only [$lemmas,*, add_zero, nsmul_eq_mul]; first | rfl | (ring_nf; try rfl)))

end ZkcSecurity.Tools.SourceProperties
