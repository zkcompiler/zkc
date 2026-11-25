module

public import ZkcFormal.Walk
public import ZkcFormal.Written.SiteCaps
public import ZkcFormal.Written.Blind
public meta import Lean

public meta section
open Lean Meta Elab Tactic

/-!
What a text says at an effect, under the judgment with fees.

A walk stops where the goal is the judgment at an effect. Under the judgment with fees within
the allowances of a table of caps, a text says one of two things there. Each of the two first
walks to the next effect where the goal is not at one, so a text writes no `walk` before them;
it writes `walk as …` where it names a fork on the way.

- `walk_free as v`: nothing is excluded and no fee is paid. The reply is `v`, and
  `permitted_v` says that it is a permitted reply. A message got or a value heard has no
  sampler and can only be met this way; a text names the reply here, since it is the reply
  that a later excluded set speaks of.
- `walk_pay fee excluding set as v kept`: a coin of the role pays `fee` for the replies in
  `set`. The tactic reads from the goal what the program and the table determine: the table and
  the path at which the run started, from the judgment; where the effect occurs, from the
  effect; the sampler of the coin's law. It leaves, in this order, what the text has to say:
  `weight`, that the sampler draws a reply of the set with probability at most the fee; `within`,
  that the fee is within the budget, unless it is a hypothesis as it stands or the kernel
  decides it on closed numbers; `cap`, that the fee
  is within the cap that the table gives the draw, unless the kernel decides it; and the rest
  of the walk after a reply `v` outside the set, with `permitted_v` and `kept : ¬ set v`.

Both apply a rule of `ZkcFormal.Written.SiteCaps` (`charged_free`, `charged_pay_at`) and
nothing else: what they leave is what the rule asks.
-/

namespace ZkcFormal.Written

/-- Whether a goal is the judgment at an effect. -/
private def isAtEffect (goal : MVarId) : MetaM Bool := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let args := target.getAppArgs
  return target.getAppFn.isConstOf ``Zkc.Core.Process.interpret && args.size ≥ 9 &&
    args[7]!.isAppOfArity ``Zkc.Core.Process.call 5

/-- The judgment at an effect that the main goal is, walked to where it is not at one: the
arguments of the judgment and the effect. -/
private def atEffect (who : String) : TacticM (Array Expr × Expr) := do
  unless ← isAtEffect (← getMainGoal) do
    evalTactic (← `(tactic| walk))
  let goal ← getMainGoal
  goal.withContext do
    let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
    unless ← isAtEffect goal do
      throwError "{who}: the walk does not stop at an effect{indentExpr target}"
    let args := target.getAppArgs
    -- inside an application, a judgment that nothing says reads no peer is renamed: the rules
    -- of a fee are about the judgment with fees itself
    if args[4]!.isAppOf ``Zkc.Core.ProcessJudgment.renamed then
      throwError "{who}: the effect is inside an application, under a judgment with its peers \
        renamed: nothing says that the judgment reads no peer of an effect (a theorem with the \
        label `walk_blind`, or a hypothesis `Blind ρ judgment` of the goal), so the goal in the \
        callee is not stated under the judgment with fees itself{indentExpr args[4]!}"
    return (args, args[7]!.getArg! 3)

/-- The reply that a tactic introduced, at its computed type, so that a text reads it as a
value: the type of the reply of its effect is computed to the type of values that it is, and
the types inside that one (the parts of a tuple, the items of a sequence) to their carriers. -/
private def readReply (goal : MVarId) (reply : Lean.Name) : MetaM MVarId := goal.withContext do
  let some decl := (← getLCtx).findFromUserName? reply | return goal
  goal.replaceLocalDeclDefEq decl.fvarId (← ZkcFormal.computedTypes (← whnfD decl.type))

/-- The name of the hypothesis that a reply is permitted. -/
private def permittedName (reply : TSyntax `ident) : TSyntax `ident :=
  mkIdentFrom reply (Name.mkSimple s!"permitted_{reply.getId}")

/-- At an effect, nothing is excluded and no fee is paid: the reply is `v`, and `permitted_v`
says that it is permitted. -/
elab "walk_free" " as " reply:ident : tactic => do
  let _ ← atEffect "walk_free"
  let permitted := permittedName reply
  evalTactic (← `(tactic|
    refine ZkcFormal.Written.charged_free _ _ _ _ _ _ fun $reply $permitted => ?_))
  replaceMainGoal [← readReply (← getMainGoal) reply.getId]

/-- The parts of a path after its start, where the path is the start with lists appended. -/
private partial def afterStart (path start : Expr) : MetaM (Option (List Expr)) := do
  if ← withReducible (isDefEq path start) then return some []
  if path.isAppOfArity ``HAppend.hAppend 6 then
    if let some before ← afterStart (path.getArg! 4) start then
      return some (before ++ [path.getArg! 5])
  return none

/-- At a coin, pay `fee` for the replies in `set`: see the header of this module. -/
elab "walk_pay " fee:term:max &" excluding " set:term:max " as " reply:ident kept:ident : tactic =>
    do
  let (args, op) ← atEffect "walk_pay"
  withMainContext do
  -- the table, the use at which the run started and its path, from the judgment
  let judgment ← whnfR args[4]!
  unless judgment.isAppOf ``Zkc.Core.ProcessJudgment.charged do
    throwError "walk_pay: the judgment is not the one with fees{indentExpr judgment}"
  -- a text may have its own name for the fees of a table: names that only abbreviate are read
  let pays ← whnfR judgment.appArg!
  unless pays.isAppOf ``ZkcFormal.ProbabilisticProcess.paysWithin do
    throwError "walk_pay: the fees are not those within allowances{indentExpr pays}"
  -- a function of the effect that only applies the table's allowances is those allowances,
  -- as written and as a name that abbreviates them unfolds
  let allowance := pays.appArg!.eta
  let allowance ← do
    if allowance.isAppOf ``Zkc.Subject.CapTable.allowance ||
        allowance.isAppOf ``Zkc.Subject.CapTable.allowanceFrom then pure allowance
    else pure (← whnfR allowance).eta
  let a := allowance.getAppArgs
  let (model, table, place, start) ←
    if allowance.isAppOfArity ``Zkc.Subject.CapTable.allowance 4 then
      pure (a[1]!, a[2]!, ← mkAppM ``Zkc.Subject.CapTable.root #[a[2]!], a[3]!)
    else if allowance.isAppOfArity ``Zkc.Subject.CapTable.allowanceFrom 5 then
      pure (a[1]!, a[2]!, a[3]!, a[4]!)
    else throwError "walk_pay: the allowances are not those of a table of caps{indentExpr allowance}"
  -- where the effect occurs: the start's path, then the frames of the loops and applications
  -- entered since, and the key of the instruction
  let occurrence ← whnf (← mkAppM ``Zkc.Core.ROp.occurrence #[model, op])
  unless occurrence.isAppOfArity ``Zkc.Core.Occurrence.mk 2 do
    throwError "walk_pay: the effect does not say where it occurs{indentExpr occurrence}"
  let key := occurrence.getArg! 1
  let some parts ← afterStart (occurrence.getArg! 0) start
    | throwError "walk_pay: the effect does not occur below the start of the run{indentExpr (occurrence.getArg! 0)}"
  let frame := mkConst ``Zkc.Core.Frame
  let mut frames ← mkListLit frame []
  for part in parts do
    frames ← mkAppM ``HAppend.hAppend #[frames, part]
  let rest ← Meta.reduce frames (skipTypes := true) (skipProofs := true)
  let permitted := permittedName reply
  let tableStx ← Term.exprToSyntax table
  let placeStx ← Term.exprToSyntax place
  let startStx ← Term.exprToSyntax start
  let restStx ← Term.exprToSyntax rest
  let keyStx ← Term.exprToSyntax key
  -- the goals that the rule leaves are those of this goal; what else is open stays behind them
  let others := (← getGoals).drop 1
  evalTactic (← `(tactic|
    refine ZkcFormal.Written.charged_pay_at _ _ $tableStx $placeStx (start := $startStx)
      (rest := $restStx) (key := $keyStx) _ _ _ _ $fee $set _
      (by simp [Zkc.Core.ROp.occurrence]) rfl ?weight ?within ?cap
      fun $reply $permitted $kept => ?_))
  let goals ← getGoals
  let left := goals.take (goals.length - others.length)
  let [weight, within, cap, after] := left
    | throwError "walk_pay: the rule of a paid draw left {left.length} goals, not four"
  let after ← readReply after reply.getId
  -- what the rule leaves beside the walk judges no process: it is stated of the values, with
  -- no variable of the walk. A goal that is true as it then stands is closed.
  let beside (goal : MVarId) : MetaM (Option MVarId) := do
    ZkcFormal.Walk.readValues (← ZkcFormal.Walk.useEquations goal)
  let weightLeft := (← beside weight).toList
  let closedBy (goal : MVarId) (tactic : TSyntax `tactic) : TacticM Bool := do
    let saved ← saveState
    try
      setGoals [goal]
      evalTactic tactic
      if (← getGoals).isEmpty then pure true else saved.restore; pure false
    catch _ =>
      saved.restore
      pure false
  -- the fee within the cap of the draw, compared first, so that a fee over the cap is refused
  -- with the name of its site also where it is over what is left of the budget: the
  -- applications of the frames are computed, so that no iteration is in what the kernel decides
  let capLeft ← match ← beside cap with
    | none => pure []
    | some cap => cap.withContext do
      let stated ← instantiateMVars (← cap.getType)
      let applications ← mkAppM ``Zkc.Core.Frame.applications #[rest]
      let computed ← Meta.reduce applications (skipTypes := true) (skipProofs := true)
      let stated := stated.replace fun e => if e == applications then some computed else none
      let cap ← cap.replaceTargetDefEq stated
      -- where the module states the cap of this site, the fee is compared with what it states,
      -- and the site has its name
      let mut cap := cap
      let mut stated := stated
      let mut site := m!"this draw"
      for name in ← Lean.labelled `walk_cap do
        let some (_, lhs, value) := (← inferType (mkConst name)).eq? | continue
        unless ← withReducible (isDefEq lhs stated.appArg!) do continue
        let narrowed := mkApp stated.appFn! value
        let next ← mkFreshExprSyntheticOpaqueMVar narrowed (← cap.getTag)
        cap.assign (← mkAppM ``LE.le.trans_eq #[next, ← mkEqSymm (mkConst name)])
        cap := next.mvarId!
        stated := narrowed
        site := m!"the draw `{lhs.appArg!}`"
        break
      if ← closedBy cap (← `(tactic| first | exact le_rfl | decide +kernel)) then pure []
      else
        -- refused where the kernel decides that the fee is over the cap; left to the text where
        -- it decides neither
        let over ← mkFreshExprSyntheticOpaqueMVar (mkNot stated)
        if ← closedBy over.mvarId! (← `(tactic| decide +kernel)) then
          throwError "walk_pay: the fee is not within the cap that the table gives {site}{indentExpr stated}"
        pure [cap]
  -- the fee within the budget: a hypothesis as it stands, or decided by the kernel where both
  -- sides are closed numbers; refused where the kernel decides that the fee is over what is
  -- left, and left to the text where it decides neither
  let withinLeft ← match ← beside within with
    | none => pure []
    | some within =>
      if (← observing? within.assumption).isSome then pure []
      else if ← closedBy within (← `(tactic| decide +kernel)) then pure []
      else
        within.withContext do
          let stated ← instantiateMVars (← within.getType)
          let over ← mkFreshExprSyntheticOpaqueMVar (mkNot stated)
          if ← closedBy over.mvarId! (← `(tactic| decide +kernel)) then
            throwError "walk_pay: the fee is not within what is left of the budget{indentExpr stated}"
          pure [within]
  setGoals (weightLeft ++ withinLeft ++ capLeft ++ [after] ++ others)

end ZkcFormal.Written
