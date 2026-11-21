module

public import Zkc.Formal.Walk
public import Zkc.Formal.Written.SiteCaps
public meta import Lean

public meta section
open Lean Meta Elab Tactic

/-!
What a text says at an effect, under the judgment with fees.

A walk stops where the goal is the judgment at an effect. Under the judgment with fees within
the allowances of a table of caps, a text says one of two things there.

- `walk_free as v`: nothing is excluded and no fee is paid. The reply is `v`, and
  `permitted_v` says that it is a permitted reply. A message got or a value heard has no
  sampler and can only be met this way; a text names the reply here, since it is the reply
  that a later excluded set speaks of.
- `walk_pay fee excluding set as v kept`: a coin of the role pays `fee` for the replies in
  `set`. The tactic reads from the goal what the program and the table determine: the table and
  the path at which the run started, from the judgment; where the effect occurs, from the
  effect; the sampler of the coin's law. It leaves, in this order, what the text has to say:
  `weight`, that the sampler draws a reply of the set with probability at most the fee; `within`,
  that the fee is within the budget, unless it is a hypothesis as it stands; `cap`, that the fee
  is within the cap that the table gives the draw, unless the kernel decides it; and the rest
  of the walk after a reply `v` outside the set, with `permitted_v` and `kept : ¬ set v`.

Both apply a rule of `Zkc.Formal.Written.SiteCaps` (`charged_free`, `charged_pay_at`) and
nothing else: what they leave is what the rule asks.
-/

namespace Zkc.Formal.Written

/-- The judgment at an effect that a goal is: the arguments of the judgment and the effect. -/
private def atEffect (goal : MVarId) (who : String) : MetaM (Array Expr × Expr) := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).consumeMData.headBeta
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Zkc.Core.Process.interpret && args.size ≥ 9 &&
      args[7]!.isAppOfArity ``Zkc.Core.Process.call 5 do
    throwError "{who}: the goal is not the judgment at an effect; walk to one first{indentExpr target}"
  return (args, args[7]!.getArg! 3)

/-- The reply that a tactic introduced, at its computed type, so that a text reads it as a
value. -/
private def readReply (goal : MVarId) (reply : Lean.Name) : MetaM MVarId := goal.withContext do
  let some decl := (← getLCtx).findFromUserName? reply | return goal
  goal.replaceLocalDeclDefEq decl.fvarId (← whnfD decl.type)

/-- The name of the hypothesis that a reply is permitted. -/
private def permittedName (reply : TSyntax `ident) : TSyntax `ident :=
  mkIdentFrom reply (Name.mkSimple s!"permitted_{reply.getId}")

/-- At an effect, nothing is excluded and no fee is paid: the reply is `v`, and `permitted_v`
says that it is permitted. -/
elab "walk_free" " as " reply:ident : tactic => do
  let _ ← atEffect (← getMainGoal) "walk_free"
  let permitted := permittedName reply
  evalTactic (← `(tactic|
    refine Zkc.Formal.Written.charged_free _ _ _ _ _ _ fun $reply $permitted => ?_))
  replaceMainGoal [← readReply (← getMainGoal) reply.getId]

/-- The parts of a path after its start, where the path is the start with lists appended. -/
private partial def afterStart (path start : Expr) : MetaM (Option (List Expr)) := do
  if ← withReducible (isDefEq path start) then return some []
  if path.isAppOfArity ``HAppend.hAppend 6 then
    if let some before ← afterStart (path.getArg! 4) start then
      return some (before ++ [path.getArg! 5])
  return none

/-- At a coin, pay `fee` for the replies in `set`: see the header of this module. -/
elab "walk_pay " fee:term:max " excluding " set:term:max " as " reply:ident kept:ident : tactic =>
    withMainContext do
  let goal ← getMainGoal
  let (args, op) ← atEffect goal "walk_pay"
  -- the table, the use at which the run started and its path, from the judgment
  let judgment := args[4]!
  let pays := judgment.appArg!
  unless judgment.isAppOf ``Zkc.Core.ProcessJudgment.charged &&
      pays.isAppOf ``Zkc.Formal.ProbabilisticProcess.paysWithin do
    throwError "walk_pay: the judgment is not the one with fees within allowances{indentExpr judgment}"
  let allowance := pays.appArg!
  let a := allowance.getAppArgs
  let (model, table, place, start) ←
    if allowance.isAppOfArity ``Zkc.Frontend.Written.CapTable.allowance 4 then
      pure (a[1]!, a[2]!, ← mkAppM ``Zkc.Frontend.Written.CapTable.root #[a[2]!], a[3]!)
    else if allowance.isAppOfArity ``Zkc.Frontend.Written.CapTable.allowanceFrom 5 then
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
  evalTactic (← `(tactic|
    refine Zkc.Formal.Written.charged_pay_at _ _ $tableStx $placeStx (start := $startStx)
      (rest := $restStx) (key := $keyStx) _ _ _ _ $fee $set _
      (by simp [Zkc.Core.ROp.occurrence]) rfl ?weight ?within ?cap
      fun $reply $permitted $kept => ?_))
  let goals ← getGoals
  let [weight, within, cap, after] := goals
    | throwError "walk_pay: the rule of a paid draw left {goals.length} goals, not four"
  let after ← readReply after reply.getId
  -- the fee within the budget, where it is a hypothesis as it stands
  let withinLeft := if (← observing? within.assumption).isSome then [] else [within]
  -- the fee within the cap of the draw: the applications of the frames are computed, so that
  -- no iteration is in what the kernel decides
  let capLeft ← cap.withContext do
    let stated ← instantiateMVars (← cap.getType)
    let applications ← mkAppM ``Zkc.Core.Frame.applications #[rest]
    let computed ← Meta.reduce applications (skipTypes := true) (skipProofs := true)
    let stated := stated.replace fun e => if e == applications then some computed else none
    let cap ← cap.replaceTargetDefEq stated
    let saved ← saveState
    try
      setGoals [cap]
      evalTactic (← `(tactic| decide +kernel))
      pure []
    catch _ =>
      saved.restore
      if stated.hasFVar then pure [cap]
      else throwError "walk_pay: the fee is not within the cap that the table gives this draw{indentExpr stated}"
  setGoals ([weight] ++ withinLeft ++ capLeft ++ [after])

end Zkc.Formal.Written
