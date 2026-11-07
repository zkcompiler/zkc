module

public meta import Zkc.Source.DeriveRegion
public meta import Zkc.Semantics.HandlerReturn
public meta import Zkc.Source.Component

public meta section

/-! Judgment-directed installation of local semantic facts. This module
selects facts, not source instructions, and constructs only kernel-checked
applications of the supplied theorems. -/

namespace Zkc.Source
open Lean Meta Elab Tactic

/-- Expose only the component wrapper on an explicit typed tuple. The equation
compiler's dependent casts can block `present` while fact parameters are unknown.
This is an input-matching aid; the original law is checked again after matching.
Mathematical payloads and unknown caller tuples stay opaque. -/
private meta partial def exposePresent (expression : Expr) : MetaM Expr := do
  unless expression.isAppOf ``Values.present do return expression
  let tuple ← whnf expression.getAppArgs.back!
  let fields := tuple.getAppArgs
  if tuple.isAppOf ``Values.nil then
    return mkAppN tuple.getAppFn
      (fields.set! 1 (← mkAppM ``Component #[fields[1]!]))
  unless tuple.isAppOf ``Values.cons do return expression
  let head ← mkAppM ``Option.some #[fields[fields.size - 2]!]
  let tail ← exposePresent (← mkAppM ``Values.present #[fields.back!])
  let fields := fields.set! 1 (← mkAppM ``Component #[fields[1]!])
  return mkAppN tuple.getAppFn
    ((fields.set! (fields.size - 2) head).set! (fields.size - 1) tail)

/-- Choose a supplied fact by its proposition before attempting unification.
Filter unrelated judgments and request identities before semantic unification.
Premises still use Lean's standard bounded elimination search; malformed fact
terms and resource failures remain errors. -/
elab "source_facts" "[" facts:term,* "]" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← withReducible <| whnf (← instantiateMVars (← goal.getType))
  for fact in facts.getElems do
    let saved ← saveState
    let value ← Term.withoutErrToSorry <| Term.elabTerm fact none
    try
      let (parameters, _, conclusion) ← forallMetaTelescope (← inferType value)
      let conclusion ← withReducible <| whnf conclusion
      unless conclusion.getAppFn.constName? == target.getAppFn.constName? do
        saved.restore
        continue
      if target.isAppOf ``RegionMeaning.OperationLaw then
        let expected := target.getAppArgs
        let offered := conclusion.getAppArgs
        unless ← isDefEq expected[expected.size - 4]! offered[offered.size - 4]! do
          saved.restore
          continue
      if target.isAppOf ``PIR.Process.ReturnsUnder then
        let expected := target.getAppArgs
        let offered := conclusion.getAppArgs
        let expectedProcess ← whnf expected[expected.size - 2]!
        let offeredProcess ← whnf offered[offered.size - 2]!
        if expectedProcess.isAppOf ``PIR.Process.call && offeredProcess.isAppOf ``PIR.Process.call then
          let expectedRequest := expectedProcess.getAppArgs
          let offeredRequest := offeredProcess.getAppArgs
          unless ← isDefEq expectedRequest[expectedRequest.size - 2]!
              offeredRequest[offeredRequest.size - 2]! do
            saved.restore
            continue
      if target.isAppOf ``Eq then
        let wanted := target.getAppArgs.back!
        let supplied := conclusion.getAppArgs.back!
        if wanted.isAppOf ``ite &&
            (supplied.isAppOf ``PIR.Process.done || supplied.isAppOf ``PIR.Process.halt) then
          saved.restore
          continue
      let expanded ← Meta.transform conclusion (pre := fun expression => do
        if expression.isAppOf ``Values.present then
          return .done (← exposePresent expression)
        return .continue)
      unless ← isDefEq expanded target do
        saved.restore
        continue
      unless ← isDefEq conclusion target do
        saved.restore
        continue
      let proof ← instantiateMVars (mkAppN value parameters)
      -- Keep unresolved values dependent on their association premises. Lean's
      -- ordinary application ordering then solves those premises first.
      let abstracted ← abstractMVars proof (levels := false)
      let goals ← goal.apply abstracted.expr { newGoals := .nonDependentOnly }
      let [] ← Lean.Elab.Tactic.SolveByElim.processSyntax
          { maxDepth := 3, exfalso := false, constructor := false, intro := false }
          true false ([← `(rfl), ← `(trivial)] ++ facts.getElems.toList) [] #[] goals
        | throwError "source fact has unresolved premises"
      replaceMainGoal []
      return
    catch error =>
      DeriveRegion.rethrowResourceFailure error
      if let .internal .. := error then throw error
      saved.restore
  throwError "no supplied fact proves this source operation"

end Zkc.Source
