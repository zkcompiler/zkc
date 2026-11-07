module

public meta import Zkc.Source.DeriveRegion
public meta import Zkc.Semantics.HandlerReturn

public meta section

/-! Judgment-directed installation of local semantic facts. This module
selects facts, not source instructions, and constructs only kernel-checked
applications of the supplied theorems. -/

namespace Zkc.Source
open Lean Meta Elab Tactic

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
      let (_, _, conclusion) ← forallMetaTelescope (← inferType value)
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
      unless ← isDefEq conclusion target do
        saved.restore
        continue
      let goals ← goal.apply value { newGoals := .nonDependentOnly }
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
