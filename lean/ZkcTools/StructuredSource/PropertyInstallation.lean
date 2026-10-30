module

public import Zkc.Source.Structured.Template
public meta import Lean.Elab.Tactic

public meta section

/-! Install a mathematical presentation through the existing exact source
association. The association fixes the full signature and raw typed body;
this proposer supplies no source equation, property premise or target placement.
Unresolved body laws and applicability conditions remain ordinary goals. -/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.PropertyInstallation
open Lean Meta Elab Tactic

/-- The selected input pattern is source-owned data. The library theorem
infers the actual role, context, arguments, captures and complete reference
from the goal, retaining every reply, stop and masked output. Only structural
visibility and scope checks are computed; mathematics stays with the author. -/
elab "install_source_template " association:term " using_pattern " pattern:term : tactic =>
  Term.withoutErrToSorry <| withoutRecover do
    evalTactic (← `(tactic| apply Zkc.Source.Structured.Template.Association.invoke
      $association (pattern := $pattern)))
    let mut remaining := []
    for goal in ← getGoals do
      setGoals [goal]
      let saved ← saveState
      try
        evalTactic (← `(tactic| assumption))
      catch error =>
        if error.isRuntime || error.isInterrupt then throw error
        saved.restore
        goal.withContext do
          let target := (← instantiateMVars (← goal.getType)).headBeta.consumeMData
          if let some (_, lhs, _) := target.eq? then
            let lhs := lhs.headBeta.consumeMData
            if lhs.isAppOf ``Zkc.Source.Structured.InputVisibility.patternVisible ||
                lhs.isAppOf ``Zkc.Source.Structured.InputVisibility.scopesBounded then
              evalTactic (← `(tactic| try (first | rfl | (solve | decide +kernel))))
      unless ← goal.isAssigned do remaining := remaining ++ [goal]
    setGoals remaining

end ZkcTools.StructuredSource.PropertyInstallation
