module

public import Zkc.Source.Structured.Import
public import Zkc.Construction.ReferenceBinding
public import Zkc.Source.Structured.BodyBindings
public meta import Lean.Elab.Tactic

@[expose] public meta section

/-! Apply installed mathematical body laws to the actual admitted table.
The untrusted elaborator finds an exact typed-body association and emits the
ordinary reference theorem. Remaining premises are ordinary Lean goals; the
matcher never turns them into assumptions or changes the requested result.
-/
namespace ZkcTools.StructuredSource.ReferenceLaws
open Lean Meta Elab Tactic

/-- An invocation premise is a separate dependency proof, not a finite ABI
normalization. Avoid silently unfolding an entire linked table with `rfl`. -/
def helperEquation (type : Expr) : Bool :=
  match type.eq? with
  | some (_, actual, _) => actual.isAppOfArity ``Zkc.Source.Structured.invoke 5 ||
      actual.isAppOfArity ``Zkc.Construction.Domain.callHelper 5
  | none => false

/-- Search proposes the actual declaration selected by the call's name. The
kernel subsequently checks its complete signature, body and input decoding. -/
partial def findHelper (definitions name : Expr) : MetaM Expr := do
  let cell ← whnf definitions
  unless cell.isAppOfArity ``List.cons 3 do
    throwError "apply_helper_reference: no linked helper has the requested name"
  let signature ← mkAppM ``Zkc.Source.Structured.CheckedDefinition.helper #[cell.getAppArgs[1]!]
  let actualName ← mkAppM ``Zkc.Source.Structured.Helper.name #[signature]
  if ← withoutModifyingState <| isDefEq actualName name then return signature
  findHelper cell.getAppArgs[2]! name

elab "apply_helper_reference " law:term " using " program:term : tactic =>
  withMainContext <| withoutRecover do
    let goal ← getMainGoal
    let target ← whnf (← instantiateMVars (← goal.getType))
    if target.hasExprMVar then
      throwError "apply_helper_reference requires the invocation and complete reference to be fixed before law selection"
    let some (_, actual, _) := target.eq? |
      throwError "apply_helper_reference expects an exact helper outcome equation"
    let compiled := actual.isAppOfArity ``Zkc.Construction.Domain.callHelper 5
    unless compiled || actual.isAppOfArity ``Zkc.Source.Structured.invoke 5 do
      throwError "apply_helper_reference expects an actual typed or constructed helper invocation on the left"
    let lawExpr ← Term.elabTerm law none
    let lawType ← whnf (← inferType lawExpr)
    unless lawType.isAppOfArity ``Zkc.Source.Structured.ReferenceLaw 3 do
      throwError "apply_helper_reference requires an installed typed ReferenceLaw"
    let source ← Term.elabTerm program none
    let payload ← mkAppM ``Zkc.Source.Structured.Program.payload #[source]
    let definitions ← mkAppM ``Zkc.Source.Structured.UnitPayload.definitions #[payload]
    let linked ← mkAppM ``Zkc.Source.Structured.UnitPayload.linked #[payload]
    let rule ← if compiled then do
        let helper ← findHelper definitions actual.getAppArgs[2]!
        let inputs ← mkAppM ``Zkc.Source.Structured.Helper.inputs #[helper]
        let decoded ← whnf (← mkAppM ``Zkc.Construction.Domain.decodeValues
          #[inputs, actual.getAppArgs[4]!])
        unless decoded.isAppOfArity ``Option.some 2 do
          throwError "apply_helper_reference: the actual nominal argument encoding does not decode"
        pure <| mkAppN (← mkConstWithFreshMVarLevels ``Zkc.Construction.Domain.Binding.callHelper_of_reference)
          #[lawType.getAppArgs[0]!, source, helper, lawExpr, decoded.getAppArgs[1]!, actual.getAppArgs[4]!]
      else
        pure <| mkAppN (← mkConstWithFreshMVarLevels ``Zkc.Source.Structured.ReferenceLaw.invoke)
          #[lawType.getAppArgs[0]!, actual.getAppArgs[3]!, lawExpr, definitions, linked]
    let pending := (← getGoals).tail
    setGoals (← goal.apply rule { newGoals := .all })
    let mut remaining : List MVarId := []
    for goal in ← getGoals do
      unless ← goal.isAssigned do
        let type ← instantiateMVars (← goal.getType)
        setGoals [goal]
        if type.isAppOf ``Zkc.Source.Structured.BodyIn then
          evalTactic (← `(tactic| bind_structured_bodies))
        else
          -- Keep semantic dependency proofs separate from finite encodings.
          unless helperEquation (← whnf type) do
            evalTactic (← `(tactic| first | exact True.intro | rfl | skip))
          remaining := remaining ++ (← getGoals)
    setGoals (remaining ++ pending)

/-- Bounded search is a convenience over the same checked application rule.
A missing dependency or mathematical premise stays an ordinary goal. Search
failure restores its metavariables before trying another installed law. -/
partial def applyLibrary (laws : Array (TSyntax `term)) (program : TSyntax `term)
    (fuel : Nat) (goal : MVarId) : TacticM (List MVarId) := goal.withContext do
  if fuel == 0 then return [goal]
  let target ← whnf (← instantiateMVars (← goal.getType))
  unless helperEquation target do return [goal]
  let saved ← saveState
  for law in laws do
    saved.restore
    try
      setGoals [goal]
      evalTactic (← `(tactic| apply_helper_reference $law using $program))
      let obligations ← getGoals
      let mut remaining : List MVarId := []
      for obligation in obligations do
        unless ← obligation.isAssigned do
          remaining := remaining ++ (← applyLibrary laws program (fuel - 1) obligation)
      return remaining
    catch error =>
      if error.isRuntime || error.isInterrupt then throw error
  saved.restore
  return [goal]

/-- Install a finite catalogue, including laws of dependencies. No declaration
name selects a formula, and the proposed reference never changes the goal. -/
elab "derive_helper_reference " "[" laws:term,* "]" " using " program:term : tactic =>
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    if (← instantiateMVars (← getMainTarget)).hasExprMVar then
      throwError "derive_helper_reference requires the invocation and complete reference to be fixed before law selection"
    let pending := (← getGoals).tail
    let remaining ← applyLibrary laws.getElems program 64 (← getMainGoal)
    setGoals (remaining ++ pending)

end ZkcTools.StructuredSource.ReferenceLaws
