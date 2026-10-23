module

public import Zkc.Source.Structured.Association
public meta import Lean.Elab.Tactic

@[expose] public section

/-! Proof-producing association with installed typed helper bodies.

The expected helper and body come from the goal. Search reads only the actual
definition list; full signature and raw-tree equality authorize a match. The
result is an ordinary `BodyIn.of_mem` proof, independent of declaration order.
-/

namespace Zkc.Source.Structured

open Lean Meta Elab Tactic

/-- Extend an exact association by an unrelated declaration. -/
theorem BodyIn.cons {definitions : List CheckedDefinition} {helper : Helper}
    {body : Region dialect helper.inputs helper.outputs}
    (head : CheckedDefinition) (association : BodyIn definitions helper body) :
    BodyIn (head :: definitions) helper body := by
  obtain ⟨definition, member, signature, exactRaw⟩ := association
  exact BodyIn.of_mem (List.mem_cons_of_mem head member) signature exactRaw

/-- Search a concrete list, constructing membership only after both exact
checks succeed. No equality decision procedure or semantic replacement is used. -/
private meta partial def findBody (definitions helper body : Expr) : MetaM Expr := do
  let erased ← mkAppM ``Region.erase #[body]
  let rec visit (remaining : Expr) : MetaM Expr := do
    let cell ← whnf remaining
    unless cell.isAppOfArity ``List.cons 3 do
      if cell.isAppOfArity ``List.nil 1 then
        throwError "bind_structured_bodies: no actual definition matches the complete helper signature and body for {helper}"
      throwError "bind_structured_bodies: expected a concrete checked definition list"
    let args := cell.getAppArgs
    let definition := args[1]!
    let tail := args[2]!
    let signature ← mkAppM ``CheckedDefinition.helper #[definition]
    let raw ← mkAppM ``CheckedDefinition.raw #[definition]
    let exactMatch ← withoutModifyingState do
      return (← isDefEq signature helper) && (← isDefEq raw erased)
    if exactMatch then
      let member ← mkAppOptM ``List.mem_cons_self #[none, some definition, some tail]
      return ← mkAppM ``BodyIn.of_mem #[member, ← mkEqRefl signature, ← mkEqRefl raw]
    let association ← visit tail
    -- Recover the matching witness from the tail proof without inspecting its
    -- mathematical interpretation, then extend its membership by one cell.
    return ← mkAppM ``BodyIn.cons #[definition, association]
  let proof ← visit definitions
  return proof

/-- Construct only nonempty proposition structures ending in exact body
associations. General propositions, empty structures and data fields are refused. -/
private meta partial def bindBodies (goal : MVarId) : MetaM Unit := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  if target.isAppOfArity ``BodyIn 3 then
    let args := target.getAppArgs
    unless !(← instantiateMVars args[1]!).hasExprMVar &&
        !(← instantiateMVars args[2]!).hasExprMVar do
      throwError "bind_structured_bodies: helper and body templates must be determined"
    let proof ← findBody args[0]! args[1]! args[2]!
    goal.assign proof
    return
  unless ← isProp target do
    throwError "bind_structured_bodies: expected BodyIn or a nonempty record of body associations"
  let some name := target.getAppFn.constName?
    | throwError "bind_structured_bodies: unsupported goal {target}"
  let some info := getStructureInfo? (← getEnv) name
    | throwError "bind_structured_bodies: unsupported proposition {target}"
  if info.fieldNames.isEmpty then
    throwError "bind_structured_bodies: empty proposition records are not body associations"
  let fields ← goal.constructor
  if fields.isEmpty then
    throwError "bind_structured_bodies: record has no body association fields"
  for field in fields do
    bindBodies field

/-- Bind installed body templates to members of the actual checked definition
list, recursively assembling records of these exact associations. -/
elab "bind_structured_bodies" : tactic => do
  let goal ← getMainGoal
  bindBodies goal
  replaceMainGoal []

end Zkc.Source.Structured
