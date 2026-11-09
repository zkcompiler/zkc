module

public import Zkc.Tools.IR.StructuredSource.ReferenceLaws
public import Zkc.IR.Source.Structured.CollectionReference

public meta section

/-! Selection is finite checked syntax work. It supplies only exact body
associations; dependency equations and mathematics are separate obligations. -/
namespace ZkcTools.StructuredSource

macro "select_reference_bodies" : tactic =>
  `(tactic| focus (constructor <;> bind_structured_bodies))

namespace ReferenceInstallation
open Lean Meta Elab Tactic Zkc.Source Zkc.Source.Structured

/-- Flatten only supplied proof records. Each projection remains a checked
proof term; neither source names nor unproved fields enter the fact set. -/
private def proofFields (proof : Expr) : Nat → MetaM (Array Expr)
  | 0 => pure #[proof]
  | fuel + 1 => do
    let type ← inferType proof
    unless ← isProp type do return #[]
    let some name := type.getAppFn.constName? | return #[proof]
    if name == ``BodyIn || name == ``ReferenceLaw.Realizes then return #[proof]
    let some info := getStructureInfo? (← getEnv) name | return #[proof]
    let mut facts := #[proof]
    for index in [:info.fieldNames.size] do
      facts := facts ++ (← proofFields (mkProj name index proof) fuel)
    return facts

/-- Apply only existing facts. A failed attempt restores all metavariables;
resource exceptions propagate. In particular an invocation is never executed
by reflexivity while trying to establish its dependency law. -/
private def fromFacts (goal : MVarId) (facts : Array Expr) : MetaM Bool := do
  for proof in facts do
    let saved ← saveState
    try
      let pending ← goal.apply proof
      if ← pending.allM (·.isAssigned) then return true
    catch error =>
      if error.isRuntime || error.isInterrupt then throw error
    saved.restore
  return false

/-- Structural premises are universal ABI arguments, conjunctions and True.
Mathematical premises remain ordinary goals unless a supplied fact proves them. -/
private def discharge (goal : MVarId) (facts : Array Expr) : Nat → MetaM (List MVarId)
  | 0 => pure [goal]
  | fuel + 1 => goal.withContext do
    if ← fromFacts goal facts then return []
    let type ← whnf (← goal.getType)
    if type.isConstOf ``True then
      goal.assign (mkConst ``True.intro)
      return []
    if type.isForall then
      let (argument, next) ← goal.intro1
      return ← next.withContext do
        let argumentType ← whnf (← inferType (mkFVar argument))
        if argumentType.isAppOf ``Values then
          let cases ← next.cases argument
          return (← cases.toList.mapM fun branch => discharge branch.mvarId facts fuel).flatten
        discharge next facts fuel
    if type.isAppOf ``And then
      return (← (← goal.constructor).mapM fun field => discharge field facts fuel).flatten
    -- A heterogeneous tuple introduced by `cases` may retain a tail. Split
    -- only such finite tuples; never induct on program states or mathematics.
    for declaration in ← getLCtx do
      unless declaration.isImplementationDetail do
        let localType ← whnf declaration.type
        if localType.isAppOf ``Values then
          let cases ← goal.cases declaration.fvarId
          return (← cases.toList.mapM fun branch => discharge branch.mvarId facts fuel).flatten
    return [goal]

private def install (goal : MVarId) (definitions linked : Expr)
    (facts : Array Expr) : MetaM (List MVarId) := goal.withContext do
  let type := (← instantiateMVars (← goal.getType)).headBeta
  unless type.isAppOf ``ReferenceLaw.Realizes do
    throwError "install_reference_laws expects a ReferenceLaw.Realizes field"
  let arguments := type.getAppArgs
  let rule ← mkAppOptM ``ReferenceLaw.realizes
    #[some arguments[0]!, some arguments[1]!, some arguments[2]!,
      some definitions, some linked]
  let obligations ← goal.apply rule
  return (← obligations.mapM fun obligation => discharge obligation facts 128).flatten

/-- Keep each installed proof in one enclosing `have`. Subsequent fields
refer to that local constant instead of embedding its derivation again. The
completed prefix is reused directly when the local context grows. Earlier
fields are never searched or installed again. -/
private def installRecord (root : MVarId) (definitions linked : Expr)
    (facts : Array Expr) (completed : Array Expr := #[]) : Nat → MetaM (List MVarId)
  | 0 => pure [root]
  | fuel + 1 => root.withContext do
    let candidate ← mkFreshExprSyntheticOpaqueMVar (← root.getType)
    let fields ← candidate.mvarId!.constructor
    let mut remaining := []
    let mut installedPrefix := completed
    for (field, index) in fields.zipIdx do
      if let some proof := completed[index]? then
        field.assign proof
      else if ← fromFacts field facts then
        if remaining.isEmpty then
          installedPrefix := installedPrefix.push (← instantiateMVars (mkMVar field))
      else
        let obligations ← install field definitions linked facts
        if obligations.isEmpty && remaining.isEmpty then
          let proof ← instantiateMVars (mkMVar field)
          unless proof.hasExprMVar do
            let type ← instantiateMVars (← field.getType)
            let next ← root.assert (← mkFreshUserName `installed) type proof
            let (name, next) ← next.intro1
            return ← installRecord next definitions linked (facts.push (mkFVar name))
              (installedPrefix.push (mkFVar name)) fuel
        remaining := remaining ++ obligations
    root.assign (← instantiateMVars candidate)
    return remaining

/-- Install exact body laws in dependency order. Missing mathematics stays
open and is never added to the usable fact set. Named proof sharing prevents
rechecking a recursively duplicated dependency derivation at every use. -/
elab "install_reference_laws " "using " linked:term " with " bodies:term : tactic =>
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let linked ← Term.elabTerm linked none
    let linkedType ← whnf (← inferType linked)
    unless linkedType.isAppOf ``DeclarationsLinked do
      throwError "install_reference_laws requires linked source declarations"
    let definitions := linkedType.getAppArgs.back!
    let bodies ← Term.elabTerm bodies none
    let facts ← proofFields bodies 16
    let root ← getMainGoal
    let following := (← getGoals).tail
    let type := (← instantiateMVars (← root.getType)).headBeta
    let remaining ← if type.isAppOf ``ReferenceLaw.Realizes then
      install root definitions linked facts
      else installRecord root definitions linked facts #[] 128
    setGoals (remaining ++ following)

end ReferenceInstallation

end ZkcTools.StructuredSource
