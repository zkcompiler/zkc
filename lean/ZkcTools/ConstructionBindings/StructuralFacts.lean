module

public meta import ZkcTools.ConstructionBindings.Readback

public meta section

/-! Finite inverse proposals for the existing output/profile projections.
Candidates are ordinary data. Reflexivity of the original equation checks
them; these routines supply no new projection law or semantic assumption. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.StructuralFacts
open Lean Meta
open Zkc.Construction

/-- Reduce literal record projections before inspecting unknown operands.
Only constructor fields and beta redexes are exposed. In particular, this does
not unfold a layout, a source continuation or a semantic function. -/
def reduceRecordProjections (value : Expr) : MetaM Expr :=
  Core.transform value (pre := fun expression => do
    if !expression.hasExprMVar then return .done expression
    if expression.isHeadBetaTarget then return .visit expression.headBeta
    if let .proj _ index record := expression then
      if let some (.ctorInfo info) := (← getEnv).find? (record.getAppFn.constName?.getD .anonymous) then
        if let some field := record.getAppArgs[info.numParams + index]? then
          return .visit field
    if let .const name _ := expression.getAppFn then
      if let some info ← getProjectionFnInfo? name then
        let arguments := expression.getAppArgs
        if let some record := arguments[info.numParams]? then
          if record.isAppOf info.ctorName then
            if let some (.ctorInfo constructor) := (← getEnv).find? info.ctorName then
              if let some field := record.getAppArgs[constructor.numParams + info.i]? then
                return .visit (mkAppN field (arguments.extract (info.numParams + 1) arguments.size))
    return .continue)

private partial def entries (value : Expr) : MetaM (Array Expr) := do
  let value ← whnf value
  if value.isAppOf ``List.nil then return #[]
  unless value.isAppOf ``List.cons do throwError "connection-structural-row-undetermined"
  return #[value.getAppArgs[1]!] ++ (← entries value.getAppArgs[2]!)

/-- Invert the finite optional-input projection during syntax matching. Lean
unification does not invent a `Subject` constructor for `Subject.comp ?subject`.
The candidate is subsequently checked by conversion of the original equation. -/
private def proposeSubject (projected actual : Expr) : MetaM Bool := do
  unless projected.isAppOf ``Zkc.Source.Structured.NormalForm.Subject.comp do return false
  let subject ← instantiateMVars projected.getAppArgs.back!
  unless subject.isMVar do return false
  let actual ← whnf actual
  let args := actual.getAppArgs
  let candidate ← if actual.isAppOf ``Zkc.Source.Structured.NormalForm.Comp.input then
      mkAppM ``Zkc.Source.Structured.NormalForm.Subject.input #[args.back!]
    else if actual.isAppOf ``Zkc.Source.Structured.NormalForm.Comp.read then
      mkAppM ``Zkc.Source.Structured.NormalForm.Subject.read #[args[args.size - 2]!, args.back!]
    else return false
  isDefEq subject candidate

private partial def matchSyntax (left right : Expr) (fuel : Nat) : MetaM Unit := do
  if fuel == 0 then throwError "connection-structural-syntax-fuel"
  let left ← instantiateMVars left
  let right ← instantiateMVars right
  if left == right then return
  -- Closed subtrees contain no operands to infer. The final reflexivity
  -- check validates them together with the complete original equation.
  if !left.hasExprMVar && !right.hasExprMVar then return
  if (← proposeSubject left right) || (← proposeSubject right left) then return
  let left ← whnf left
  let right ← whnf right
  if left == right then return
  if left.getAppFn == right.getAppFn && left.getAppNumArgs == right.getAppNumArgs then
    if let some name := left.getAppFn.constName? then
      if let some (.ctorInfo info) := (← getEnv).find? name then
        for index in [info.numParams:left.getAppNumArgs] do
          matchSyntax left.getAppArgs[index]! right.getAppArgs[index]! (fuel - 1)
        return
  unless ← isDefEq left right do throwError "connection-structural-syntax-undetermined"

/-- Match only finite source syntax. Constructor proposals carry no proof
authority: reflexivity still checks the complete fixed equation, and failure
rolls back every inferred operand. -/
def proposeSourceEquality (goal : MVarId) : MetaM Bool := goal.withContext do
  let saved ← saveState
  try
    let target ← instantiateMVars (← goal.getType)
    unless target.isAppOf ``Eq && target.hasExprMVar do return false
    let type ← whnf target.getAppArgs[0]!
    unless type.isAppOf ``Zkc.Source.Structured.NormalForm.Form ||
        (type.isAppOf ``Except && type.getAppArgs.back!.isAppOf ``Zkc.Source.Structured.NormalForm.Form) do
      return false
    matchSyntax target.getAppArgs[1]! target.getAppArgs[2]! 4096
    goal.refl
    return true
  catch error =>
    saved.restore
    if error.isRuntime || error.isInterrupt then throw error
    return false

private def proposeCore (goal : MVarId) (sourceSyntax : Bool) : MetaM Bool := goal.withContext do
  if sourceSyntax then
    if ← proposeSourceEquality goal then return true
  -- Size equations can mention unresolved cells whose contents are irrelevant
  -- to the size. Prove them from length laws before ordinary conversion tries
  -- to inspect those cells through dependent layout constructors.
  if (← instantiateMVars (← goal.getType)).hasExprMVar then
    if ← LayoutLookup.proposeLengthEquality goal then return true
  if ← LayoutLookup.propose goal then return true
  if ← LayoutLookup.inferIndex goal then return true
  let type ← whnf (← instantiateMVars (← goal.getType))
  unless type.isAppOf ``Eq do return false
  let left := type.getAppArgs[1]!
  unless left.isAppOf ``Original.profileReferences || left.isAppOf ``Original.outputReferences do
    return false
  let right ← whnf type.getAppArgs[2]!
  unless right.isAppOf ``Option.some do return false
  let result := right.getAppArgs.back!
  if result.hasExprMVar then return false
  if left.isAppOf ``Original.profileReferences then
    let args := left.getAppArgs
    let profile ← whnf (← mkAppM ``Context.profile #[args[0]!])
    let row ← entries result
    let (data, history) ← if profile.isAppOf ``Profile.plain then
        pure (row, ← mkAppOptM ``Option.none #[some (mkConst ``Nat)])
      else if profile.isAppOf ``Profile.fiatShamir && !row.isEmpty then
        pure (row.extract 0 (row.size - 1), ← mkAppM ``Option.some #[row.back!])
      else throwError "connection-structural-profile-row"
    unless ← isDefEq args[1]! (← mkListLit (mkConst ``Nat) data.toList) do return false
    unless ← isDefEq args[2]! history do return false
    goal.refl
    return true
  if left.isAppOf ``Original.outputReferences then
    let args := left.getAppArgs
    let scopes ← entries args[1]!
    let row ← entries result
    let mut offset := 0
    let mut locations := #[]
    for scope in scopes do
      let contains ← mkAppM ``List.contains #[scope, args[0]!]
      let contains ← whnf contains
      unless contains.isConstOf ``Bool.true || contains.isConstOf ``Bool.false do
        throwError "connection-structural-visibility-undetermined"
      let visible := contains.isConstOf ``Bool.true
      if visible then
        let some reference := row[offset]? | throwError "connection-structural-visible-row"
        locations := locations.push (← mkAppM ``Original.Location.data #[reference])
        offset := offset + 1
      else locations := locations.push (mkConst ``Original.Location.absent)
    unless offset == row.size do throwError "connection-structural-output-row"
    unless ← isDefEq args[2]! (← mkListLit (mkConst ``Original.Location) locations.toList) do return false
    goal.refl
    return true
  return false

/-- A refused projection must not leave partial data inference behind. This
boundary also covers callers collecting a reusable family's finite premises.
Discovery can defer source equations until application fixes their operands. -/
def propose (goal : MVarId) (sourceSyntax : Bool := true) : MetaM Bool := do
  let saved ← saveState
  try
    let accepted ← proposeCore goal sourceSyntax
    unless accepted do saved.restore
    return accepted
  catch error =>
    saved.restore
    throw error

end ZkcTools.ConstructionBindings.StructuralFacts
