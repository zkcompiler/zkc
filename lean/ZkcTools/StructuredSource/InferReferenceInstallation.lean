module

public import Zkc.Source.Structured.BodyBindings
public meta import Lean.Elab.Tactic
public meta import Lean.Meta.CollectMVars

public meta section

/-! Infer finite library bindings by exact typed-body matching.
The caller selects the mathematical library's association record. Search only
fills its data witness and proves those associations; it supplies no reference
formula, dependency equation or mathematical premise. Backtracking across the
whole record prevents an early ambiguous helper from fixing the wrong chain.
Selection constructs one valid library witness; it does not choose a security
method or a component occurrence. Callers fix those through their request.
A universal model binder makes the selected names independent of the model.
-/
set_option autoImplicit false
namespace ZkcTools.StructuredSource.InferReferenceInstallation
open Lean Meta Elab Tactic Zkc.Source.Structured Zkc.Source

initialize registerTraceClass `zkc.referenceBindings

/-- Constructor fields remain ordinary metavariables until exact body matching
fixes them. Only non-recursive records are expanded, with a finite depth bound. -/
private def unresolved (goal : MVarId) (type : Expr) : MetaM (List MVarId) := do
  let value ← mkFreshExprMVar type
  goal.assign value
  return [value.mvarId!]

private def witness (goal : MVarId) : Nat → MetaM (List MVarId)
  | 0 => throwError "reference-binding-record-depth"
  | fuel + 1 => goal.withContext do
    let type ← instantiateMVars (← goal.getType)
    if type.isConstOf ``String || type.isConstOf ``Nat || type.isConstOf ``Bool then
      return ← unresolved goal type
    let some name := type.getAppFn.constName? | return ← unresolved goal type
    let some _ := getStructureInfo? (← getEnv) name | return ← unresolved goal type
    let fields ← goal.constructor
    let mut remaining := []
    for field in fields do
      remaining := remaining ++ (← witness field fuel)
    return remaining

/-- Flatten association records before searching. This exposes the complete
constraint set, including associations inherited from other library records. -/
private partial def associations (goal : MVarId) : TacticM (List MVarId) := goal.withContext do
  let target := (← instantiateMVars (← goal.getType)).headBeta
  if target.isAppOfArity ``BodyIn 3 then return [goal]
  if let .forallE _ domain _ _ := target then
    if ← isProp domain then throwError "reference-binding-premise-not-association"
    let (_, body) ← goal.intro1
    return ← associations body
  unless ← isProp target do throwError "reference-binding-expected-association-record"
  let some name := target.getAppFn.constName?
    | throwError "reference-binding-expected-association-record"
  let some info := getStructureInfo? (← getEnv) name
    | throwError "reference-binding-expected-association-record"
  if info.fieldNames.isEmpty then throwError "reference-binding-empty-association-record"
  let fields ← goal.constructor
  if fields.isEmpty then throwError "reference-binding-empty-association-record"
  return (← fields.mapM associations).flatten

/-- A source-selected helper is more informative than an unconstrained
library name. Process such anchors first, retaining stable order on ties. -/
private def prioritized (goals : List MVarId) : TacticM (List MVarId) := do
  let scored ← goals.mapM fun goal => goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let signature ← withTransparency .all <| reduce target.getAppArgs[1]!
    return ((← getMVars signature).size, goal)
  return (scored.mergeSort (fun left right => left.1 ≤ right.1)).map Prod.snd

/-- Complete-record search uses finite admitted declaration lists. Every
successful candidate is certified by BodyIn.of_mem and constructor membership.
No proposed equality or recursive assumption is added to the context. If an
otherwise complete association leaves data unconstrained, refuse immediately:
choosing arbitrary unused data is not part of this proposer. -/
private partial def solve (goals : List MVarId) (data : List MVarId)
    (deferred : Nat := 0) : TacticM Bool := do
  let goals ← if deferred == 0 then prioritized goals else pure goals
  match goals with
  | [] =>
      for goal in data do
        if (← instantiateMVars (mkMVar goal)).hasMVar then
          throwError "reference-binding-unconstrained-field: {(← goal.getDecl).userName}"
      return true
  | goal :: rest => goal.withContext do
      let target := (← instantiateMVars (← goal.getType)).headBeta
      trace[zkc.referenceBindings] "matching {target.getAppFn}"
      if target.isAppOfArity ``BodyIn 3 then
        let arguments := target.getAppArgs
        let rec visit (definitions : Expr) (previousDefinitions : List Expr) : TacticM Bool := do
          let cell ← withTransparency .all <| whnf definitions
          if cell.isAppOf ``List.nil then return false
          unless cell.isAppOfArity ``List.cons 3 do
            throwError "reference-binding-definition-list-not-finite"
          let args := cell.getAppArgs
          let definition := args[1]!
          let checkpoint ← saveState
          let signature ← mkAppM ``CheckedDefinition.helper #[definition]
          let raw ← mkAppM ``CheckedDefinition.raw #[definition]
          let sameSignature ← withTransparency .all <| isDefEq signature arguments[1]!
          let typed ← mkAppM ``CheckedDefinition.body #[definition]
          let expected ← withTransparency .all <| reduce arguments[2]!
          let sameBody ← if sameSignature then
            withTransparency .all <| isDefEq typed expected
            else pure false
          if sameSignature && sameBody then
            trace[zkc.referenceBindings] "selected {signature}"
            let member ← mkAppOptM ``List.mem_cons_self #[none, some definition, some args[2]!]
            let mut proof := mkAppN (← mkConstWithFreshMVarLevels ``BodyIn.of_mem)
              #[definitions, definition, arguments[1]!, arguments[2]!,
                member, ← mkEqRefl signature, ← mkEqRefl raw]
            for previous in previousDefinitions do
              proof ← mkAppM ``BodyIn.cons #[previous, proof]
            goal.assign proof
            if ← solve rest data then return true
          checkpoint.restore
          visit args[2]! (definition :: previousDefinitions)
        if ← visit arguments[0]! [] then return true
        let expected ← withTransparency .all <| reduce arguments[2]!
        let signature ← withTransparency .all <| reduce arguments[1]!
        if !expected.hasExprMVar && !signature.hasExprMVar then return false
        -- A dependent body can remain blocked until another association fixes
        -- its data. Retry each pending constraint at most once without progress.
        if deferred + 1 < goals.length then
          return ← solve (rest ++ [goal]) data (deferred + 1)
        return false
      throwError "reference-binding-expected-exact-association"

/-- Construct a subtype whose witness is finite library data and whose property
is a nonempty record of exact body associations. Failure proves nothing. -/
elab "infer_reference_installation" : tactic => withMainContext do
  Term.withoutErrToSorry <| withoutRecover do
    let goal ← getMainGoal
    let pending := (← getGoals).tail
    let target := (← instantiateMVars (← goal.getType)).headBeta
    unless target.isAppOf ``Subtype do
      throwError "infer_reference_installation expects a subtype of library bindings"
    let [data, associations] ← goal.constructor { newGoals := .all }
      | throwError "reference-binding-subtype-shape"
    let fields ← witness data 16
    let constraints ← InferReferenceInstallation.associations associations
    unless ← solve constraints fields do
      throwError "reference-binding-no-complete-match"
    setGoals pending

end ZkcTools.StructuredSource.InferReferenceInstallation
