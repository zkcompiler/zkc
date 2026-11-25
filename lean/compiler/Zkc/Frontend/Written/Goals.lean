module

public import Zkc.Frontend.Written.Statement

@[expose] public section
namespace Zkc.Frontend.Written

/-- A single goal's admitted package and the module that states its challenge. Issuance
records the proposition. A submitted proof requires its own judgment. -/
structure IssuedGoal where
  statements : Statements
  publication : Module

/-- One occurrence on the command line. Aliases share the decision for the canonical path.
A failure before name resolution has only the selector. -/
structure GoalResult where
  selector : String
  path : Option String
  outcome : Except String IssuedGoal

/-- The aggregate succeeds exactly when a nonempty request issued every goal. -/
def allGoalsIssued (results : Array GoalResult) : Bool :=
  !results.isEmpty && results.all (·.outcome.isOk)

/-- An injective spelling of the canonical path. Long spellings use bounded ASCII
components. A terminal `Goal` component can never be an internal `Part_` component. -/
private def goalNamespace (path : String) : String :=
  let segment (name : String) := String.join (name.toList.map fun c =>
    if c.isAlphanum then String.singleton c else s!"_u{c.toNat}z")
  let encoded := "__".intercalate ((path.splitOn "::").map segment)
  let width := 120
  if encoded.length ≤ width then "WrittenGoal_" ++ encoded
  else
    let chars := encoded.toList.toArray
    let parts := (List.range ((chars.size + width - 1) / width)).map fun i =>
      "Part_" ++ String.ofList (chars.extract (i * width) ((i + 1) * width)).toList
    ".".intercalate ("WrittenLongGoal" :: parts ++ ["Goal"])

private def issueGoal (root : AdmittedRoot) (id : DeclarationId) (path : String) :
    ExportM IssuedGoal := do
  let claims ← singleGoalClaims root id
  let statements : Statements := ⟨claims, claims.functionsBeforeRoot⟩
  let publication ← statements.module (goalNamespace path) {}
  return ⟨statements, publication⟩

/-- Select each requested occurrence in the same source environment. Schemes can close
lazily, so cache an admission by its source scheme declaration, not a locally allocated
instance number. Each goal starts its relation elaboration from that admission. -/
private def issueSelectedGoals (source : GoalSource)
    (selectors : List String) :
    Array GoalResult := Id.run do
  let index := declarationIndex source.state .goal
  let mut roots : Std.HashMap DeclarationId (ExportM AdmittedRoot) := {}
  let mut decisions : Std.HashMap DeclarationId (ExportM IssuedGoal) := {}
  let mut results := #[]
  for selector in selectors do
    match index.select selector "WK-GOAL" with
    | .error reason => results := results.push ⟨selector, none, .error reason⟩
    | .ok (id, path) =>
      if let some prior := decisions[id]? then
        results := results.push ⟨selector, some path, prior⟩
        continue
      let (nextRoots, decision) := match source.selectId id .soundness with
        | .error reason => (roots, .error reason)
        | .ok (selected, closed) => Id.run do
          let scheme := selected.scheme
          let root := match roots[scheme.declaration]? with
            | some prior => prior
            | none => closed.admitScheme scheme
          let outcome := root.bind fun r => issueGoal r id path
          let place := (selected.goal.map (·.span)).getD scheme.span
          return (roots.insert scheme.declaration root,
            outcome.mapError fun why => s!"{location place}: {why}")
      roots := nextRoots
      decisions := decisions.insert id decision
      results := results.push ⟨selector, some path, decision⟩
  return results

/-- Issue an independent written soundness challenge for each selected source declaration.
A shared source-phase failure is reported for every request. -/
@[no_expose] def issueSoundnessGoals (assembly : Assembly) (selectors : List String) :
    Array GoalResult :=
  match resolveGoals assembly with
  | .ok source => issueSelectedGoals source selectors
  | .error reason => selectors.toArray.map fun selector => ⟨selector, none, .error reason⟩

end Zkc.Frontend.Written
