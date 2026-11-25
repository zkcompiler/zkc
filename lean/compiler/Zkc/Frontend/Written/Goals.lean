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

/-- Encode a source path as one Lean module component. Escaping the escape character
keeps underscores distinct from encoded punctuation, including the source path separator. -/
private def goalNamespace (path : String) : String :=
  let segment (name : String) := String.join (name.toList.map fun c =>
    if c.isAlphanum && c.toNat < 128 then String.singleton c else s!"_u{c.toNat}z")
  "WrittenGoal_" ++ "__".intercalate ((path.splitOn "::").map segment)

private def issueGoal (root : AdmittedRoot) (id : DeclarationId) (path : String) :
    ExportM IssuedGoal := do
  let claims ← singleGoalClaims root id
  let statements : Statements := ⟨claims, claims.functionsBeforeRoot⟩
  let publication ← statements.module (goalNamespace path) {}
  return ⟨statements, publication⟩

/-- Select each requested occurrence in the same source environment. Schemes can close
lazily, so cache an admission by its source scheme declaration, not a locally allocated
instance number. Each goal starts its relation elaboration from that admission. -/
private def issueSelectedGoals (state : Compile.State) (refusals : Std.HashMap Names.Owner Diagnostic)
    (selectors : List String) :
    Array GoalResult := Id.run do
  let mut roots : Std.HashMap DeclarationId (ExportM AdmittedRoot) := {}
  let mut decisions : Std.HashMap DeclarationId (ExportM IssuedGoal) := {}
  let mut results := #[]
  for selector in selectors do
    match selectDeclaration state .goal selector "WK-GOAL" with
    | .error reason => results := results.push ⟨selector, none, .error reason⟩
    | .ok (id, path) =>
      if let some prior := decisions[id]? then
        results := results.push ⟨selector, some path, prior⟩
        continue
      let selection : ExportM (Selection × Compile.State) := do
        if let some why := refusals[Names.Owner.declaration id]? then
          throw s!"{why.span.file}:{why.render state.env.renderer}"
        selectNamedGoal state path .soundness
      let (nextRoots, decision) := match selection with
        | .error reason => (roots, .error reason)
        | .ok (selected, closed) => Id.run do
          let scheme := selected.scheme
          let root := match roots[scheme.declaration]? with
            | some prior => prior
            | none => admitInstance closed scheme.protocol scheme.span
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
  let resolved := resolveProgram assembly
  let shared := resolved.refusalsByOwner.filter fun owner _ => match owner with
    | .declaration id => !(assembly.program.declarations[id]?).any (·.kind == .goal)
    | _ => true
  let names := { Driver.resolve with run := Driver.installResolution { resolved with refusalsByOwner := shared } }
  match runSourcePhases #[Driver.assemble assembly, names, Driver.instances] with
  | .ok state => issueSelectedGoals state resolved.refusalsByOwner selectors
  | .error reason => selectors.toArray.map fun selector => ⟨selector, none, .error reason⟩

end Zkc.Frontend.Written
