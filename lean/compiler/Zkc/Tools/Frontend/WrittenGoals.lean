import Zkc.Frontend.Written.Goals
import Zkc.Tools.Frontend.Names

namespace Zkc.Tools.Frontend

open Zkc.Frontend Zkc.Frontend.Written

/-- Write the trusted side of a goal. Both files use the same module names as the
in-memory publication. The output directory belongs to this invocation. -/
private def writeGoal (directory : System.FilePath) (publication : Written.Module) : IO Unit := do
  let pending := directory / ".pending"
  IO.FS.createDir pending
  try
    IO.FS.writeFile (pending / "Stated.lean") publication.statements
    IO.FS.writeFile (pending / "Challenge.lean") publication.challenge
    IO.FS.rename pending (directory / publication.space)
  finally
    if ← pending.pathExists then IO.FS.removeDirAll pending

/-- Report every requested occurrence in order, write each distinct challenge once, and
return failure if any required goal was refused. -/
def writtenGoals (options : Names.Options) : IO UInt32 := do
  if options.goals.isEmpty then
    IO.eprintln "written-goals requires at least one --goal"
    return 2
  let inputs ← options.files.mapM Names.readInput
  let assembly ← assemble inputs (Names.libraryLoader options.libraries)
  let results := issueSoundnessGoals assembly options.goals.toList
  if let some directory := options.output then IO.FS.createDir directory
  let mut written : Std.HashSet String := {}
  for result in results do
    let path := result.path.getD result.selector
    match result.outcome with
    | .error why => IO.println s!"{result.selector} -> {path}: refused: {why}"
    | .ok issued =>
      let publication := issued.publication
      if let some directory := options.output then
        unless written.contains path do
          writeGoal directory publication
          written := written.insert path
      let claims := issued.statements.claims
      for goal in claims.goals do
        IO.println (s!"{result.selector} -> {path}: issued {publication.space}.Challenge " ++
          s!"(scheme {claims.schemeName}, root {claims.root}, relation {goal.relation}, " ++
          s!"spec {goal.specification})")
  return if allGoalsIssued results then 0 else 1

end Zkc.Tools.Frontend
