import Zkc.Frontend.Written.Goals
import Zkc.Tools.Frontend.Names

namespace Zkc.Tools.Frontend

open Zkc.Frontend Zkc.Frontend.Written

/-- Write what the issuer publishes for a goal: the trusted side (`Stated.lean`, the data module,
and `Challenge.lean`) and the two modules for proofs and readers (`Views.lean`, `Fees.lean`). The
files use the same module names as the in-memory publication. The output directory belongs to
this invocation. -/
private def writeGoal (directory : System.FilePath) (publication : Written.Publication) : IO Unit := do
  let pending := directory / ".pending"
  IO.FS.createDir pending
  try
    for (file, source) in [("Stated.lean", publication.data), ("Challenge.lean", publication.challenge),
        ("Views.lean", publication.views), ("Fees.lean", publication.fees)] do
      let handle ← IO.FS.Handle.mk (pending / file) .write
      handle.putStr source
      -- A buffered final write can fail after putStr returns.
      handle.flush
    let target := (publication.space.splitOn ".").foldl (· / ·) directory
    if let some parent := target.parent then IO.FS.createDirAll parent
    IO.FS.rename pending target
  finally
    if ← pending.pathExists then IO.FS.removeDirAll pending

/-- Report every requested occurrence in order, write each distinct challenge once, and
return failure if any required goal was refused. -/
def writtenGoals (options : Names.Options) : IO UInt32 := do
  if options.goals.isEmpty then
    IO.eprintln "written-goals requires at least one --goal"
    return 2
  let source ← (do
    let inputs ← options.files.mapM Names.readInput
    assemble inputs (Names.libraryLoader options.libraries)).toBaseIO
  let results := match source with
    | .ok assembly => issueSoundnessGoals assembly options.goals.toList
    | .error why => options.goals.map fun selector => ⟨selector, none, .error (toString why)⟩
  let ready ← (options.output.forM IO.FS.createDir).toBaseIO
  let mut exports : Std.HashMap String (Except IO.Error Unit) := {}
  let mut exported := true
  for result in results do
    let path := result.path.getD result.selector
    match result.outcome with
    | .error why => IO.println s!"{result.selector} -> {path}: refused: {why}"
    | .ok issued =>
      let publication := issued.publication
      if let some directory := options.output then
        let status ← match exports[path]? with
          | some prior => pure prior
          | none => match ready with
            | .error why => pure (.error why)
            | .ok () => (writeGoal directory publication).toBaseIO
        exports := exports.insert path status
        if let .error why := status then
          IO.println s!"{result.selector} -> {path}: export failed: {why}"
          exported := false
          continue
      let claims := issued.statements.claims
      for goal in claims.goals do
        IO.println (s!"{result.selector} -> {path}: issued {publication.space}.Challenge " ++
          s!"(scheme {claims.schemeName}, root {claims.root}, relation {goal.relation}, " ++
          s!"spec {goal.specification})")
  return if exported && allGoalsIssued results then 0 else 1

end Zkc.Tools.Frontend
