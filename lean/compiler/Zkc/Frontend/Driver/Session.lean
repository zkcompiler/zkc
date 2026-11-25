module

public import Zkc.Frontend.Driver.Phase

@[expose] public section

set_option autoImplicit false

/-!
# The session

A session is a run in progress: the context it was started with, the state reached, and the
report of each phase run so far. It is a value: a session that has loaded and lowered a library
is the base of every program compiled against that library, and each of them continues from a
copy of it without repeating what the base did.

A command selects the last phase it needs. Admission records which roots have a checked
package. A completed result requires an error-free session with no incomplete checks.
-/

namespace Zkc.Frontend.Driver

structure Session where
  context : Compile.Context
  state : Compile.State := {}
  reports : Array PhaseReport := #[]
  /-- The names of the files given, in the order given: the order of output starts with them. -/
  inputNames : Array String := #[]
  deriving Inhabited

namespace Session

def start (vocabulary : Vocabulary := Zkc.Frontend.vocabulary) (options : Options := {})
    (inputNames : Array String := #[]) : Session :=
  { context := { options, vocabulary }, inputNames }

def hasErrors (session : Session) : Bool := session.state.log.hasErrors

/-- Whether a check was left incomplete: a budget of the compiler ran out (SP10). -/
def hasIncomplete (session : Session) : Bool := session.state.log.hasIncomplete

/-- Runs one phase. -/
def run (session : Session) (phase : Phase) : Session :=
  let (report, state) := phase.runIn session.context session.state
  { session with state, reports := session.reports.push report }

/-- Runs phases in order. With the option to stop at errors, a phase after one that logged an
error is not run. -/
def runAll (session : Session) (phases : Array Phase) : Session := Id.run do
  let mut current := session
  for phase in phases do
    if current.context.options.stopAtErrors && current.hasErrors then break
    current := current.run phase
  return current

/-- Runs phases in order, each timed by the caller's clock. -/
def runAllTimed {m : Type → Type} [Monad m] (clock : m Nat) (session : Session)
    (phases : Array Phase) : m Session := do
  let mut current := session
  for phase in phases do
    if current.context.options.stopAtErrors && current.hasErrors then break
    let (report, state) ← phase.runTimed clock current.context current.state
    current := { current with state, reports := current.reports.push report }
  return current

/-- Loads and assembles the sources of a program, and runs the phases up to one with a name.
`load` reads the library file of a module path, with the effects of the caller. -/
def compile {m : Type → Type} [Monad m] (session : Session) (inputs : Array SourceInput)
    (load : Array String → m (Option SourceInput)) (lastPhase : String := "packages") :
    m Session := do
  let assembly ← Zkc.Frontend.assemble inputs load
  let session := { session with inputNames := inputs.map fun (input : SourceInput) => input.name }
  match upTo (pipeline assembly) lastPhase with
  | .ok phases => return session.runAll phases
  | .error message =>
    let log := session.state.log.add { rule := "phase", span := default, message := .ofText message }
    return { session with state.log := log }

/-- The files in the order of output: those given, in the order given, then those of the
library in the order of the program. -/
def fileOrder (session : Session) : Array String :=
  let files := session.state.program.files.map (·.name)
  session.inputNames ++ files.filter (!session.inputNames.contains ·)

/-- The diagnostics logged by the phases with the given names, in the order they were made. -/
def diagnosticsOf (session : Session) (phases : Array String) : Array Diagnostic :=
  session.reports.foldl (init := #[]) fun found report =>
    if phases.contains report.name then
      found ++ session.state.log.entries.extract report.firstDiagnostic
        (report.firstDiagnostic + report.diagnostics)
    else found

/-- The refusals of the phases with the given names, in source order (`sortRefusals`): their
errors, and nothing else. -/
def refusalsOf (session : Session) (phases : Array String) : Array Refusal :=
  sortRefusals session.fileOrder
    (((session.diagnosticsOf phases).filter (·.isError)).map (·.toRefusal Renderer.plain))

/-- The checks that the phases with the given names left incomplete, in the order they were
made: a budget of the compiler ran out in each. -/
def incompleteOf (session : Session) (phases : Array String) : Array Diagnostic :=
  (session.diagnosticsOf phases).filter (·.isIncomplete)

/-- Whether a phase with a name has run. -/
def ran (session : Session) (name : String) : Bool := session.reports.any (·.name == name)

/-- The packages of the roots asked for: the roots named (each as `types` prints it, or the
declaration of a default instance), qualified by the module when names coincide, or, when none is named, every root that is a function or a
protocol and has a package of its own. A root whose package the core admitted is held; any other
is lacking, with why. -/
def admitRoots (session : Session) (requested : Option (Array String) := none) :
    Admitted CheckedPackage :=
  let state := session.state
  let roots := (Typing.functionRoots state).map fun root =>
    (root, Typing.rootDescription state root, Typing.rootDescription state root (qualified := true))
  let outcomes : Array (String × Except Lack CheckedPackage) := Id.run do
    match requested with
    | none =>
      let mut seen : Std.HashSet String := {}
      let mut ambiguous : Std.HashSet String := {}
      for (_, short, _) in roots do
        if seen.contains short then ambiguous := ambiguous.insert short
        seen := seen.insert short
      return roots.filterMap fun (root, short, full) =>
        match Typing.rootPackage state root with
        | .error (.noPackage _) => none
        | outcome => some (if ambiguous.contains short then full else short, outcome)
    | some names =>
      return names.toList.eraseDups.toArray.map fun name =>
        match roots.filter (fun (_, short, full) => namesRoot name short || namesRoot name full) with
        | #[(root, _, _)] => (name, Typing.rootPackage state root)
        | #[] => (name, .error .absent)
        | candidates =>
          let places := candidates.map fun (root, _, full) => Id.run do
            let some instanceKey := state.table.allocatedKey? root | return full
            let some decl := state.program.declarations[instanceKey.declaration]? | return full
            let some written := decl.name | return full
            return s!"{full} at {written.span.file}:{written.span.render}"
          (name, .error (.ambiguous places))
  Admitted.ofLog state.log outcomes

/-- The diagnostics in the order of output: those of the files given first, in the order the
files were given, then those of the library. -/
def diagnostics (session : Session) : Array Diagnostic :=
  let records := session.state.env.modules.records
  let rank (file : String) : Nat :=
    match records.findIdx? (·.source.name == file) with
    | some index => if records[index]!.source.fromLibrary then records.size + index else index
    | none => 2 * records.size
  session.state.log.sorted rank

/-- The diagnostics as text, one per line and chain line. -/
def renderDiagnostics (session : Session) : Array String :=
  let renderer := session.state.env.renderer
  session.diagnostics.map (·.render renderer)

end Session

/-- What a command of the tool needs: the name of the last phase it runs. -/
inductive Command where
  /-- The names of the program: refusals, or a summary; the table of resolutions. -/
  | names
  /-- The instances of the program with their default instances. -/
  | instances
  /-- The typed bodies, their packages, sites and obligations. -/
  | types
  deriving Inhabited, BEq, Repr

def Command.lastPhase : Command → String
  | .names => "names"
  | .instances => "defaults"
  | .types => "packages"

end Zkc.Frontend.Driver
