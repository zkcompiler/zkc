import Zkc.Tests.Frontend.TypingReference
import Zkc.Tests.Frontend.FormatCases

/-!
# Formatting keeps a program

A program and its canonical text are checked as the same file, with the library in source:
the canonical text has the outcome of the program, formatting it again gives it back, and it
has the same declarations, of the same kinds, and the same instances, holding the same types.
The declarations and the instances are compared as `zkc-check instances --contents` reads them:
each declaration of the file by its name and its kind, each instance by its description and
what it holds (the type of an alias, the fields of a record, the signature of a function). The
programs of `FormatCases` are admitted before and after formatting; every file of `libraries/`
and `examples/` keeps its outcome, whatever it is.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax

/-- A file checked to the typing of its bodies. -/
structure CheckedFile where
  instances : InstanceCheck
  typing : TypingCheck

/-- Checks one file given under `name`, with the modules that `load` gives: its names, its
instances and the typing of its bodies; or the first refusal of its names. -/
def checkFile (load : Array String → IO (Option SourceInput)) (name : String)
    (parsed : Except SyntaxError SourceFile) : IO (Except String CheckedFile) := do
  let nameCheck ← checkNames #[({ name, parsed } : SourceInput)] load
  if let some first := nameCheck.refusals[0]? then return .error first.render
  let instances := checkInstances nameCheck #[name]
  return .ok { instances, typing := checkTyping instances #[name] }

/-- Each declaration of the file `name` with its kind, then each instance with what it holds. -/
def declarationLines (name : String) (check : InstanceCheck) : Array String := Id.run do
  let program := check.names.program
  let mut lines := #[]
  for index in [0:program.declarations.size] do
    let declaration := program.declarations[index]!
    unless (program.files[declaration.file]?).any (·.name == name) do continue
    lines := lines.push s!"declaration {program.nameOf index}: {repr declaration.kind}"
  for entry in check.state.table.entries do
    let description := match ((Static.describeInstance entry.key.declaration
        entry.key.arguments).run check.context check.state).1 with
      | .ok text => text
      | .error _ => "?"
    let content := match entry.state with
      | .done (.data content) => Instances.renderContent check.state content
      | .exhausted exhaustion => s!"nothing: it is not checked, {exhaustion.describe}"
      | _ => "failed"
    lines := lines.push s!"instance {description} holds {content}"
  return lines

def packageOutcomeText : PackageOutcome → String
  | .admitted _ => "admitted"
  | .unjustified functions _ => s!"not justified: {", ".intercalate functions.toList}"
  | .refused reason _ => s!"refused by the core: {reason}"
  | .waiting reason => s!"waiting for {reason}"
  | .typedOnly reason => s!"typed only: {reason}"
  | .defect message => s!"not emitted: {message}"
  | .exhausted exhaustion => s!"not checked: {exhaustion.describe}"

/-- The outcome of a checked file, without places: its refusals by rule and message, its
incomplete checks by rule, and the outcome of the package of each root. -/
def outcomeLines (check : TypingCheck) : Array String :=
  check.refusals.map (fun refusal => s!"refuse {refusal.rule}: {refusal.message}") ++
    check.incomplete.map (fun diagnostic => s!"incomplete {diagnostic.rule}") ++
    check.packages.map fun report => s!"package {report.description}: {packageOutcomeText report.outcome}"

/-- Whether a checked file is admitted: no refusal, no incomplete check, and the package of
every root, of which there is one at least, admitted by the core. -/
def isAdmitted (checked : CheckedFile) : Bool :=
  checked.typing.refusals.isEmpty && checked.typing.incomplete.isEmpty &&
    !checked.typing.packages.isEmpty &&
    checked.typing.packages.all fun report => report.outcome matches .admitted _

/-- The first difference of two lists of lines, for a message. -/
def firstDifference (before after : Array String) : String :=
  let index := ((before.zip after).findIdx? fun (x, y) => x != y).getD (min before.size after.size)
  s!"line {index + 1}: `{before.getD index "(none)"}` became `{after.getD index "(none)"}`"

/-- The checks of formatting on a source given under `name`: its canonical text parses, is
given back by formatting it again, has the outcome of the source, and the same declarations
and instances. With `admitted`, the source and its canonical text are both admitted. -/
def checkFormatting (load : Array String → IO (Option SourceInput)) (label name : String)
    (source : ByteArray) (admitted : Bool) : TestM Unit := do
  let parsed := parse name source
  let .ok sourceFile := parsed
    | failure s!"{label}: the source is refused by the parser"
  let canonical := formatSourceFile sourceFile
  let reparsed := parseString name canonical
  let .ok canonicalFile := reparsed
    | failure s!"{label}: the canonical text is refused by the parser:\n{canonical}"
  expectTrue (formatSourceFile canonicalFile == canonical)
    s!"{label}: formatting the canonical text changes it"
  let before ← checkFile load name parsed
  let after ← checkFile load name reparsed
  match before, after with
  | .error first, _ => failure s!"{label}: the names of the source do not resolve: {first}"
  | .ok _, .error first =>
    failure s!"{label}: the names of the canonical text do not resolve: {first}\n{canonical}"
  | .ok original, .ok formatted =>
    if admitted then
      expectTrue (isAdmitted original) s!"{label}: the source is not admitted: {outcomeLines original.typing}"
      expectTrue (isAdmitted formatted)
        s!"{label}: the canonical text is not admitted: {outcomeLines formatted.typing}\n{canonical}"
    let outcomes := (outcomeLines original.typing, outcomeLines formatted.typing)
    expectTrue (outcomes.1 == outcomes.2)
      s!"{label}: the canonical text has another outcome: {firstDifference outcomes.1 outcomes.2}"
    let declarations := (declarationLines name original.instances, declarationLines name formatted.instances)
    expectTrue (declarations.1 == declarations.2)
      s!"{label}: the canonical text has other declarations or instances: {firstDifference declarations.1 declarations.2}"

/-- The programs of `FormatCases`: each is admitted, and so is its canonical text, which keeps
its declarations, their kinds and their types. -/
def formatCaseSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries]
  let blocks := readBlocks formatCases
  for block in blocks do
    expectTrue (block.expect == "accept") s!"{block.id}: expects `{block.expect}`"
    match block.files with
    | #[text] => checkFormatting load block.id s!"{block.id}.zkc" text.toUTF8 true
    | _ => failure s!"{block.id}: a program of one module is expected"
  note s!"{blocks.size} programs, each admitted before and after formatting"
  expectTrue (blocks.size == 36) s!"expected the 36 programs of `FormatCases`, found {blocks.size}"

/-- Every file of `libraries/` and `examples/`, given alone with the library in source (and, for
a file of `examples/`, the modules of `examples/` and `examples/support/`): its canonical text has
its outcome, its declarations and its instances. -/
def corpusFormattingSuite (repository : Repository) : TestM Unit := do
  let libraryLoad ← cachedLoader #[repository.libraries]
  let programLoad ← cachedLoader #[repository.libraries, repository.examples, repository.examples / "support"]
  let mut count := 0
  for (directory, load) in [(repository.libraries, libraryLoad), (repository.examples, programLoad)] do
    for path in ← sortedFiles directory "zkc" do
      count := count + 1
      checkFormatting load path.toString path.toString (← IO.FS.readBinFile path) false
  note s!"{count} files of libraries/ and examples/, each with its outcome after formatting"

end Zkc.Tests.Frontend
