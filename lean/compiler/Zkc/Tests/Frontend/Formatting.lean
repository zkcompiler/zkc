import Zkc.Tests.Frontend.TypingReference
import Zkc.Tests.Frontend.Independent
import Zkc.Tests.Frontend.FormatCases

/-!
# Formatting keeps a program

A source and its canonical text are checked as the same file, with the library in source, and
compared by what the checker computes from them: their outcome, the declarations of the file,
the instances, and the packages of the core emitted for the roots, which hold the bodies. The
outcome is the refusals and the incomplete checks by rule, and the outcome of the package of each
root; a message is not compared, since it holds places and source text, which formatting moves.
A declaration is compared by its name, its kind and its modifiers (`pub`, a kernel attribute,
`spec`, `entry`, `partial`); an instance by its description and what it holds, as
`describedInstances` prints it; a package by its text.

The sources:
- the programs of `FormatCases`, each admitted before and after formatting, with the checks of
  the printer;
- every file of `libraries/` and `examples/` (`corpusSuite` makes the checks of the printer);
- the conformance tests tagged `fmt`, each admitted before and after formatting
  (`conformanceSuite` makes the checks of the printer);
- the independent conformance suite: every file that parses, with the checks of the printer, and
  each case of one file that the suite expects to be accepted.
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
    (parsed : Except SyntaxError SourceFile) : IO (Except (Array Refusal) CheckedFile) := do
  let nameCheck ← checkNames #[({ name, parsed } : SourceInput)] load
  unless nameCheck.refusals.isEmpty do return .error nameCheck.refusals
  let instances := checkInstances nameCheck #[name]
  return .ok { instances, typing := checkTyping instances #[name] }

/-- The modifiers of a declaration: `pub`, and the kernel attribute and the word written before
`def` or `protocol`. -/
def modifiers (declaration : Declaration) : Array String :=
  let kernel (value : Option KernelAttr) : Array String :=
    value.toArray.map fun kernelAttr => s!"kernel {kernelAttr.name.content}"
  let written := match declaration.node with
    | .«def» node => kernel node.kernel ++ match node.modifier with
      | some (.spec _) => #["spec"]
      | some (.entry _) => #["entry"]
      | none => #[]
    | .memberDef node => kernel node.kernel ++ (if node.spec then #["spec"] else #[])
    | .protocol node => if node.spec then #["spec"] else #[]
    | .member (.defMember _ (some (.spec _)) ..) => #["spec"]
    | .member (.defMember _ (some (.«partial» _)) ..) => #["partial"]
    | _ => #[]
  (if declaration.pub then #["pub"] else #[]) ++ written

/-- Each declaration of the file `name`: its name, its kind and its modifiers. -/
def declarationLines (name : String) (check : InstanceCheck) : Array String := Id.run do
  let program := check.names.program
  let mut lines := #[]
  for index in [0:program.declarations.size] do
    let declaration := program.declarations[index]!
    unless (program.files[declaration.file]?).any (·.name == name) do continue
    lines := lines.push
      s!"declaration {program.nameOf index}: {repr declaration.kind} {modifiers declaration}"
  return lines

/-- Each instance with what it holds. -/
def instanceLines (check : InstanceCheck) : Array String :=
  (describedInstances check).map fun (description, content) => s!"instance {description} holds {content}"

def packageOutcomeText : PackageOutcome → String
  | .admitted _ => "admitted"
  | .refused source errors => s!"refused by the core: {source.describeRefusals errors}"
  | .waiting reason => s!"waiting for {reason}"
  | .typedOnly reason => s!"typed only: {reason}"
  | .defect message => s!"not emitted: {message}"
  | .exhausted exhaustion => s!"not checked: {exhaustion.describe}"

/-- The outcome of a checked file: its refusals and its incomplete checks by rule, and the
outcome of the package of each root. -/
def outcomeLines (check : TypingCheck) : Array String :=
  check.refusals.map (fun refusal => s!"refuse {refusal.rule}") ++
    check.incomplete.map (fun diagnostic => s!"incomplete {diagnostic.rule}") ++
    check.packages.map fun report => s!"package {report.description}: {packageOutcomeText report.outcome}"

/-- Whether a checked file is admitted: no refusal, no incomplete check, and the package of
every root, of which there is one at least, admitted by the core. -/
def isAdmitted (checked : CheckedFile) : Bool :=
  checked.typing.refusals.isEmpty && checked.typing.incomplete.isEmpty &&
    !checked.typing.packages.isEmpty &&
    checked.typing.packages.all fun report => report.outcome matches .admitted _

/-- The position of the first difference of two lists of lines, counted from 0. -/
def differenceAt (before after : Array String) : Nat :=
  ((before.zip after).findIdx? fun (x, y) => x != y).getD (min before.size after.size)

/-- The first difference of two lists of lines, for a message. -/
def firstDifference (before after : Array String) : String :=
  let index := differenceAt before after
  s!"line {index + 1}: `{before.getD index "(none)"}` became `{after.getD index "(none)"}`"

/-- The checks of formatting on a source given under `name`: its canonical text parses, and has
the outcome of the source, its declarations, its instances and its packages. With `admitted`,
the source and its canonical text are both admitted. -/
def checkFormatting (load : Array String → IO (Option SourceInput)) (label name : String)
    (source : SourceFile) (admitted : Bool) : TestM Unit := do
  let canonical := formatSourceFile source
  let reparsed := parseString name canonical
  let .ok _ := reparsed
    | failure s!"{label}: the canonical text is refused by the parser:\n{canonical}"
  let before ← checkFile load name (.ok source)
  let after ← checkFile load name reparsed
  match before, after with
  | .error original, .error formatted =>
    let sameDiagnostic (r : Refusal) := (r.rule, r.message)
    expectTrue (!admitted && expectedNameRefusal name original &&
      original.map sameDiagnostic == formatted.map sameDiagnostic)
      s!"{label}: name refusals before and after formatting: {original.map (·.render)}, {formatted.map (·.render)}"
  | .error first, _ => failure s!"{label}: the names of the source do not resolve: {first.map (·.render)}"
  | .ok _, .error first =>
    failure s!"{label}: the names of the canonical text do not resolve: {first.map (·.render)}\n{canonical}"
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
      s!"{label}: the canonical text has other declarations: {firstDifference declarations.1 declarations.2}"
    let instances := (instanceLines original.instances, instanceLines formatted.instances)
    expectTrue (instances.1 == instances.2)
      s!"{label}: the canonical text has other instances: {firstDifference instances.1 instances.2}"
    let packages := (packageTexts original.typing, packageTexts formatted.typing)
    expectTrue (packages.1 == packages.2)
      s!"{label}: the canonical text emits other packages: the package {differenceAt packages.1 packages.2 + 1} of {packages.1.size} differs"

/-- The programs of `FormatCases`: the checks of the printer, and each program is admitted, and
so is its canonical text, which keeps its outcome, its declarations, its instances and its
packages. -/
def formatCaseSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries]
  let blocks := readBlocks formatCases
  for block in blocks do
    unless block.expect == "accept" do failure s!"{block.id}: expects `{block.expect}`"
    let name := s!"{block.id}.zkc"
    match block.files with
    | #[text] =>
      match parseString name text with
      | .ok source =>
        checkPrinter block.id source
        checkFormatting load block.id name source (admitted := true)
      | .error error => failure s!"{block.id}: the source is refused by the parser: {error.render}"
    | _ => failure s!"{block.id}: a program of one module is expected"
  note s!"{blocks.size} programs, each admitted before and after formatting"
  expectTrue (blocks.size == 36) s!"expected the 36 programs of `FormatCases`, found {blocks.size}"

/-- Every file of `libraries/` and `examples/`, given alone with the library in source (and, for
a file of `examples/`, the modules of `examples/` and `examples/support/`): its canonical text has
its outcome, its declarations, its instances and its packages. A file that is refused keeps the
rules that refuse it. -/
def corpusFormattingSuite (repository : Repository) : TestM Unit := do
  let libraryLoad ← cachedLoader #[repository.libraries]
  let programLoad ← cachedLoader #[repository.libraries, repository.examples, repository.examples / "support"]
  let mut count := 0
  for (directory, load) in [(repository.libraries, libraryLoad), (repository.examples, programLoad)] do
    for path in ← sortedFiles directory "zkc" do
      count := count + 1
      match parse path.toString (← IO.FS.readBinFile path) with
      | .ok source => checkFormatting load path.toString path.toString source (admitted := false)
      | .error error => failure s!"{path}: {error.render}"
  note s!"{count} files of libraries/ and examples/, each with its outcome, its declarations, its instances and its packages after formatting"

/-- Whether the expectation of a conformance test carries the tag `fmt`, as `accept, fmt` does. -/
def isFormattingTest (expect : String) : Bool :=
  ((expect.splitOn ",").map trimSpaces).contains "fmt"

/-- The conformance tests tagged `fmt`: each is admitted, and so is its canonical text, which
keeps its outcome, its declarations, its instances and its packages. -/
def formatTaggedSuite (repository : Repository) : TestM Unit := do
  let load ← cachedLoader #[repository.libraries]
  let mut count := 0
  for path in ← sortedFiles (repository.conformance) "txt" do
    for block in readBlocks (← IO.FS.readFile path) do
      unless isFormattingTest block.expect do continue
      count := count + 1
      let name := s!"{block.id}.zkc"
      match block.files with
      | #[text] =>
        match parseString name text with
        | .ok source => checkFormatting load block.id name source (admitted := true)
        | .error error => failure s!"{block.id}: the source is refused by the parser: {error.render}"
      | _ => failure s!"{block.id}: a test of one module is expected"
  note s!"{count} conformance tests tagged `fmt`, each admitted before and after formatting"
  expectTrue (count == 5) s!"expected the 5 conformance tests tagged `fmt`, found {count}"

/-- The independent conformance suite: the checks of the printer on every file that parses, and
each case of one file that the suite expects to be accepted keeps its outcome, its declarations,
its instances and its packages after formatting. -/
def independentFormattingSuite (repository : Repository) : TestM Unit := do
  let cases ← match ← readIndependentCases repository.independent with
    | .ok cases => pure cases
    | .error message => do failure s!"independent suite: {message}"; return
  let load ← cachedLoader #[repository.libraries]
  let mut printed := 0
  let mut compared := 0
  for case in cases do
    for (fileName, path) in case.files do
      let name := s!"{case.id}/{fileName}"
      let .ok source := parse name (← IO.FS.readBinFile path) | continue
      printed := printed + 1
      checkPrinter name source
      if case.expected == "accept" && case.files.size == 1 then
        compared := compared + 1
        checkFormatting load name name source (admitted := false)
  note s!"{printed} files of the independent suite parse; {compared} cases of one file that the suite expects to be accepted keep their meaning after formatting"
  expectTrue (compared == 69)
    s!"expected the 69 cases of one file that the independent suite expects to be accepted, found {compared}"

end Zkc.Tests.Frontend
