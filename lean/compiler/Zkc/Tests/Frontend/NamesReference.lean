import Zkc.Tests.Frontend.Reference
import Zkc.Tests.Frontend.Names
import Zkc.Tools.Frontend.Generate

/-!
# The check of names over the reference

Read from the reference directory: the tests of layer A, every module of `lib/` as a root, and
the worked programs with their example files. A module of a test or of the library is read
from `lib/`; a worked program also reads `programs/` and `programs/support/`.

A refusal is the test's when it is in one of the test's own modules (a module `zkc::…` of a test
stands in place of the library module); a refusal in a module of the library that a test reaches
is a property of the library, reported once.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax

/-- The rules of §6.1 that the check of names decides. -/
def nameRules : Array String := #["NL2", "NL3", "NL4", "NL7", "NL10"]

/-- The tests of layer A that the check of names refuses: the rule and the line of the first
refusal, in the first module of the test. `L-ALG3` is refused by SP3: a member of `Self` that no
interface of `Self` declares is refused at the declaration, whatever the instances are. -/
def expectedNameRefusals : Array (String × String × Nat) := #[
  ("S-Z6", "NL2", 6), ("I-8d", "NL3", 11), ("R-SP7a", "NL3", 3), ("N-NL3a", "NL3", 2),
  ("L-HASH1", "NL3", 8), ("R-NL10a", "NL10", 2), ("L-ALG3", "SP3", 57)]

/-- The tests of layer A whose refusal is by a rule of names, and whose deciding needs the type
of an expression: they pass the check of names. -/
def waitingForTyping : Array (String × String) := #[]

/-- A loader of library modules from directories, which parses each file once. -/
def cachedLoader (directories : Array System.FilePath) :
    IO (Array String → IO (Option SourceInput)) := do
  let cache ← IO.mkRef ({} : Std.HashMap String (Option SourceInput))
  return fun names => do
    let key := pathText names
    if let some cached := (← cache.get)[key]? then return cached
    let mut found : Option SourceInput := none
    for directory in directories do
      let file := (names.foldl (· / ·) directory).addExtension "zkc"
      if ← file.pathExists then
        let source ← IO.FS.readBinFile file
        found := some { name := file.toString, parsed := parse file.toString source }
        break
    cache.modify (·.insert key found)
    return found

/-- The place and the text of every `Path` of a tree, read from its dump: the walk of the
printer, which is not the resolver's. A path with static arguments has no text. -/
def pathPlaces (tree : File) : Array (Nat × Nat × String) := Id.run do
  let mut places := #[]
  for line in (dumpFile tree true).splitOn "\n" do
    let some (_, rest) := splitFirst line ": Path" | continue
    unless rest.startsWith " " do continue
    let some (text, span) := splitFirst rest "@" | continue
    let some (start, _) := splitFirst span "-" | continue
    match start.splitOn ":" with
    | [line, column] =>
      if let (some l, some c) := (line.toNat?, column.toNat?) then
        places := places.push (l, c, trimSpaces text)
    | _ => pure ()
  return places

/-- The byte of a line and a column (in characters) of a source. -/
def byteOf (lines : Array String) (line column : Nat) : Nat :=
  let start := (lines.extract 0 (line - 1)).foldl (fun total l => total + l.utf8ByteSize + 1) 0
  start + (String.ofList (((lines[line - 1]?).getD "").toList.take (column - 1))).utf8ByteSize

/-- The paths of a given file that have no resolution. -/
def unrecordedPaths (check : NameCheck) (name : String) (source : String) (tree : File) :
    Array String := Id.run do
  let some file := check.program.files.findIdx? (·.name == name) | return #[s!"{name}: not in the program"]
  let table := (check.resolutions.files[file]?).getD {}
  let lines := (source.splitOn "\n").toArray
  let mut found := #[]
  for (line, column, text) in pathPlaces tree do
    if table.contains (byteOf lines line column).toUInt32 then continue
    found := found.push s!"{name}:{line}:{column} {if text.isEmpty then "(a path with static arguments)" else text}"
  return found

/-- Every path of the given files of a check that has no refusal in that file has a
resolution. -/
def checkCoverage (label : String) (check : NameCheck) (files : Array (String × String × File)) :
    TestM Unit := do
  for (name, source, tree) in files do
    if check.refusals.any (·.span.file == name) then continue
    let unrecorded := unrecordedPaths check name source tree
    if unrecorded.isEmpty then pass
    else for entry in unrecorded do failure s!"{label}: a path without a resolution: {entry}"

/-- The refusals of a check in the given files, and those in the library. -/
def splitRefusals (check : NameCheck) (names : Array String) : Array Refusal × Array Refusal :=
  check.refusals.partition fun refusal => names.contains refusal.span.file

def conformanceNamesSuite (reference : System.FilePath) : TestM Unit := do
  let load ← cachedLoader #[reference / "lib"]
  let mut total := 0
  let mut parserRefused := 0
  let mut accepted := 0
  let mut refusedHere : Array String := #[]
  let mut waiting : Array String := #[]
  let mut libraryRefusals : Array String := #[]
  let mut seen : Array String := #[]
  let mut contradictions : Array (String × String) := #[]
  for path in ← sortedFiles (reference / "conformance") "txt" do
    unless (path.fileName.getD "").startsWith "layer-a-" do continue
    for block in readBlocks (← IO.FS.readFile path) do
      total := total + 1
      seen := seen.push block.id
      let .ok files := parseBlock block
        | parserRefused := parserRefused + 1
      let names := (List.range files.size).toArray.map fun index => s!"{block.id}.{index}"
      let inputs := (List.range files.size).toArray.map fun index =>
        ({ name := names[index]!, parsed := .ok files[index]! } : SourceInput)
      let check ← checkNames inputs fun names => (load names : IO _)
      checkCoverage block.id check ((names.zip (block.files.zip files)).map fun (name, text, tree) =>
        (name, text, tree.tree))
      let (own, library) := splitRefusals check names
      for refusal in library do
        let text := s!"{refusal.span.file}: {refusal.render}"
        unless libraryRefusals.contains text do
          libraryRefusals := libraryRefusals.push text
          failure s!"{block.id} reaches a module of the library that does not resolve: {text}"
      let rules := refusalRules block.expect
      let expected := expectedNameRefusals.find? (·.1 == block.id)
      let waits := waitingForTyping.find? (·.1 == block.id)
      if let some (_, rule, line) := expected then
        match own[0]? with
        | some first =>
          if first.rule == rule && first.span.file == names[0]! && first.span.startLine.toNat == line then
            pass
            refusedHere := refusedHere.push s!"{block.id} {rule} line {line}"
            if contradicts block.expect rule then
              contradictions := contradictions.push
                (block.id, s!"{block.id} expects `{block.expect}`; refused by {rule} at line {line}")
          else failure s!"{block.id}: expected a refusal by {rule} at line {line}; {first.span.file}: {first.render}"
        | none => failure s!"{block.id}: expected a refusal by {rule} at line {line}; the names resolve"
      else if rules.any nameRules.contains && waits.isNone then
        failure s!"{block.id}: expects `{block.expect}`, and neither a line nor a reason to wait for typing is recorded"
      else
        match own[0]? with
        | none =>
          pass
          if let some (_, reason) := waits then waiting := waiting.push s!"{block.id}: {reason}"
          else accepted := accepted + 1
        | some first =>
          failure s!"{block.id}: expects `{block.expect}`; refused by the check of names: {first.span.file}: {first.render}"
  reportContradictions contradictions
  note s!"{total} tests of layer A: {parserRefused} refused by the parser, {refusedHere.size} refused by the check of names as expected, {waiting.size} waiting for typing, {accepted} pass the check of names"
  for entry in refusedHere do note s!"refused: {entry}"
  for entry in waiting do note s!"waiting for typing: {entry}"
  for (id, rule, _) in expectedNameRefusals do
    unless seen.contains id do failure s!"{id}: expected to be refused by {rule}; not found"
  -- the counts of `conformance/README.md` give 147 tests to `layer-a-types-facts.txt`, which
  -- has 149
  expectTrue (total == 322) s!"expected the 322 tests of layer A, found {total}"

/-- Every module of `lib/` as a root resolves, with every module it reaches. -/
def libraryNamesSuite (reference : System.FilePath) : TestM Unit := do
  let load ← cachedLoader #[reference / "lib"]
  let mut count := 0
  for path in ← sortedFiles (reference / "lib") "zkc" do
    count := count + 1
    let source ← IO.FS.readBinFile path
    let input : SourceInput := { name := path.toString, parsed := parse path.toString source }
    let check ← checkNames #[input] fun names => (load names : IO _)
    if let .ok tree := input.parsed then
      checkCoverage path.toString check #[(path.toString, ← IO.FS.readFile path, tree.tree)]
    if check.refusals.isEmpty then pass
    for refusal in check.refusals do
      failure s!"{path} does not resolve: {refusal.span.file}: {refusal.render}"
  note s!"{count} modules of lib/"

/-- Every worked program resolves with its example file where there is one, and with every
module it reaches. -/
def programNamesSuite (reference : System.FilePath) : TestM Unit := do
  let programs := reference / "programs"
  let load ← cachedLoader #[reference / "lib", programs, programs / "support"]
  let mut count := 0
  for path in ← sortedFiles programs "zkc" do
    let stem := path.fileStem.getD ""
    if stem.endsWith "_example" || path.parent != some programs then continue
    count := count + 1
    let exampleFile := programs / s!"{stem}_example.zkc"
    let files := if ← exampleFile.pathExists then #[path, exampleFile] else #[path]
    let inputs ← files.mapM fun file => do
      let source ← IO.FS.readBinFile file
      return ({ name := file.toString, parsed := parse file.toString source } : SourceInput)
    let check ← checkNames inputs fun names => (load names : IO _)
    let mut parsed := #[]
    for (file, input) in files.zip inputs do
      if let .ok tree := input.parsed then
        parsed := parsed.push (file.toString, ← IO.FS.readFile file, tree.tree)
    checkCoverage stem check parsed
    let label := if files.size == 2 then s!"{stem} with {stem}_example" else stem
    if check.refusals.isEmpty then pass
    for refusal in check.refusals do
      failure s!"{label} does not resolve: {refusal.span.file}: {refusal.render}"
  note s!"{count} worked programs"

/-- The generated program of the measurements resolves with the library of the reference. -/
def generatedNamesSuite (reference : System.FilePath) : TestM Unit := do
  let load ← cachedLoader #[reference / "lib"]
  let text := Zkc.Tools.Frontend.Generate.program 50000
  let input : SourceInput := { name := "generated", parsed := parseString "generated" text }
  let check ← checkNames #[input] fun names => (load names : IO _)
  if check.refusals.isEmpty then pass
  for refusal in check.refusals.extract 0 5 do
    failure s!"the generated program does not resolve: {refusal.span.file}: {refusal.render}"
  if let .ok tree := input.parsed then checkCoverage "generated" check #[("generated", text, tree.tree)]
  note s!"generated program: {check.program.declarations.size} declarations, {check.resolutions.size} resolved paths"

end Zkc.Tests.Frontend
