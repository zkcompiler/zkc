import Zkc.Tests.Frontend.Harness
import Zkc.Tests.Frontend.NameCases

/-!
# The check of names, without the reference

The programs of `NameCases` over the small library given in memory: each rule that the check of
names decides, accepted and refused, and each kind of step of a resolution.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax

/-- A loader of modules held in memory; the file of a module is named by its path. -/
def memoryLoader (sources : Array (String × String)) (names : Array String) :
    Id (Option SourceInput) :=
  let key := pathText names
  (sources.find? (·.1 == key)).map fun (name, text) => { name, parsed := parseString name text }

/-- The byte at which the `occurrence`-th match of `text` on line `line` of `source` starts. -/
def findOnLine (source : String) (line : Nat) (text : String) (occurrence : Nat) : Option Nat := do
  let lines := (source.splitOn "\n").toArray
  let lineText ← lines[line - 1]?
  let parts := (lineText.splitOn text).toArray
  if occurrence == 0 || parts.size <= occurrence then none
  let start := (lines.extract 0 (line - 1)).foldl (fun total l => total + l.utf8ByteSize + 1) 0
  let before := (parts.extract 0 occurrence).foldl (fun total part => total + part.utf8ByteSize) 0
  return start + before + (occurrence - 1) * text.utf8ByteSize

/-- `<line>` or `<line>#<occurrence>`. -/
def readLineSpec (spec : String) : Option (Nat × Nat) :=
  match spec.splitOn "#" with
  | [line] => line.toNat?.map (·, 1)
  | [line, occurrence] => do return (← line.toNat?, ← occurrence.toNat?)
  | _ => none

/-- The text after the first occurrence of `separator`, and the text before it. -/
def splitFirst (text separator : String) : Option (String × String) :=
  match text.splitOn separator with
  | first :: rest@(_ :: _) => some (first, separator.intercalate rest)
  | _ => none

/-- Checks the assertions `// at …` and `// none …` of one module of a test. -/
def checkAssertions (label : String) (check : NameCheck) (name source : String) : TestM Unit := do
  let asserts := (source.splitOn "\n").any fun line =>
    line.startsWith "// at " || line.startsWith "// none "
  unless asserts do return
  let some file := check.program.files.findIdx? (·.name == name)
    | failure s!"{label}: the module {name} is not in the program"
  let table := (check.resolutions.files[file]?).getD {}
  for line in source.splitOn "\n" do
    if line.startsWith "// at " then
      let some (spec, rest) := splitFirst (String.ofList (line.toList.drop 6)) " "
        | failure s!"{label}: unreadable assertion `{line}`"
      let some (text, expected) := splitFirst rest " = "
        | failure s!"{label}: unreadable assertion `{line}`"
      let some (number, occurrence) := readLineSpec spec
        | failure s!"{label}: unreadable assertion `{line}`"
      let some byte := findOnLine source number text occurrence
        | failure s!"{label}: `{text}` is not on line {number}"
      match table[byte.toUInt32]? with
      | some resolution =>
        let found := renderResolution check.program resolution
        expectTrue (found == expected)
          s!"{label}: `{text}` on line {number} resolves to `{found}`, expected `{expected}`"
      | none => failure s!"{label}: `{text}` on line {number} has no resolution, expected `{expected}`"
    else if line.startsWith "// none " then
      let some (spec, text) := splitFirst (String.ofList (line.toList.drop 8)) " "
        | failure s!"{label}: unreadable assertion `{line}`"
      let some (number, occurrence) := readLineSpec spec
        | failure s!"{label}: unreadable assertion `{line}`"
      let some byte := findOnLine source number text occurrence
        | failure s!"{label}: `{text}` is not on line {number}"
      match table[byte.toUInt32]? with
      | some resolution =>
        failure s!"{label}: `{text}` on line {number} resolves to `{renderResolution check.program resolution}`, expected no entry"
      | none => pass

/-- Checks a block's refusals against its expectation. -/
def checkNameExpectation (block : Block) (names : Array String) (check : NameCheck) : TestM Unit := do
  let words := (block.expect.splitOn " ").filter (· != "")
  match words with
  | ["accept"] =>
    match check.refusals[0]? with
    | none => pass
    | some first => failure s!"{block.id}: expected to resolve; {first.span.file}: {first.render}"
  | "refuse" :: rule :: place :: rest =>
    let fileName := match rest with
      | ["in", which] => if which.all Char.isDigit then s!"{block.id}.{which}" else which
      | _ => names[0]!
    let found := match check.refusals[0]? with
      | some first => s!"{first.span.file}: {first.render}"
      | none => "the names resolve"
    match check.refusals[0]? with
    | some first =>
      let position := match place.splitOn ":" with
        | [_] => s!"{first.span.startLine}"
        | _ => s!"{first.span.startLine}:{first.span.startColumn}"
      expectTrue (first.rule == rule && first.span.file == fileName && position == place)
        s!"{block.id}: expected a refusal by {rule} at {place} in {fileName}; {found}"
    | none => failure s!"{block.id}: expected a refusal by {rule} at {place}; {found}"
  | _ => failure s!"{block.id}: unreadable expectation `{block.expect}`"
  for (text, name) in block.files.zip names do
    checkAssertions block.id check name text

/-- Checks a block against `accept` or `refuse <rule> <line>[:<column>] [in <file>]`. -/
def checkNameBlock (block : Block) : TestM Unit := do
  let names := (List.range block.files.size).toArray.map fun index => s!"{block.id}.{index}"
  let inputs := (block.files.zip names).map fun (text, name) =>
    ({ name, parsed := parseString name text } : SourceInput)
  let check := Id.run (checkNames inputs (memoryLoader nameLibrary))
  checkNameExpectation block names check

def nameCaseSuite : TestM Unit := do
  let blocks := readBlocks nameCases
  for block in blocks do checkNameBlock block
  note s!"{blocks.size} programs for the check of names"

end Zkc.Tests.Frontend
