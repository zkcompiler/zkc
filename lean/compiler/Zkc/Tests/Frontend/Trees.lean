import Zkc.Tests.Frontend.Independent
import Zkc.Tests.Frontend.TypingReference
import Zkc.Tests.Frontend.ProtocolRuns
import Zkc.Tests.Frontend.Generators
import Zkc.Tools.Frontend.Trees
import Zkc.Tools.Frontend.Reading

/-!
# The typed trees of the corpus's protocols

The corpus is every program whose roots the frontend emits: each module of `libraries/`, each
worked program of `examples/` with its example file (an example file without a program on its
own), the generated program, every test of layer A of the conformance and every case of the
independent suite that the frontend accepts, the test modules of the generators of true
statements (`Generators`) and the programs of the run tests of protocols (`ProtocolRuns`).

For every program of the corpus: what became of the body of each protocol instance, the
invariants of the trees, and the second reading. The second reading evaluates the tree of a
protocol root role by role, from the tables of the passes, and compares what each role does
with the run of the emitted package under the model of the vocabulary's rows, by the keys of
the events (`Zkc.Tools.Frontend.Reading`): it is the check that the emitter keeps what each
role does.
-/

set_option autoImplicit false

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax
open Zkc.Tools.Frontend

/-- A program of the corpus: its identifier, its files, and the loader of its library. -/
structure CorpusProgram where
  id : String
  inputs : Array SourceInput
  load : Array String → IO (Option SourceInput)

/-- The programs of the corpus, in a fixed order. -/
def corpusPrograms (repository : Repository) : IO (Array CorpusProgram) := do
  let library ← cachedLoader #[repository.libraries]
  let programs := repository.examples
  let withPrograms ← cachedLoader #[repository.libraries, programs, programs / "support"]
  let mut corpus : Array CorpusProgram := #[]
  let readFile (file : System.FilePath) : IO SourceInput := do
    return { name := file.toString, parsed := parse file.toString (← IO.FS.readBinFile file) }
  -- the modules of the library
  for path in ← sortedFiles repository.libraries "zkc" do
    let relative := ((path.toString.drop (repository.libraries.toString.length + 1)).dropEnd 4).toString
    corpus := corpus.push { id := s!"libraries/{relative}", inputs := #[← readFile path]
                            load := fun names => library names }
  -- the worked programs, each with its example file, and an example file without a program
  for path in ← sortedFiles programs "zkc" do
    let stem := path.fileStem.getD ""
    if path.parent != some programs then continue
    if stem.endsWith "_example" && (← (programs / s!"{(stem.dropEnd 8).toString}.zkc").pathExists) then
      continue
    if expectedProgramRefusals.any (·.1 == stem) then continue
    let exampleFile := programs / s!"{stem}_example.zkc"
    let files := if ← exampleFile.pathExists then #[path, exampleFile] else #[path]
    corpus := corpus.push { id := s!"examples/{stem}", inputs := ← files.mapM readFile
                            load := fun names => withPrograms names }
  -- the generated program
  let generated := Zkc.Tools.Frontend.Generate.program 50000
  corpus := corpus.push { id := "generated"
                          inputs := #[{ name := "generated", parsed := parseString "generated" generated }]
                          load := fun names => library names }
  -- the tests of layer A
  for path in ← sortedFiles repository.conformance "txt" do
    unless (path.fileName.getD "").startsWith "layer-a-" do continue
    for block in readBlocks (← IO.FS.readFile path) do
      let .ok files := parseBlock block | continue
      let inputs := (List.range files.size).toArray.map fun index =>
        ({ name := s!"{block.id}.{index}", parsed := .ok files[index]! } : SourceInput)
      corpus := corpus.push { id := s!"conformance/{block.id}", inputs, load := fun names => library names }
  -- the cases of the independent suite
  match ← readIndependentCases repository.independent with
  | .error message => throw (IO.userError s!"the independent suite: {message}")
  | .ok cases =>
    for case in cases do
      if ["lexical", "parse", "parse-only"].contains case.phase then continue
      let mut inputs : Array SourceInput := #[]
      for (name, file) in case.files do
        let label := s!"{case.id}/{name}"
        inputs := inputs.push { name := label, parsed := parse label (← IO.FS.readBinFile file) }
      corpus := corpus.push { id := s!"independent/{case.id}", inputs, load := fun names => library names }
  -- the test modules of the generators of true statements, with the worked programs
  for (name, text) in generatorPrograms do
    corpus := corpus.push { id := s!"generators/{name}"
                            inputs := #[{ name, parsed := parseString name text }]
                            load := fun names => withPrograms names }
  -- the programs of the run tests of protocols
  for (name, text) in protocolRunPrograms do
    corpus := corpus.push { id := s!"runs/{name}"
                            inputs := #[{ name, parsed := parseString name text }]
                            load := fun names => pure (Id.run (memoryLoader nameLibrary names)) }
  return corpus

/-- The seeds under which the second reading is compared with the run of each package. -/
def readingSeeds : List Nat := List.range 4

/-- The trees of the corpus. -/
def treeSuite (repository : Repository) : TestM Unit := do
  let start ← IO.monoMsNow
  let mut outcomes : Array (String × Nat) := #[]
  let mut violations : Array (String × Nat × String) := #[]
  let mut readAgree := 0
  let mut readDiffer : Array String := #[]
  let mut readIncomplete : Array (String × Nat) := #[]
  for program in ← corpusPrograms repository do
    let .ok trees ← Trees.treesOf program.inputs program.load | continue
    for (_, _, outcome) in Trees.protocolOutcomes trees do
      let key := (outcome.splitOn ":").headD outcome
      outcomes := match outcomes.findIdx? (·.1 == key) with
        | some index => outcomes.modify index fun (key, count) => (key, count + 1)
        | none => outcomes.push (key, 1)
    -- the second reading of each protocol root against the run of its package
    for (description, verdict) in Reading.compareProgram trees readingSeeds do
      match verdict with
      | .agree _ => readAgree := readAgree + 1
      | .differ .. =>
        readDiffer := readDiffer.push
          s!"{program.id}: reading of {description}: {Reading.describeVerdict verdict}"
      | .incomplete why =>
        let text := Reading.describeVerdict (.incomplete why)
        if (text.splitOn "the reading breaks off").length > 1 then
          readDiffer := readDiffer.push s!"{program.id}: reading of {description}: {text}"
        let key := (text.take 110).toString
        readIncomplete := match readIncomplete.findIdx? (·.1 == key) with
          | some index => readIncomplete.modify index fun (key, count) => (key, count + 1)
          | none => readIncomplete.push (key, 1)
    for line in Trees.violationsOf trees do
      -- the kind of a violation: its message without the numbers of binders
      let message := (line.splitOn ": ").getLastD line
      let kind := String.ofList (message.toList.filter fun char => !char.isDigit)
      violations := match violations.findIdx? (·.1 == kind) with
        | some index => violations.modify index fun (kind, count, first) => (kind, count + 1, first)
        | none => violations.push (kind, 1, s!"{program.id}: {line}")
  note s!"protocol instances: {", ".intercalate (outcomes.map fun (key, count) => s!"{count} {key}").toList}"
  note s!"second reading against the run of the package: {readAgree} observed to agree, {readDiffer.size} to differ, {readIncomplete.foldl (fun sum (_, count) => sum + count) 0} incomplete"
  for (key, count) in readIncomplete do note s!"  {count} {key}"
  note s!"invariants of the trees: {violations.foldl (fun sum (_, count, _) => sum + count) 0} violations of {violations.size} kinds"
  for (kind, count, first) in violations do note s!"  {count} × {kind}; first: {first}"
  note s!"time: {(← IO.monoMsNow) - start} ms"
  for line in readDiffer do failure line
  for (kind, _, first) in violations do failure s!"an invariant of the trees is violated: {kind}: {first}"
  if readDiffer.isEmpty && violations.isEmpty then pass

end Zkc.Tests.Frontend
