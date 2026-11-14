import Zkc.Tests.Frontend.Independent
import Zkc.Tests.Frontend.TypingReference
import Zkc.Tests.Frontend.ProtocolRuns
import Zkc.Tools.Frontend.Differential
import Zkc.Tests.Frontend.Generators

/-!
# Differential runs over the corpus

The corpus is every program whose roots the frontend emits: each module of `lib/`, each worked
program of `programs/` with its example file (an example file without a program on its own),
the generated program, every test of layer A of the conformance and every case of the
independent suite that the frontend accepts, the test modules of the generators of true
statements (`Generators`) and the programs of the run tests of protocols (`ProtocolRuns`). A
protocol root that has a generator is run on its statements. A **baseline** is what one commit of
the frontend emitted for the corpus, in a directory outside the repository: a directory per
program (`Zkc.Tools.Frontend.Differential.writeBaseline`) and `programs.json`, which lists the
programs written.

- `--write-baseline <dir>` writes the baseline of the corpus there and runs nothing else.
- `--baseline <dir>`, or `ZKC_DIFFERENTIAL_BASELINE=<dir>`, compares every program of the corpus
  with the baseline, root by root: identical text and tables of sites, or observed to agree
  when run under the seeds, or observed to differ with the seed, the inputs and the role that
  show it, or incomplete with why. A root or a
  program of the baseline that the frontend no longer emits, and a root that differs, are
  failures; the counts and the reasons for which roots cannot be run are noted.
- Of the roots of the generated program whose text differs, one function root in
  `generatedFunctionSpacing` and one protocol root in `generatedProtocolSpacing` is run; the
  others are counted as sampled out.
- `--compare-by-runs` runs the packages also when their text is identical; `--every-root` samples
  nothing.
- `--mutants` also gives the mutant score: for every root of the library modules and the
  worked programs, and for one root in `mutantSpacing` of the others, mutants of its package
  are compared with it by runs; the score and the survivors are noted.
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend
open Zkc.Frontend.Syntax
open Zkc.Tools.Frontend.Differential

/-- A program of the corpus: its identifier, its files, and the loader of its library. -/
structure CorpusProgram where
  id : String
  inputs : Array SourceInput
  load : Array String → IO (Option SourceInput)

/-- The group of a program: the part of its identifier before the first `/`. -/
def CorpusProgram.group (program : CorpusProgram) : String :=
  (program.id.splitOn "/").headD program.id

/-- The programs of the corpus, in a fixed order. -/
def corpusPrograms (reference : System.FilePath) (independent : Option System.FilePath) :
    IO (Array CorpusProgram) := do
  let library ← cachedLoader #[reference / "lib"]
  let programs := reference / "programs"
  let withPrograms ← cachedLoader #[reference / "lib", programs, programs / "support"]
  let mut corpus : Array CorpusProgram := #[]
  let readFile (file : System.FilePath) : IO SourceInput := do
    return { name := file.toString, parsed := parse file.toString (← IO.FS.readBinFile file) }
  -- the modules of the library
  for path in ← sortedFiles (reference / "lib") "zkc" do
    let relative := ((path.toString.drop ((reference / "lib").toString.length + 1)).dropEnd 4).toString
    corpus := corpus.push { id := s!"lib/{relative}", inputs := #[← readFile path]
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
    corpus := corpus.push { id := s!"programs/{stem}", inputs := ← files.mapM readFile
                            load := fun names => withPrograms names }
  -- the generated program
  let generated := Zkc.Tools.Frontend.Generate.program 50000
  corpus := corpus.push { id := "generated"
                          inputs := #[{ name := "generated", parsed := parseString "generated" generated }]
                          load := fun names => library names }
  -- the tests of layer A
  for path in ← sortedFiles (reference / "conformance") "txt" do
    unless (path.fileName.getD "").startsWith "layer-a-" do continue
    for block in readBlocks (← IO.FS.readFile path) do
      let .ok files := parseBlock block | continue
      let inputs := (List.range files.size).toArray.map fun index =>
        ({ name := s!"{block.id}.{index}", parsed := .ok files[index]! } : SourceInput)
      corpus := corpus.push { id := s!"conformance/{block.id}", inputs, load := fun names => library names }
  -- the cases of the independent suite
  if let some directory := independent then
    if let .ok cases ← readIndependentCases directory then
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

/-- The directory of a program in a baseline: its identifier, every character other than a
letter, a digit, `-`, `_`, `.` and `/` written `_`. -/
def programDirectory (baseline : System.FilePath) (id : String) : System.FilePath :=
  baseline / String.ofList (id.toList.map fun char =>
    if char.isAlphanum || "-_./".contains char then char else '_')

/-- Writes the baseline of the corpus: a directory per program that the frontend emits, and
`programs.json`, the list of the programs written. -/
def writeCorpusBaseline (baseline : System.FilePath) (reference : System.FilePath)
    (independent : Option System.FilePath) : IO UInt32 := do
  let mut written : Array Zkc.Json := #[]
  let mut roots := 0
  let mut schemes := 0
  for program in ← corpusPrograms reference independent do
    let .ok emission ← emit program.inputs program.load | continue
    if emission.roots.isEmpty && emission.schemes.isEmpty && emission.lacking.isEmpty then continue
    writeBaseline (programDirectory baseline program.id) emission
    written := written.push (.str program.id)
    roots := roots + emission.roots.size
    schemes := schemes + emission.schemes.size
  IO.FS.writeFile (baseline / "programs.json") ((Zkc.Json.arr written).render ++ "\n")
  IO.println s!"baseline written to {baseline}: {written.size} programs, {roots} roots, {schemes} schemes"
  return 0

/-- The kind of a reason why a root cannot be run, for the counts: the reason without its
numbers and details. -/
def reasonKey (reason : String) : String :=
  let has (text : String) : Bool := (reason.splitOn text).length > 1
  if reason.startsWith "a run of about" then "a run above the bound of operations"
  else if reason.startsWith "inputs and outputs of" then "inputs and outputs above the bound of numbers"
  else if has "has no entry in the table of sites" then "a site without an entry in the table of sites"
  else if has "is not a row of the vocabulary" then "a row that is not the vocabulary's at its arguments"
  else if has "has no implementation in the model" then "a row that the model does not compute"
  else if has "has no values that the model of the vocabulary computes" then
    "a type whose values the model does not compute"
  else match reason.splitOn ": " with
    | "not complete" :: why :: _ => s!"not complete: {why}"
    | first :: _ => first
    | [] => reason

/-- How the differential suite runs. -/
structure DifferentialOptions where
  baseline : System.FilePath
  byRuns : Bool := false
  everyRoot : Bool := false
  mutants : Bool := false
  /-- The runs are under the provider of uninterpreted rows. -/
  uninterpreted : Bool := false

/-- One function root in this many of the generated program, and one protocol root in
`generatedProtocolSpacing`, is run when its text differs: the program is one unit of
declarations repeated with another number, so every form of it is in every sample; and the
runs of its protocols each compute about a dozen multiplications of points of G1, and validate
the points of its inputs, by another. -/
def generatedFunctionSpacing : Nat := 10

def generatedProtocolSpacing : Nat := 25

/-- One root in this many of the programs other than the library and the worked programs gets
mutants. -/
def mutantSpacing : Nat := 40

/-- The changes of a root, before admission, of which its mutants are made. -/
def mutantCandidates : Nat := 24

/-- A protocol whose verifier draws two challenges and returns them. -/
def twoDrawsProgram : String := "module two_draws
type F = primitive(\"bls12-381.fr\")
protocol TwoDraws roles(P, V)(x: F @(P, V)) -> (first: F @(P, V), second: F @(P, V)):
    c <- draw F from V to P
    d <- draw F from V to P
    return (c + x, d)
"

/-- The text of a package with the sites `a` and `b` of its draws, samples and applications
exchanged: the same protocol, its sites numbered otherwise. -/
partial def exchangeSites (a b : Nat) : Zkc.Json → Zkc.Json
  | .arr items =>
    let position := match items[0]? with
      | some (.str "draw") | some (.str "apply") => some 3
      | some (.str "sample") => some 2
      | _ => none
    let items := items.map (exchangeSites a b)
    let exchange : Zkc.Json → Zkc.Json
      | .num n => .num (if n == a then b else if n == b then a else n)
      | other => other
    .arr (match position with
      | some index => items.modify index exchange
      | none => items)
  | other => other

/-- Coins are keyed by the event of the source that the table of sites gives for a site: the
protocol of two draws with the numbers of its two sites exchanged, and the rows of its table
exchanged alike, is observed to agree with the original; with the original's table its two coins are
exchanged and it is different; with a table that lacks the row of a site it reaches, it
cannot be run. -/
def keyingSuite : TestM Unit := do
  let emitted ← emit #[{ name := "two_draws", parsed := parseString "two_draws" twoDrawsProgram }]
    fun names => pure (Id.run (memoryLoader nameLibrary names))
  let emission ← match emitted with
    | .ok emission => pure emission
    | .error message => do failure s!"two draws: {message}"; return
  let some (_, package) := emission.roots[0]?
    | failure "two draws: no root"
  let some (name, rows) := emission.sites[0]?
    | failure "two draws: no table of sites"
  let some first := rows[0]? | failure "two draws: no site 0"
  let some second := rows[1]? | failure "two draws: no site 1"
  let exchanged ← match Zkc.Core.Raw.parsePackage
      (Zkc.Json.render (exchangeSites 0 1 (Zkc.Core.Raw.printPackage package))) with
    | .ok exchanged => pure exchanged
    | .error message => do failure s!"two draws: {message}"; return
  expectTrue (packageText exchanged != packageText package)
    "two draws: the sites exchanged change the text"
  let settings : Settings := {}
  expectTrue (compareRoot settings package exchanged emission.sites #[(name, #[second, first])]
      matches .agree _)
    "two draws: renumbered with the table, observed to agree"
  expectTrue (compareRoot settings package exchanged emission.sites emission.sites
      matches .differ ..)
    "two draws: renumbered without the table, observed to differ"
  expectTrue (compareRoot settings package exchanged emission.sites #[(name, #[second])]
      matches .incomplete (.cannotRun _))
    "two draws: a site without a row cannot be run"
  -- a table that gives two sites one key: the two would get the same coins
  expectTrue (compareRoot settings package package emission.sites #[(name, #[first, first])]
      matches .incomplete (.cannotRun _))
    "two draws: a table that names a key twice cannot be compared"
  -- the same text is the same program only with the same table of sites
  let baseline : Baseline :=
    { roots := emission.roots.map fun (description, package) => (description, packageText package, package)
      schemes := #[], sites := #[(name, #[second, first])], lacking := #[] }
  let swapped ← compareProgram settings "two draws" baseline emission
  expectTrue (swapped.found.all fun (_, found) => found matches .differ ..)
    "two draws: the same text with another table of sites is run, and observed to differ"
  let same ← compareProgram settings "two draws"
    { baseline with sites := emission.sites } emission
  expectTrue (same.found.all fun (_, found) => found matches .identical)
    "two draws: the same text with the same table of sites is identical"
  -- without a seed nothing is observed
  expectTrue ((← underBudget { settings with seeds := [] } fun seeds =>
      compareRoot { settings with seeds } package package emission.sites emission.sites)
      matches .incomplete .noSeed)
    "two draws: without a seed the comparison is incomplete"

/-- A function with a branch that no input takes: its condition is a product with zero. -/
def unreachedProgram : String := "module unreached
type F = primitive(\"bls12-381.fr\")
def branch(x: F, z: F) -> F:
    mut y = x
    if x * 0 != 0:
        y := y * z + 3
    return y + z
"

/-- A mutant that survives is unreached when no seed reaches its instruction, and is to be read
otherwise. The mutants of a branch that no input takes are unreached. A change of the product
with zero is reached and changes nothing that is seen: it is to be read. -/
def reachSuite : TestM Unit := do
  let emitted ← emit #[{ name := "unreached", parsed := parseString "unreached" unreachedProgram }]
    fun names => pure (Id.run (memoryLoader nameLibrary names))
  let emission ← match emitted with
    | .ok emission => pure emission
    | .error message => do failure s!"unreached: {message}"; return
  let some (_, package) := emission.roots[0]? | failure "unreached: no root"
  let settings : Settings := {}
  let score ← mutantScore settings "branch" package emission.sites 200 (mutantRootBudget settings)
  expectTrue (score.unreached.size > 0 && score.killed > 0)
    s!"unreached: {score.describe}"
  expectTrue (score.survivors.any fun survivor => (survivor.splitOn "instruction 1:").length > 1)
    s!"unreached: survivors to be read: {score.survivors.toList}"
  expectTrue (score.unreached.all fun survivor => (survivor.splitOn "instruction 1:").length == 1)
    s!"unreached: {score.unreached.toList}"

def differentialSuite (options : DifferentialOptions) (reference : System.FilePath)
    (independent : Option System.FilePath) : TestM Unit := do
  let start ← IO.monoMsNow
  let listed ← match Zkc.Json.parse (← IO.FS.readFile (options.baseline / "programs.json")) with
    | .ok (.arr items) => pure (items.filterMap fun | .str id => some id | _ => none)
    | _ => do failure s!"{options.baseline} has no list of programs"; return
  let settings : Settings :=
    { byRunsOnly := options.byRuns
      provider := if options.uninterpreted then Zkc.Core.UninterpretedRows.provider
        else Zkc.Core.RunComparison.arithmetic }
  let mut times : Array (String × Nat) := #[]
  let mut comparisons : Array Comparison := #[]
  let mut seen : Array String := #[]
  let mut reasons : Array (String × Nat) := #[]
  let mut groups : Array (String × Array Comparison) := #[]
  let mut score : Score := {}
  let mut workedScore : Score := {}
  let mut otherRoots := 0
  let mut structures := 0
  for program in ← corpusPrograms reference independent do
    let emitted ← emit program.inputs program.load
    let inBaseline := listed.contains program.id
    match emitted with
    | .error message =>
      if inBaseline then failure s!"{program.id}: in the baseline, and now {message}"
      continue
    | .ok emission =>
      if emission.roots.isEmpty && emission.schemes.isEmpty && emission.lacking.isEmpty then
        if inBaseline then failure s!"{program.id}: in the baseline, and now emits nothing"
        continue
      unless inBaseline do
        comparisons := comparisons.push
          { program := program.id, found := emission.roots.map fun (name, _) => (name, .added) }
        continue
      seen := seen.push program.id
      let baseline ← match ← readBaseline (programDirectory options.baseline program.id) with
        | .ok baseline => pure baseline
        | .error message => do failure s!"{program.id}: {message}"; continue
      let begun ← IO.monoMsNow
      let programSettings := if program.id == "generated" && !options.everyRoot then
        { settings with functionSpacing := generatedFunctionSpacing
                        protocolSpacing := generatedProtocolSpacing } else settings
      -- a protocol root that has a generator is run on true statements
      let programSettings := { programSettings with
        generators := generatorsOf ((program.id.splitOn "/").getLastD "") }
      -- what each definition does, against the baseline: this comparison does not run a program
      -- and does not depend on how a body is written
      for change in digestChanges baseline emission do failure s!"{program.id}: {change}"
      structures := structures + (baseline.digests.map (·.size)).getD 0
      let comparison ← compareProgram programSettings program.id baseline emission
      let spent := (← IO.monoMsNow) - begun
      times := match times.findIdx? (·.1 == program.group) with
        | some index => times.modify index fun (group, total) => (group, total + spent)
        | none => times.push (program.group, spent)
      for (root, found) in comparison.found do
        match found with
        | .differ .. | .missing _ => failure s!"{program.id}: {root}: {found.describe}"
        | .incomplete (.cannotRun reason) =>
          let key := reasonKey reason
          reasons := match reasons.findIdx? (·.1 == key) with
            | some index => reasons.modify index fun (text, count) => (text, count + 1)
            | none => reasons.push (key, 1)
        | _ => pure ()
      comparisons := comparisons.push comparison
      groups := match groups.findIdx? (·.1 == program.group) with
        | some index => groups.modify index fun (name, list) => (name, list.push comparison)
        | none => groups.push (program.group, #[comparison])
      if options.mutants then
        let worked := program.group == "lib" || program.group == "programs"
        for (description, _, package) in baseline.roots do
          let chosen := worked || otherRoots % mutantSpacing == 0
          unless worked do otherRoots := otherRoots + 1
          unless chosen do continue
          let found ← mutantScore settings s!"{program.id}: {description}" package baseline.sites
            mutantCandidates (mutantRootBudget settings)
            (generatorOf programSettings (baseline.roots.map fun (name, _, package) => (name, package))
              description)
          score := score.add found
          if worked then workedScore := workedScore.add found
  for id in listed do
    unless seen.contains id do failure s!"{id}: in the baseline, and not in the corpus now"
  if comparisons.all (!·.failed) then pass
  note s!"{comparisons.size} programs compared with {options.baseline}: {tally comparisons}"
  note s!"what each definition does, by its digest: {structures} definitions and roles of the baseline compared"
  for (group, list) in groups do
    let spent := ((times.find? (·.1 == group)).map (·.2)).getD 0
    note s!"  {group}: {list.size} programs; {tally list}; compared in {spent} ms"
  -- how many seeds the roots observed to agree were run under, within the budget of a root
  let mut bySeeds : Array (Nat × Nat) := #[]
  for comparison in comparisons do
    for (_, found) in comparison.found do
      if let .agree seeds := found then
        bySeeds := match bySeeds.findIdx? (·.1 == seeds) with
          | some index => bySeeds.modify index fun (count, total) => (count, total + 1)
          | none => bySeeds.push (seeds, 1)
  let sortedBySeeds := bySeeds.qsort (·.1 > ·.1)
  unless sortedBySeeds.isEmpty do
    note s!"roots observed to agree, by the seeds they were run under: {", ".intercalate (sortedBySeeds.toList.map fun (seeds, count) => s!"{count} under {seeds}")}"
  for (reason, count) in reasons do note s!"cannot be run, {count} roots: {reason}"
  for comparison in comparisons do
    for (root, found) in comparison.found do
      if found matches .incomplete _ then
        if ["lib", "programs"].any (comparison.program.startsWith ·) then
          note s!"incomplete: {comparison.program}: {root}: {found.describe}"
  if options.mutants then
    note s!"mutants: {score.describe}"
    note s!"mutants of the library and the worked programs: {workedScore.describe}"
    for survivor in workedScore.survivors do note s!"survives, to be read: {survivor}"
    for survivor in workedScore.unreached do note s!"survives, unreached: {survivor}"
    note s!"survivors of the other programs: {score.survivors.size - workedScore.survivors.size} to be read, {score.unreached.size - workedScore.unreached.size} unreached"
    for (mutant, reason) in score.incomplete.extract 0 20 do note s!"mutant incomplete: {mutant}: {reason}"
  note s!"time: {(← IO.monoMsNow) - start} ms"

end Zkc.Tests.Frontend
