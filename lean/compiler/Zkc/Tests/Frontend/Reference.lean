import Zkc.Tests.Frontend.Harness

/-!
# The sources and the conformance tests of the reference

Read from the reference directory given to the test driver (the directory that holds
`LANGUAGE.md`, `lib/`, `programs/` and `conformance/`).
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend.Syntax

/-- The tests of `conformance/` that the parser refuses, with the rule. Every other test parses.
The tests whose expectation names a lexical or grammar rule are among them; the others are
refused because their form has no production and the reference names a rule for it, or because
§5 restricts the production in prose (the kernel attribute, `spec` before a static parameter,
`using` after `external`). `T-F1` (an event in a `def`, FN1) parses: the productions of §5.5
admit it, and FN1 is a rule of §6 for the checker. -/
def expectedRefusals : Array (String × String) := #[
  ("R-FN5c", "FN5"), ("T-P8", "EV2"), ("T-P9", "RM1"), ("T-P10", "CT1"), ("T-P11", "HO3"),
  ("M-SCH5", "HO3"), ("T-L2", "LX3"), ("T-L3", "LX4"), ("T-L5", "LX5"), ("T-L8", "LX8"),
  ("T-L9", "LX7"), ("T-L10", "LX2"), ("T-P3", "GR2"), ("T-Z10b", "GR"), ("T-Z14", "GR6"),
  ("T-F3", "GR6"), ("S-K7", "GR6"), ("R-GR6a", "GR6"), ("R-GR6b", "GR6"), ("M-FRA9", "GR6"),
  ("R-NL9a", "NL9"), ("N-SP11d", "SP11"), ("N-NL9a", "NL9"), ("T-P5", "TY13"), ("S-K4", "TY13"),
  ("N-SX6f", "SX6"), ("R-SC5a", "SC5"), ("R-OR3a", "OR3"), ("N-E5", "NL9")]

def sortedFiles (directory : System.FilePath) (extension : String) : IO (Array System.FilePath) := do
  let files ← System.FilePath.walkDir directory
  let selected := files.filter (·.extension == some extension)
  return selected.qsort (·.toString < ·.toString)

/-- Every file of `lib/` and `programs/` parses, and its canonical text parses to the same tree. -/
def corpusSuite (reference : System.FilePath) : TestM Unit := do
  let mut count := 0
  for directory in [reference / "lib", reference / "programs"] do
    for path in ← sortedFiles directory "zkc" do
      count := count + 1
      let source ← IO.FS.readBinFile path
      match parse path.toString source with
      | .error error => failure s!"{path}: {error.render}"
      | .ok parsed =>
        pass
        checkPrinter path.toString parsed
        -- no annotation of these files is one that the formatter removes: their canonical
        -- text parses to the tree of the source itself
        expectTrue (treeText (canonicalize parsed.tree) == treeText parsed.tree)
          s!"{path}: the canonical tree differs from the tree of the source"
  note s!"{count} files of lib/ and programs/"
  expectTrue (count == 44) s!"expected the 44 files of the reference, found {count}"

/-- Every program of `conformance/`: a test whose expected refusal is a lexical or grammar rule
is refused by that rule, every refusal is by a rule that its test names, and the refused tests
are exactly `expectedRefusals`. The printer keeps the tree of every program that parses. -/
def conformanceSuite (reference : System.FilePath) : TestM Unit := do
  let mut total := 0
  let mut parsedCount := 0
  let mut refused : Array (String × String) := #[]
  let mut leftToChecker : Array String := #[]
  for path in ← sortedFiles (reference / "conformance") "txt" do
    for block in readBlocks (← IO.FS.readFile path) do
      total := total + 1
      let rules := refusalRules block.expect
      let expected := expectedRefusals.find? (·.1 == block.id)
      match parseBlock block with
      | .ok files =>
        parsedCount := parsedCount + 1
        if rules.any isLexicalOrGrammarRule then
          failure s!"{block.id}: parses, but its test expects `{block.expect}`"
        else if let some (_, rule) := expected then
          failure s!"{block.id}: parses, but is expected to be refused by {rule}"
        else
          pass
          if !rules.isEmpty then leftToChecker := leftToChecker.push block.id
        for index in [0:files.size] do
          checkPrinter s!"{block.id}.{index}" files[index]!
      | .error error =>
        refused := refused.push (block.id, error.rule)
        if !rules.contains error.rule then
          failure s!"{block.id}: expects `{block.expect}`; refused: {error.render}"
        else if expected.map (·.2) != some error.rule then
          failure s!"{block.id}: refused by {error.rule}, which `expectedRefusals` does not list"
        else pass
  for (id, rule) in expectedRefusals do
    unless refused.any (·.1 == id) do failure s!"{id}: expected to be refused by {rule}; not found"
  note s!"{total} conformance tests: {parsedCount} parse, {refused.size} are refused"
  note s!"{leftToChecker.size} tests that expect a refusal by a rule of the checker parse"
  expectTrue (total == 502) s!"expected 502 conformance tests, found {total}"

end Zkc.Tests.Frontend
