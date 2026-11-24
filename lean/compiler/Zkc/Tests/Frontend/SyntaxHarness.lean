import Zkc.Frontend.Syntax.Format
import Zkc.Frontend.Syntax.Dump

/-!
# Test harness

Checks that record a failure and carry on, counted per suite; and the reader of the block
format of the conformance tests (`=== ID | expect | note`, then the program, with `--- file`
between the modules of one test).
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend.Syntax

/-- The two report classes for a reached body that has no package of its own. -/
inductive UnpackagedOutcome where
  | waiting (reason : String)
  | typedOnly (reason : String)
  deriving BEq

def UnpackagedOutcome.describe : UnpackagedOutcome → String
  | .waiting reason => s!"waiting for {reason}"
  | .typedOnly reason => s!"typed only: {reason}"

structure UnpackagedRoot where
  block : String
  declaration : String
  instanceName : String
  outcome : UnpackagedOutcome

/-- An instance uses its qualified source description, including its arguments and owner.
A family counts reports of one qualified declaration in one block. -/
inductive ExpectedInstances where
  | one (instanceName : String)
  | family (declaration : String) (count : Nat)

structure ExpectedRoot where
  block : String
  instances : ExpectedInstances
  outcome : UnpackagedOutcome

private def ExpectedRoot.matches (expected : ExpectedRoot) (root : UnpackagedRoot) : Bool :=
  expected.block == root.block && expected.outcome == root.outcome && match expected.instances with
    | .one name => name == root.instanceName
    | .family name _ => name == root.declaration

structure Tally where
  admittedRoots : Nat := 0
  unpackagedRoots : Array UnpackagedRoot := #[]
  passed : Nat := 0
  failures : Array String := #[]
  notes : Array String := #[]

abbrev TestM := StateT Tally IO

def pass : TestM Unit := modify fun t => { t with passed := t.passed + 1 }

def failure (message : String) : TestM Unit :=
  modify fun t => { t with failures := t.failures.push message }

def note (message : String) : TestM Unit := modify fun t => { t with notes := t.notes.push message }

/-- Compare the multiset for the entire suite, including blocks which no longer reach typing.
An excess report names the actual instance. A deficit names the expected instance or family. -/
def checkExpectedRoots (expected : List ExpectedRoot) (blocks : Array String) : TestM Unit := do
  for block in (expected.map (·.block)).eraseDups do
    if blocks.count block > 1 then failure s!"ambiguous root expectations: several blocks named {block}"
  let tally ← get
  -- Reserve an exact instance before using a family allowance for the same declaration.
  let (exact, families) := expected.partition fun entry => entry.instances matches .one _
  let mut entries := (exact ++ families).toArray.map fun entry =>
    let count := match entry.instances with
      | .one _ => 1
      | .family _ count => count
    (entry, count)
  for root in tally.unpackagedRoots do
    if let some i := entries.findIdx? (fun (entry, left) => left > 0 && entry.matches root) then
      entries := entries.modify i fun (entry, left) => (entry, left - 1)
      pass
    else failure s!"{root.block}: unexpected {root.instanceName}: {root.outcome.describe}"
  for (entry, remaining) in entries do
    let name := match entry.instances with
      | .one instanceName => instanceName
      | .family declaration count => s!"{declaration} (family of {count})"
    let message := s!"{entry.block}: {name}: {entry.outcome.describe}"
    if remaining > 0 then failure s!"{message}; missing {remaining} expected"
    else note message
  let waiting := tally.unpackagedRoots.countP (fun r => r.outcome matches .waiting _)
  note s!"package reports in typing blocks: {tally.admittedRoots} admitted, {waiting} waiting, {tally.unpackagedRoots.size - waiting} typed only"

/-- The directories of the repository that the tests read: the reference of the language
(`language/`, which holds `LANGUAGE.md` and `conformance/`), the library in source
(`libraries/`, a module `zkc::a::b` at `zkc/a/b.zkc`) and the worked programs (`examples/`, with
the modules they share in `examples/support/`). -/
structure Repository where
  language : System.FilePath
  libraries : System.FilePath
  examples : System.FilePath

/-- The conformance tests of the reference. -/
def Repository.conformance (repository : Repository) : System.FilePath :=
  repository.language / "conformance"

/-- The independent conformance suite. -/
def Repository.independent (repository : Repository) : System.FilePath :=
  repository.conformance / "independent"

/-- The cases of the independent suite that the reference accepts since a fact is about a
value and not about a name. The suite was written from the reference before that amendment,
and its files are not changed: each of these expects a refusal of a rule of facts about a
`mut` name, and is accepted. -/
def acceptedSinceFactsAreAboutValues : Array (String × String) := #[
  ("facts-mut-guard", "a guard on a `mut` name, then its use at `index<8>`: the name is the value that the guard tested"),
  ("loop-mut-size-guard", "a guard on the size of a `mut` collection: the name is the value that the guard tested")]

def expectTrue (condition : Bool) (message : String) : TestM Unit :=
  if condition then pass else failure message

/-- One test of the block format. -/
structure Block where
  id : String
  expect : String
  note : String
  files : Array String
  deriving Inhabited

def trimSpaces (text : String) : String :=
  let isSpace (c : Char) := c == ' ' || c == '\t' || c == '\r'
  String.ofList ((text.toList.dropWhile isSpace).reverse.dropWhile isSpace).reverse

/-- Drops the empty lines at the start and at the end, and ends the text with one line end. -/
def stripBlankLines (lines : Array String) : String :=
  let start := (lines.findIdx? (· != "")).getD lines.size
  let stop := match (lines.reverse.findIdx? (· != "")) with
    | some k => lines.size - k
    | none => start
  String.intercalate "\n" (lines.extract start stop).toList ++ "\n"

/-- The blocks of a file in the block format; the lines before the first block are a heading. -/
def readBlocks (text : String) : Array Block := Id.run do
  let mut blocks : Array Block := #[]
  let mut current : Option (String × String × String) := none
  let mut files : Array String := #[]
  let mut lines : Array String := #[]
  for line in text.splitOn "\n" do
    if line.startsWith "=== " then
      if let some (id, expect, blockNote) := current then
        blocks := blocks.push { id, expect, note := blockNote, files := files.push (stripBlankLines lines) }
      let fields := ((String.ofList (line.toList.drop 4)).splitOn "|").map trimSpaces
      current := some (fields.getD 0 "", fields.getD 1 "", fields.getD 2 "")
      files := #[]
      lines := #[]
    else if current.isSome ∧ trimSpaces line == "--- file" then
      files := files.push (stripBlankLines lines)
      lines := #[]
    else
      lines := lines.push line
  if let some (id, expect, blockNote) := current then
    blocks := blocks.push { id, expect, note := blockNote, files := files.push (stripBlankLines lines) }
  return blocks

/-- The rules that an expectation `refuse R S …` names. -/
def refusalRules (expect : String) : List String :=
  match expect.splitOn " " |>.filter (· != "") with
  | "refuse" :: rules => rules
  | _ => []

/-- The tests of layer A whose outcome contradicts what they expect and is known, each with the
reason. A contradiction not listed here fails the run. -/
def knownContradictions : Array (String × String) := #[]

/-- Whether a refusal by `rule` contradicts what a test expects: acceptance, or a refusal by other
rules than the one named and its stated alternatives. -/
def contradicts (expect : String) (rule : String) : Bool :=
  expect.startsWith "accept" || !(refusalRules expect).contains rule

/-- Reports the contradictions of a suite under their own heading: each fails unless it is known,
with its reason. -/
def reportContradictions (contradictions : Array (String × String)) : TestM Unit := do
  if contradictions.isEmpty then return
  note s!"contradictions: {contradictions.size}"
  for (id, text) in contradictions do
    match knownContradictions.find? (·.1 == id) with
    | some (_, reason) => note s!"contradiction, known: {text}; {reason}"
    | none => failure s!"contradiction: {text}"

def isLexicalOrGrammarRule (rule : String) : Bool :=
  rule.startsWith "LX" || rule.startsWith "GR"

/-- Parses every module of a test; the first refusal, if any. -/
def parseBlock (block : Block) : Except SyntaxError (Array SourceFile) :=
  block.files.mapIdxM fun index text => parseString s!"{block.id}.{index}" text

def treeText (tree : File) : String := dumpFile tree (withSpans := false)

def commentTexts (comments : Array Comment) : Array String := comments.map (·.text)

/-- The checks of the printer on a parsed source:
1. the printed tree parses to the same tree (up to spans);
2. the canonical text parses to the canonical tree;
3. formatting the canonical text gives it back byte for byte;
4. the comments are kept, in order. -/
def checkPrinter (label : String) (parsed : SourceFile) : TestM Unit := do
  let printed := printFile parsed.tree parsed.comments
  match parseString s!"{label} (printed)" printed with
  | .error error => failure s!"{label}: the printed text is refused: {error.render}"
  | .ok again =>
    expectTrue (treeText again.tree == treeText parsed.tree)
      s!"{label}: the printed text parses to another tree"
  let canonical := formatSourceFile parsed
  match parseString s!"{label} (canonical)" canonical with
  | .error error => failure s!"{label}: the canonical text is refused: {error.render}"
  | .ok again =>
    expectTrue (treeText again.tree == treeText (canonicalize parsed.tree))
      s!"{label}: the canonical text parses to another tree than the canonical tree"
    expectTrue (formatSourceFile again == canonical)
      s!"{label}: formatting the canonical text changes it"
    expectTrue (commentTexts again.comments == commentTexts parsed.comments)
      s!"{label}: the canonical text does not keep the comments"

/-- One specific diagnostic expected from one case in one suite. -/
structure KnownFailure where
  suite : String
  caseName : String
  detail : String
  reason : String
  deriving BEq

structure TestCounts where
  passed : Nat := 0
  known : Nat := 0
  failed : Nat := 0

/-- Each entry accounts for one occurrence. Check the remaining entries after all suites,
so that removing or renaming a suite also exposes its stale entries. -/
def runSuites (suites : List (String × TestM Unit)) (knownFailures : List KnownFailure := []) :
    IO TestCounts := do
  let mut remaining := knownFailures
  let mut totals : TestCounts := {}
  for (name, suite) in suites do
    let ((), tally) ← suite.run {}
    let mut known := 0
    for message in tally.notes do IO.println s!"  {name}: {message}"
    for message in tally.failures do
      match remaining.find? (fun entry =>
          entry.suite == name && message == s!"{entry.caseName}: {entry.detail}") with
      | some entry =>
        remaining := remaining.erase entry
        known := known + 1
        IO.println s!"  KNOWN {name}: {message}. {entry.reason}"
      | none => IO.println s!"  FAIL {name}: {message}"
    let failed := tally.failures.size - known
    IO.println s!"{name}: {tally.passed} checks passed, {known} known failures, {failed} failed"
    totals := ⟨totals.passed + tally.passed, totals.known + known, totals.failed + failed⟩
  for entry in remaining do
    IO.println s!"  FAIL {entry.suite}: {entry.caseName}: {entry.detail} did not occur; remove the known-failure entry"
  return { totals with failed := totals.failed + remaining.length }

end Zkc.Tests.Frontend
