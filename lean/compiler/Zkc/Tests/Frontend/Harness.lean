import Zkc.Frontend

/-!
# Test harness

Checks that record a failure and carry on, counted per suite; and the reader of the block
format of the conformance tests (`=== ID | expect | note`, then the program, with `--- file`
between the modules of one test).
-/

namespace Zkc.Tests.Frontend

open Zkc.Frontend.Syntax

structure Tally where
  passed : Nat := 0
  failed : Nat := 0
  failures : Array String := #[]
  notes : Array String := #[]

abbrev TestM := StateT Tally IO

def pass : TestM Unit := modify fun t => { t with passed := t.passed + 1 }

def failure (message : String) : TestM Unit :=
  modify fun t => { t with failed := t.failed + 1, failures := t.failures.push message }

def note (message : String) : TestM Unit := modify fun t => { t with notes := t.notes.push message }

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

/-- Runs a suite and prints its summary; the failures are listed. -/
def runSuite (name : String) (suite : TestM Unit) : IO Tally := do
  let ((), tally) ← suite.run {}
  IO.println s!"{name}: {tally.passed} checks passed, {tally.failed} failed"
  for message in tally.notes do IO.println s!"  {message}"
  for message in tally.failures do IO.println s!"  FAIL {message}"
  return tally

end Zkc.Tests.Frontend
