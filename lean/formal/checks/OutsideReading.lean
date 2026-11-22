import ZkcFormalTests.WrittenSubject

/-!
The judgment of a proof module, as the checks use it.

A check of a written subject does not rest on Lean's acceptance of a proof module: a text is
arbitrary Lean. It gives the proof modules that it accepts to `lake comparator`, with the
module of the statements and a challenge that the generator writes, in a project that is
settled so that a text has nothing to change (`ZkcFormalTests.SubjectProject`). The
comparator's own behaviour is the toolchain's to test. What is checked here is the use that the
checks make of it, through the functions by which every check has a module accepted
(`WrittenSubject.startModule`) or refused by the judgment (`WrittenSubject.readOutside`), on
pairs as the generator writes them: a module of statements with a definition and a proposition,
a challenge that states the published theorem with no proof, and a proof module that imports the
statements and holds a text.

- The pair that is as stated is accepted.
- A proof of another proposition under the published name, a proof module without the
  published theorem, and a theorem that rests on an axiom through another theorem are refused,
  each with its reason.
- A false proposition proved with the kernel's check turned off by the text, which Lean
  accepts, is refused by the kernel.
- A text that proves a false proposition from an axiom and, while Lean reads it, writes over
  its statements, its challenge, the exported challenge, the list of the pairs to judge, the
  verdict, and under a recipe a pair in the recipe's folder: every write fails, the files are as the check wrote them, and the pair is refused
  for its axiom.
- A text of another module of the same project that, while Lean reads it, replaces the objects
  of a pair (the statements with a true proposition, the proof module with a proof of it): the
  objects are replaced, and the pair is refused, since its challenge was exported before any
  text was read.
- A consumer that the check writes after the closing theorems is judged with the published
  theorems: after a text that turns the kernel's check off for what follows it, Lean accepts a
  false consumer, and the kernel of the judgment refuses it.
-/

open Zkc.Frontend.Written
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace OutsideReading

/-- A pair as the generator would write it, in the name space `name`: the statements are a
definition and the proposition `gGoal`, and the proof module holds `text`, which is to prove
`g_sound : gGoal`. -/
def pair (name text : String) (proposition := "mark = mark") : Module where
  space := name
  statementsName := .str (.str .anonymous name) "Stated"
  statements := s!"namespace {name}\ndef mark : Nat := 0\ndef gGoal : Prop := {proposition}\nend {name}\n"
  stated := []
  statedImports := []
  proof := s!"import {name}.Stated\nnamespace {name}\n{text}\nend {name}\n"
  proved := ["g_sound"]
  proofImports := []
  textLine := 3
  textLines := (text.splitOn "\n").length
  published := [(.str (.str .anonymous name) "g_sound", .str (.str .anonymous name) "gGoal")]

/-- A pair that the judgment must refuse, saying `reason`; Lean accepts its two modules. -/
def refused (work : System.FilePath) (name text reason : String) (proposition := "mark = mark") :
    IO (IO Unit) :=
  refusedOutside work name name (pair name text proposition) [reason]

/-- A text that proves its proposition from an axiom and tries each write that would have the
pair accepted: `targets`, each a file and what to write there. It says how many failed. -/
def writer (targets : List (System.FilePath × String)) : String :=
  "axiom cheat : False\n#eval show IO Unit from do\n  let mut failed := 0\n" ++
  String.join (targets.map fun (file, content) =>
    s!"  try IO.FS.writeFile {reprStr file.toString} {reprStr content}\n" ++
    "  catch _ => failed := failed + 1\n") ++
  "  IO.println s!\"writes that failed: {failed}\"\n" ++
  "theorem g_sound : gGoal := cheat.elim"

/-- A module that imports the proof module of the pair `Forged` and, while Lean reads it,
compiles a module of statements with a true proposition and a proof module with a proof of it
over the objects of the pair. It says how each compilation ended. -/
def forger : String :=
  "import Forged\n" ++
  "#eval show IO Unit from do\n" ++
  "  IO.FS.createDirAll \".lake/forge/Forged\"\n" ++
  "  IO.FS.writeFile \".lake/forge/Forged/Stated.lean\"\n" ++
  "    \"namespace Forged\\ndef mark : Nat := 0\\ndef gGoal : Prop := True\\nend Forged\\n\"\n" ++
  "  IO.FS.writeFile \".lake/forge/Forged.lean\"\n" ++
  "    \"import Forged.Stated\\nnamespace Forged\\ntheorem g_sound : gGoal := trivial\\nend Forged\\n\"\n" ++
  "  let objects := \".lake/build/lib/lean\"\n" ++
  "  let lean (object source : String) : IO UInt32 := do\n" ++
  "    let out ← IO.Process.output { cmd := \"lean\", args := #[\"-o\", s!\"{objects}/{object}\", source] }\n" ++
  "    return out.exitCode\n" ++
  "  let stated ← lean \"Forged/Stated.olean\" \".lake/forge/Forged/Stated.lean\"\n" ++
  "  let proved ← lean \"Forged.olean\" \".lake/forge/Forged.lean\"\n" ++
  "  IO.println s!\"objects replaced: {stated} {proved}\"\n"

/-- A pair with a consumer, as a check writes one after the closing theorems: the text turns
the kernel's check off for what follows it and makes `decide` decide by the kernel, so that
Lean accepts the consumer's false statement. -/
def consumed : Module :=
  let text := "theorem g_proof : gGoal := rfl\nset_option debug.skipKernelTC true\n" ++
    "macro_rules | `(tactic| decide) => `(tactic| decide +kernel)"
  let consumer : Consumer :=
    { name := "consumer", signature := "theorem consumer : mark = 1", proof := "by decide",
      imports := ["ZkcFormal.Written.WalkFees", "ZkcFormal.Written.FiniteModel"] }
  let plain := pair "Consumed" text
  { plain with
    proof := s!"import Consumed.Stated\nnamespace Consumed\n{text}\n" ++
      "theorem g_sound : gGoal := g_proof\n" ++ consumer.text ++ "end Consumed\n"
    proved := ["g_proof", "g_sound", "consumer"]
    consumers := [consumer] }

def run (work : System.FilePath) : IO Unit := do
  let project ← IO.FS.realPath work
  let project := projectOf project
  let honest ← startModule work "Honest" (pair "Honest" "theorem g_sound : gGoal := rfl")
  let proposition ← refused work "Proposition" "theorem g_sound : mark = mark := rfl"
    "Challenge and solution theorem statement do not match: 'Proposition.g_sound'"
  -- the solution is exported by the names that the judgment is of: the exporter does not
  -- find the name
  let missing ← refused work "Missing" "theorem other : gGoal := rfl"
    "Constant Missing.g_sound not found in environment"
  let axiom_ ← refused work "Axiom"
    "axiom extra : True\ntheorem helper : True := extra\ntheorem g_sound : gGoal := (fun _ : True => rfl) helper"
    "Illegal axiom detected: 'Axiom.extra'"
  let unchecked ← refused work "Unchecked"
    "set_option «debug».skipKernelTC true in\ntheorem g_sound : gGoal := by\n  show (0 : Nat) = 1\n  decide +kernel"
    "kernel rejected the solution" (proposition := "(0 : Nat) = 1")
  -- what the writer writes over: its statements and its challenge, the exported challenge,
  -- the verdict and the mark of a settled project, the list of the pairs to judge, and under a
  -- recipe the statements of another pair in the recipe's folder
  let shared ← (← IO.getEnv "ZKC_SUBJECTS").mapM fun folder => IO.FS.realPath folder
  let noted := shared.getD project / "accepted.txt"
  let trueStatements (name : String) := (pair name "" "True").statements
  let targets := [(project / "Writer" / "Stated.lean", trueStatements "Writer"),
    (project / "Writer" / "Challenge.lean", "import Writer.Stated\ntheorem Writer.g_sound : True := by sorry\n"),
    (project / "exports" / "WriterAlone.challenge.ndjson", ""),
    (project / "WriterAlone.verdict", "accepted"), (project / "settled", ""),
    (noted, "Writer.Challenge\tWriter\tWriter.g_sound\n")] ++
    (shared.map fun folder => (folder / "Honest" / "Stated.lean", trueStatements "Honest")).toList
  let writerPair := pair "Writer" (writer targets) "(0 : Nat) = 1"
  let writing ← readOutside work "Writer" writerPair
  let forgedPair := pair "Forged" "axiom cheat : False\ntheorem g_sound : gGoal := cheat.elim" "(0 : Nat) = 1"
  let forging ← readOutside work "Forged" forgedPair
  let forgerLean ← startLakeLean work "Forger" forger
  let consuming ← refusedOutside work "a false consumer after a text that turns the kernel's check off"
    "Consumed" consumed ["kernel rejected the solution"]

  let honestPair := pair "Honest" "theorem g_sound : gGoal := rfl"
  let notedBefore ← IO.FS.readFile noted

  let _ ← honest
  proposition
  missing
  axiom_
  unchecked
  -- the writer: Lean read it, every write failed, and the files are as the check wrote them
  let wrote ← writing
  unless wrote.lean.2.contains s!"writes that failed: {targets.length}" do
    throw (IO.userError s!"a text wrote a file outside the objects of its project\n{wrote.lean.2}")
  unless (← IO.FS.readFile (project / "Writer" / "Stated.lean")) == writerPair.statements do
    throw (IO.userError "a text changed its statements")
  unless (← IO.FS.readFile (project / "Writer" / "Challenge.lean")) == writerPair.challenge do
    throw (IO.userError "a text changed its challenge")
  unless (← IO.FS.readFile noted) == notedBefore do
    throw (IO.userError "a text changed the list of the pairs to judge")
  if let some folder := shared then
    unless (← IO.FS.readFile (folder / "Honest" / "Stated.lean")) == honestPair.statements do
      throw (IO.userError "a text changed the statements of a pair in the recipe's folder")
  wrote.refused "a text that writes over what it is judged by" "Writer" ["Illegal axiom detected: 'Writer.cheat'"]
  -- the forger: the objects of the pair are replaced, and the pair is refused all the same
  let (forgerOk, forgerSaid) ← forgerLean
  unless forgerOk && forgerSaid.contains "objects replaced: 0 0" do
    throw (IO.userError s!"the objects of a pair were not replaced: the control tests nothing\n{forgerSaid}")
  (← forging).refused "the objects of a pair replaced by another text" "Forged"
    ["Const does not match between challenge and target 'Forged.gGoal'"]
  consuming
  IO.println ("The judgment accepts the pair that is as stated, and refuses a proof of another " ++
    "proposition under the published name, a proof module without the published theorem, a " ++
    "theorem that rests on an axiom through another theorem, and a false proposition proved " ++
    "with the kernel's check turned off, each with its reason; a text that writes over its " ++
    "statements, its challenge, the exported challenge and the verdict has every write fail " ++
    "and is refused for its axiom; a pair whose objects another text replaced is refused, " ++
    "since its challenge was exported before any text was read; a consumer that a check " ++
    "wrote after a text is judged with the published theorems.")

end OutsideReading

#eval show IO Unit from
  IO.FS.withTempDir fun work => OutsideReading.run work
