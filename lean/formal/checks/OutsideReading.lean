import Zkc.Tests.Frontend.WrittenSubject

/-!
The reading of a module outside the file, on small modules written here.

A check of a subject does not rest on Lean's acceptance of a proof module: the module is
compiled to an object and read by `Zkc/Tools/Formal/VerifyPublication.lean` with the module that
the generator writes without the text (`WrittenSubject.readOutside`). This check gives that
program modules that Lean accepts and that it must refuse, each for the reason that the control
names, and one that it must accept:

- a published theorem that rests on an axiom of the module, passed through another theorem;
- a definition under the published proposition that is not the reference's;
- a published theorem of another proposition that holds as well;
- a module without the published theorem;
- a false proposition proved with the kernel's check turned off by the module;
- a definition under the proposition rewritten in the kernel's environment by a text that sets
  no option at all, with a proof of the proposition that is then true (Lean accepts the module:
  neither the generator's search for an option nor Lean's acceptance sees it);
- a declaration written over one of an import;
- a module that lacks an import of the reference.

One more module is refused by Lean itself, in the sandbox in which every module of a check is
elaborated: a text that writes a file outside its own folder (the program that reads the
object, the reference and the imports all stand outside it). It is given both ways in which a
check starts a module: as a proof module that is read outside, and as a control.

The reference imports nothing, so the program's own steps are what is run: the replay, the
comparison with the reference, and the walk of the proofs for axioms. A text's own imports are
not the reference's, and a module with them is accepted.
-/

open Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open Zkc.Tests.Frontend.WrittenSubject

namespace OutsideReading

/-- What the generator would state: a definition, and a proposition that uses it. -/
def stated (proposition : String) : String :=
  "namespace Fixture\ndef mark : Nat := 0\n" ++ s!"def gGoal : Prop := {proposition}\n"

/-- A module of the fixture: the statements, a text, and the published theorem. The text may
ask for imports, which the reference does not have; `needs` are imports of the reference. -/
def fixture (text : String) (mark := "0") (proposition := "mark = mark") (imports := "")
    (needs := "") : Module where
  text := imports ++
    (stated proposition).replace "def mark : Nat := 0" s!"def mark : Nat := {mark}" ++ text ++
    "\nend Fixture\n"
  theorems := []
  reference := needs ++ stated proposition ++ "end Fixture\n"
  published := [("Fixture.g_sound", "Fixture.gGoal")]

/-- The imports with which a text can reach the kernel's environment. -/
def metaImports : String := "import Lean\nimport Batteries.Tactic.OpenPrivate\n"

/-- A text that sets no option. It writes a declaration into the kernel's environment directly,
replacing what stands there under `name`, and then adds the published theorem with the proof
`proof`, which no check of the file reads against the old declaration. -/
def rewriting (name value proof : String) : String :=
  "open Lean Elab Command\n" ++
  "open private Lean.Environment.setCheckedSync from Lean.Environment\n" ++
  "open private Lean.Kernel.Environment.add from Lean.Environment\n" ++
  "run_cmd do\n" ++
  "  let env ← getEnv\n" ++
  "  let kernel := env.toKernelEnv\n" ++
  "  let some (.defnInfo found) := kernel.find? `Fixture.mark | throwError \"no mark\"\n" ++
  s!"  let written : DefinitionVal := \{ found with toConstantVal.name := `{name}, value := {value} }\n" ++
  "  let changed := Lean.Kernel.Environment.add kernel (.defnInfo written)\n" ++
  "  setEnv (Lean.Environment.setCheckedSync env changed)\n" ++
  "run_cmd do\n" ++
  "  let stated := mkConst `Fixture.gGoal\n" ++
  s!"  let proof := {proof}\n" ++
  "  liftCoreM <| addDecl (.thmDecl { name := `Fixture.g_sound, levelParams := [], type := stated, value := proof })\n"

/-- A module that Lean accepts and the reading outside refuses, saying `place` and `also`. -/
def refused (work : System.FilePath) (title : String) (module : Module) (place : String)
    (also : String := "") : IO Unit := do
  let outside ← readOutside (work / title) "Fixture" module
  unless outside.lean.1 do
    throw (IO.userError s!"{title}: Lean refused the module\n{outside.lean.2}")
  match outside.verified with
  | some (false, said) =>
    unless said.contains place && said.contains also do
      throw (IO.userError s!"{title}: refused outside the file for another reason\n{said}")
  | _ => throw (IO.userError s!"{title}: the module was accepted outside the file")

/-- A module that the reading outside accepts. -/
def accepted (work : System.FilePath) (title : String) (module : Module) : IO Unit := do
  let outside ← readOutside (work / title) "Fixture" module
  unless outside.lean.1 && outside.verified.map (·.1) == some true do
    throw (IO.userError s!"{title}: the module is refused\n{outside.lean.2}\n{outside.verified.map (·.2)}")

/-- A text that writes a file outside its own folder, in a proof module that is read outside:
the module is elaborated in a sandbox, and Lean stops at the write. The file is one that the
check itself made beside the module's folder, so that a sandbox that failed would harm
nothing. -/
def writtenOutside (work : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (work / "written")
  let target := (← IO.FS.realPath (work / "written")) / "beside.txt"
  IO.FS.writeFile target "as the check wrote it\n"
  let writing ← readOutside (work / "written") "Fixture"
    (fixture (s!"#eval IO.FS.writeFile {reprStr target.toString} \"rewritten by the text\"\n" ++
      "theorem g_sound : gGoal := rfl"))
  unless !writing.lean.1 && writing.lean.2.contains "read-only" &&
      (← IO.FS.readFile target) == "as the check wrote it\n" do
    throw (IO.userError s!"a text wrote a file outside its folder\n{writing.lean.2}")

/-- The same of a module that a check starts in the other way (a control, which also holds the
text): it is elaborated in the same sandbox. -/
def writtenByControl (work : System.FilePath) : IO Unit := do
  let beside := (← IO.FS.realPath work) / "beside.txt"
  IO.FS.writeFile beside "as the check wrote it\n"
  let (ok, said) ← finishLean (← startLakeLean work "Writer"
    s!"#eval IO.FS.writeFile {reprStr beside.toString} \"rewritten by the text\"\n")
  unless !ok && said.contains "read-only" && (← IO.FS.readFile beside) == "as the check wrote it\n" do
    throw (IO.userError s!"a module of a check wrote a file outside its folder\n{said}")

def run (work : System.FilePath) : IO Unit := do
  let cases : List (IO Unit) := [
    -- the module that is as the generator states it
    accepted work "honest" (fixture "theorem g_sound : gGoal := rfl"),
    -- a text with imports of its own, which the reference does not have, is read as any other
    accepted work "imported" (fixture "theorem g_sound : gGoal := rfl" (imports := metaImports)),
    refused work "axiom"
      (fixture "axiom extra : True\ntheorem helper : True := extra\ntheorem g_sound : gGoal := (fun _ : True => rfl) helper")
      "`Fixture.g_sound` rests on",
    refused work "definition"
      (fixture "theorem g_sound : gGoal := rfl" (mark := "1"))
      "`Fixture.mark` is not the declaration that the reference has: its value differs",
    refused work "proposition"
      (fixture "theorem g_sound : mark = mark := rfl")
      "`Fixture.g_sound` is not of the proposition `Fixture.gGoal`",
    refused work "missing"
      (fixture "theorem other : gGoal := rfl")
      "the candidate does not declare the theorem `Fixture.g_sound`",
    refused work "unchecked"
      (fixture ("set_option «debug».skipKernelTC true in\n" ++
        "theorem g_sound : gGoal := by\n  show (0 : Nat) = 1\n  decide +kernel") (proposition := "(0 : Nat) = 1"))
      "the kernel refuses a declaration of the candidate on replay" "Fixture.g_sound",
    refused work "rewritten"
      (fixture (rewriting "Fixture.mark" "mkNatLit 1"
        "mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1)") (proposition := "mark = 1")
        (imports := metaImports))
      "`Fixture.mark` is not the declaration that the reference has",
    refused work "overwritten"
      (fixture (rewriting "Nat.zero" "mkNatLit 1"
        "mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkConst `Fixture.mark)") (imports := metaImports))
      "the candidate declares `Nat.zero`, which an import has",
    refused work "unimported"
      (fixture "theorem g_sound : gGoal := rfl" (needs := "import Lean\n"))
      "the candidate does not import `Lean`, which the reference imports",
    writtenOutside work,
    writtenByControl work]
  -- at once: each case has a folder of its own
  let started ← cases.mapM fun case => IO.asTask case
  for task in started do
    IO.ofExcept task.get
  IO.println ("The reading outside the file accepts the module that is as stated, also with " ++
    "imports of its text, and refuses eight that Lean accepts: an axiom through another " ++
    "theorem, a definition that is not the reference's, another proposition, a missing " ++
    "theorem, a false proposition proved with the kernel's check turned off, a definition " ++
    "rewritten in the kernel's environment with no option set, a declaration written over an " ++
    "import's, and a module without an import of the reference. A text that writes a file " ++
    "outside its own folder is stopped by the sandbox in which every module of a check is " ++
    "elaborated, a control as a proof module.")

end OutsideReading

#eval show IO Unit from
  IO.FS.withTempDir fun work => OutsideReading.run work
