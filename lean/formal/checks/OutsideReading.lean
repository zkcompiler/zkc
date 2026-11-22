import Zkc.Tests.Formal.WrittenSubject

/-!
The reading of a module outside the file, on small modules written here.

A check of a subject does not rest on Lean's acceptance of a proof module: the module of the
statements is compiled with no text, the proof module is compiled against it, and the object of
the proof module is read by `Zkc/Tools/Formal/VerifyPublication.lean`
(`WrittenSubject.readOutside`). This check gives that program modules that Lean accepts and
that it must refuse, each for the reason that the control names, and three that it must accept
(the module as stated; a text with imports of its own; a text with an `unsafe` and a `partial`
definition and a type of two constructors, whose code the replay leaves out, and with a name
that contains `sorry`):

- a published theorem that rests on an axiom of the module, passed through another theorem;
- a published theorem of another proposition that holds as well;
- a module without the published theorem;
- a module without a theorem that the check lists and does not publish (a consumer that a
  command of the text made elaborate nothing);
- a false proposition proved with the kernel's check turned off by the module;
- a definition of the statements rewritten in the kernel's environment by a text that sets no
  option at all, with a proof of the proposition that is then true (Lean accepts the module:
  Lean's acceptance does not see it). The rewritten declaration is among those that the object
  carries, under a name of an import;
- a declaration written over one of the library, in the same way;
- a theorem with a proof that does not check, put into the kernel's environment directly, with
  no other name declared: the replay on the statements as they were compiled refuses it;
- a proof module that does not import the statements and declares them itself.

A text cannot give a definition of the statements another value by declaring it again: the
definition is imported, and Lean refuses a second declaration of its name, which a case shows.

One module shows what the object is: whatever the run of Lean on the text leaves in the
module's folder. Its text writes the object itself and ends Lean with success; the program does
not read what it wrote as an object. A text can also leave there a well-formed object of its
choosing, and the program then judges that object: every declaration in it is replayed on the
imports, so what is accepted is a proof of the stated propositions whoever wrote the file. The
program reads the object in the sandbox too, since it maps the file into memory without
checking its format.

One more module is refused by Lean itself, in the sandbox in which every module of a check is
elaborated: a text that writes a file outside its own folder, here the object of the statements
that it imports (the program that reads the object, the setup and the imports all stand outside
it as well). The same is shown of a module that a check starts as one source. Two more texts
try to leave the sandbox by a socket: one asks the user's service manager to write the file,
and one makes a socket. Neither can: a module of a check makes no socket. A last text leaves a
link in its own folder to a folder outside; the check's removal of its work folder removes the
link and leaves what it points to.

The statements import nothing, so the program's own steps are what is run: the replay, the
reading of the published theorems, and the walk of the proofs for axioms. A text's own imports
are not the statements', and a module with them is accepted.
-/

open Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open Zkc.Tests.Formal.WrittenSubject

namespace OutsideReading

/-- What the generator would state, in a module of its own: a definition, and a proposition
that uses it. -/
def stated (proposition : String) : String :=
  "namespace Fixture\ndef mark : Nat := 0\n" ++ s!"def gGoal : Prop := {proposition}\nend Fixture\n"

/-- The two modules of the fixture: the statements, and a proof module that imports them and
holds a text and the published theorem. The text may ask for imports. A proof module that does
not import the statements is written whole by the case. -/
def fixture (text : String) (proposition := "mark = mark") (imports : List String := [])
    (whole : Option String := none) (proved : List String := []) : Module :=
  let opening := String.join (("Fixture.Stated" :: imports).map (s!"import {·}\n")) ++ "namespace Fixture\n"
  { space := "Fixture"
    statementsName := `Fixture.Stated
    statements := stated proposition
    stated := []
    statedImports := []
    proof := whole.getD (opening ++ text ++ "\nend Fixture\n")
    proved
    proofImports := imports
    textLine := (opening.splitOn "\n").length
    textLines := (text.splitOn "\n").length
    published := [(`Fixture.g_sound, `Fixture.gGoal)] }

/-- The imports with which a text can reach the kernel's environment. -/
def metaImports : List String := ["Lean", "Batteries.Tactic.OpenPrivate"]

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

/-- A text that sets no option and declares nothing again. It puts the published theorem into
the kernel's environment directly, with the proof `proof`, which nothing checks in the file. -/
def planting (proof : String) : String :=
  "open Lean Elab Command\n" ++
  "open private Lean.Environment.setCheckedSync from Lean.Environment\n" ++
  "open private Lean.Kernel.Environment.add from Lean.Environment\n" ++
  "run_cmd do\n" ++
  "  let env ← getEnv\n" ++
  s!"  let proof := {proof}\n" ++
  "  let planted : TheoremVal := { name := `Fixture.g_sound, levelParams := [], type := mkConst `Fixture.gGoal, value := proof }\n" ++
  "  let changed := Lean.Kernel.Environment.add env.toKernelEnv (.thmInfo planted)\n" ++
  "  setEnv (Lean.Environment.setCheckedSync env changed)\n"

/-- A module that Lean itself refuses, saying `place`, at the position `at_` of the text
(`text:<line>:<column>`: an error of a text is reported by the lines of the text). -/
def refusedByLean (work : System.FilePath) (title : String) (module : Module) (place at_ : String) :
    IO Unit := do
  let outside ← readOutside (work / title) "Fixture" module
  unless !outside.lean.1 && outside.lean.2.contains place && outside.lean.2.contains s!"{at_}: error" do
    throw (IO.userError s!"{title}: Lean did not refuse the module at `{place}`\n{outside.lean.2}")

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

/-- A module that a check accepts: Lean and the reading outside do, as a check of a subject
judges them (`Outside.accepted`). -/
def accepted (work : System.FilePath) (title : String) (module : Module) : IO Unit := do
  (← readOutside (work / title) "Fixture" module).accepted title

/-- A text that writes a file outside its own folder, in a proof module that is read outside:
the module is elaborated in a sandbox, and Lean stops at the write. The file is the object of
the statements that the module imports, which the check compiled before. -/
def writtenOutside (work : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (work / "written")
  let target := (← IO.FS.realPath (work / "written")) / "Fixture.stated" / "Stated.olean"
  let writing ← readOutside (work / "written") "Fixture"
    (fixture (s!"#eval IO.FS.writeFile {reprStr target.toString} \"rewritten by the text\"\n" ++
      "theorem g_sound : gGoal := rfl"))
  unless !writing.lean.1 && writing.lean.2.contains "read-only" &&
      (← IO.FS.readBinFile target) != "rewritten by the text".toUTF8 do
    throw (IO.userError s!"a text wrote over the object of its statements\n{writing.lean.2}")

/-- The same of a module that a check starts as one source (a module without a text of an
author, or a comparison): it is elaborated in the same sandbox. -/
def writtenByControl (work : System.FilePath) : IO Unit := do
  let beside := (← IO.FS.realPath work) / "beside.txt"
  IO.FS.writeFile beside "as the check wrote it\n"
  let (ok, said) ← finishLean (← startLakeLean work "Writer"
    s!"#eval IO.FS.writeFile {reprStr beside.toString} \"rewritten by the text\"\n")
  unless !ok && said.contains "read-only" && (← IO.FS.readFile beside) == "as the check wrote it\n" do
    throw (IO.userError s!"a module of a check wrote a file outside its folder\n{said}")

/-- A text that asks a process outside the sandbox to write the file for it. A file system that
is bound read-only does not stop a connection to a socket with a path, and the user's service
manager, reached through one, runs a command outside. The sandbox lets a process make no
socket, so the request fails and the file is as the check wrote it. On a host without that
service manager the command is not found, and the file is as the check wrote it as well. -/
def askedOutside (work : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (work / "asked")
  let beside := (← IO.FS.realPath (work / "asked")) / "beside.txt"
  IO.FS.writeFile beside "as the check wrote it\n"
  let (_, said) ← finishLean (← startLakeLean (work / "asked") "Asker"
    ("#eval show IO Unit from do\n" ++
      "  let out ← IO.Process.output { cmd := \"systemd-run\", args := #[\"--user\", \"-q\", \"--wait\", " ++
      "\"--collect\", \"sh\", \"-c\", " ++ reprStr s!"echo rewritten by the text > {beside}" ++ "] }\n" ++
      "  IO.println s!\"the service manager answered {out.exitCode}\"\n"))
  unless (← IO.FS.readFile beside) == "as the check wrote it\n" do
    throw (IO.userError s!"a text had a process outside the sandbox write a file\n{said}")

/-- A text that leaves, in its own folder, a link to a folder beside the work folder. A check
removes its work folder when it ends; the removal takes the link away and not what it points
to. -/
def linkedOutside (work : System.FilePath) : IO Unit := do
  IO.FS.createDirAll (work / "kept")
  let kept ← IO.FS.realPath (work / "kept")
  IO.FS.writeFile (kept / "file.txt") "as the check wrote it\n"
  let linked ← IO.FS.withTempDir fun inner => do
    let (_, said) ← finishLean (← startLakeLean inner "Linker"
      ("#eval show IO Unit from do\n" ++
        "  let some folder ← IO.getEnv \"TMPDIR\" | throw (IO.userError \"no folder\")\n" ++
        "  let out ← IO.Process.output { cmd := \"ln\", args := #[\"-s\", " ++ reprStr kept.toString ++
        ", folder ++ \"/link\"] }\n" ++
        "  IO.println s!\"linked {out.exitCode}\"\n"))
    unless ← (inner / "Linker" / "link" / "file.txt").pathExists do
      throw (IO.userError s!"the text left no link in its folder\n{said}")
    pure (inner / "Linker" / "link")
  unless !(← linked.pathExists) && (← IO.FS.readFile (kept / "file.txt")) == "as the check wrote it\n" do
    throw (IO.userError "the removal of a work folder followed a link that a text left in it")

/-- A module of a check can make no socket: the call fails where the text makes one. -/
def socketMade (work : System.FilePath) : IO Unit := do
  let (_, said) ← finishLean (← startLakeLean (work / "socket") "Socket"
    ("#eval show IO Unit from do\n" ++
      "  let out ← IO.Process.output { cmd := \"python3\", args := #[\"-c\", " ++
      "\"import socket\\nsocket.socket(socket.AF_UNIX)\\nprint('a socket was made')\"] }\n" ++
      "  IO.println (out.stdout ++ out.stderr)\n"))
  unless said.contains "PermissionError" && !said.contains "a socket was made" do
    throw (IO.userError s!"a module of a check made a socket\n{said}")

def run (work : System.FilePath) : IO Unit := do
  let cases : List (IO Unit) := [
    -- the module that is as the generator states it
    accepted work "honest" (fixture "theorem g_sound : gGoal := rfl"),
    -- a text with imports of its own, which the statements do not have, is read as any other
    accepted work "imported" (fixture "theorem g_sound : gGoal := rfl" (imports := metaImports)),
    -- what a text may have beside its proofs: code that the kernel does not check (it is not
    -- replayed, and its axioms are not asked for), and a name with `sorry` in it, which Lean
    -- prints and which is no placeholder
    accepted work "helpers"
      (fixture ("inductive Color where\n  | red\n  | green\n  deriving DecidableEq\n" ++
        "unsafe def unchecked (n : Nat) : Nat := n + 1\n" ++
        "partial def lengthOfTail : List Nat → Nat\n  | [] => 0\n  | _ :: rest => lengthOfTail rest + 1\n" ++
        "def sorryEstimate : Nat := 0\n#check sorryEstimate\n" ++
        "theorem g_sound : gGoal := rfl")),
    refused work "axiom"
      (fixture "axiom extra : True\ntheorem helper : True := extra\ntheorem g_sound : gGoal := (fun _ : True => rfl) helper")
      "`Fixture.g_sound` rests on",
    -- a definition of the statements cannot be declared again
    refusedByLean work "redeclared"
      (fixture "def mark : Nat := 1\ntheorem g_sound : gGoal := rfl")
      "already been declared" "text:1:4",
    refused work "proposition"
      (fixture "theorem g_sound : mark = mark := rfl")
      "`Fixture.g_sound` is not of the proposition `Fixture.gGoal`",
    refused work "missing"
      (fixture "theorem other : gGoal := rfl")
      "the candidate does not declare the theorem `Fixture.g_sound`",
    -- a theorem that the check lists and the object does not have: a text can make a later
    -- command elaborate nothing, and Lean then says nothing of the theorem that is missing
    refused work "dropped"
      (fixture ("open Lean Elab Command in\nelab_rules : command\n" ++
        "  | `(theorem consumer $_:declSig $_:declVal) => pure ()\n" ++
        "theorem g_sound : gGoal := rfl\ntheorem consumer : mark = 0 := rfl")
        (imports := ["Lean"]) (proved := ["consumer"]))
      "the candidate does not have the theorem `Fixture.consumer`, which the check lists",
    refused work "unchecked"
      (fixture ("set_option «debug».skipKernelTC true in\n" ++
        "theorem g_sound : gGoal := by\n  show (0 : Nat) = 1\n  decide +kernel") (proposition := "(0 : Nat) = 1"))
      "the kernel refuses a declaration of the candidate on replay" "Fixture.g_sound",
    -- the kernel that checks the file does not see a declaration written over an imported
    -- one (Lean then refuses a proof that needs the new value); the object carries it, under
    -- a name of the statements, and that is what the program refuses
    refused work "rewritten"
      (fixture (rewriting "Fixture.mark" "mkNatLit 1"
        "mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkConst `Fixture.mark)") (imports := metaImports))
      "the candidate declares `Fixture.mark`, which an import has",
    refusedByLean work "relied"
      (fixture (rewriting "Fixture.mark" "mkNatLit 1"
        "mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1)") (proposition := "mark = 1")
        (imports := metaImports))
      "declaration type mismatch" "text:11:0",
    refused work "overwritten"
      (fixture (rewriting "Nat.zero" "mkNatLit 1"
        "mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkConst `Fixture.mark)") (imports := metaImports))
      "the candidate declares `Nat.zero`, which an import has",
    -- no name is declared again: the replay on the statements as compiled is what refuses
    refused work "planted"
      (fixture (planting "mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (mkNatLit 1)")
        (proposition := "mark = 1") (imports := metaImports))
      "the kernel refuses a declaration of the candidate on replay" "Fixture.g_sound",
    refused work "unimported"
      (fixture "" (whole := some ("namespace Fixture\ndef mark : Nat := 0\ndef gGoal : Prop := mark = mark\n" ++
        "theorem g_sound : gGoal := rfl\nend Fixture\n")))
      "the candidate does not import `Fixture.Stated`, the module of the statements",
    -- the object is what the run of Lean on the text leaves in the module's folder: a text
    -- that writes it itself and ends Lean with success leaves no object that Lean wrote
    refused work "forged"
      (fixture ("#eval show IO Unit from do\n" ++
        "  let some folder ← IO.getEnv \"TMPDIR\" | throw (IO.userError \"no folder\")\n" ++
        "  IO.FS.writeFile (System.FilePath.mk folder / \"Fixture.olean\") \"written by the text\"\n" ++
        "  IO.Process.exit 0\n"))
      "invalid header",
    writtenOutside work,
    writtenByControl work,
    askedOutside work,
    socketMade work,
    linkedOutside work]
  -- at once: each case has a folder of its own
  let started ← cases.mapM fun case => IO.asTask case
  for task in started do
    IO.ofExcept task.get
  IO.println ("The reading outside the file accepts the module that is as stated, also with " ++
    "imports of its text, with code that the kernel does not check and with a name that has " ++
    "`sorry` in it, and refuses nine that Lean accepts: an axiom through another " ++
    "theorem, another proposition, a missing theorem, a missing theorem that the check lists and does not publish, a false proposition proved with the " ++
    "kernel's check turned off, a definition of the statements rewritten in the kernel's " ++
    "environment with no option set, a declaration written over the library's, a theorem put " ++
    "into the kernel's environment unchecked with no other name declared, and a module that " ++
    "declares the statements itself; a definition of the statements declared again is refused " ++
    "by Lean, and so is a proof that needs a value written over an imported one, each at its " ++
    "line of the text; and an object that the text wrote itself, with Lean ended in success, is not " ++
    "read as an object. A text that writes over the object of its statements is stopped by " ++
    "the sandbox in which every module of a check is elaborated; so is one that asks the " ++
    "user's service manager to write a file, since a module there can make no socket.")

end OutsideReading

#eval show IO Unit from
  IO.FS.withTempDir fun work => OutsideReading.run work
