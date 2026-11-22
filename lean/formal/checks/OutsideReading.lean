import ZkcFormalTests.SubjectProject

/-!
The judgment of a proof module, as the checks use it.

A check of a written subject does not rest on Lean's acceptance of a proof module: a text is
arbitrary Lean. It gives the proof modules that it accepts to `lake comparator`, with the
module of the statements and a challenge that the generator writes
(`ZkcFormalTests.SubjectProject.judge`). The comparator's own behaviour is the toolchain's to
test. What is checked here is the use that the checks make of it, on pairs as the generator
writes them (a module of statements with a definition and a proposition, a challenge that
states the published theorem with no proof, a proof module that imports the statements and
holds a text):

- the pair that is as stated is accepted;
- a proof of another proposition under the published name, a proof module without the
  published theorem, and a theorem that rests on an axiom through another theorem are refused,
  each with its reason;
- a false proposition proved with the kernel's check turned off by the text, which Lean
  accepts, is refused by the kernel;
- a text that writes a file beside its project, or over the challenge, changes nothing: the
  comparator builds a solution in its sandbox, and a check gives it a text that no other run
  of Lean has read.

Each case is a project of its own that requires no package, so that `lake` has nothing to
resolve.
-/

open ZkcFormalTests

namespace OutsideReading

/-- What the generator would state, in a module of its own: a definition, and a proposition
that uses it. -/
def stated (proposition : String) : String :=
  "namespace Fixture\ndef mark : Nat := 0\n" ++ s!"def gGoal : Prop := {proposition}\nend Fixture\n"

/-- The challenge of the pair: the published theorem over its proposition, with no proof. -/
def challenge : String :=
  "import Fixture.Stated\ntheorem Fixture.g_sound : Fixture.gGoal := by sorry\n"

/-- A proof module with the text `text`. -/
def proof (text : String) : String :=
  "import Fixture.Stated\nnamespace Fixture\n" ++ text ++ "\nend Fixture\n"

/-- The pair of a case in a project of its own, judged without an earlier build: the
comparator's verdict and what it said. -/
def judged (work : System.FilePath) (title text : String) (proposition := "mark = mark") :
    IO (Bool × String) := do
  let project := work / title
  SubjectProject.bare project
  discard <| SubjectProject.add project `Fixture.Stated (stated proposition)
  discard <| SubjectProject.add project `Fixture.Challenge challenge .challenge
  discard <| SubjectProject.add project `Fixture (proof text)
  SubjectProject.judge project "Case" [(`Fixture.Challenge, `Fixture)] [`Fixture.g_sound]
    ["propext", "Classical.choice", "Quot.sound"]

/-- A case that the judgment accepts. -/
def accepted (work : System.FilePath) (title text : String) : IO Unit := do
  let (ok, said) ← judged work title text
  unless ok do throw (IO.userError s!"{title}: the judgment refuses the pair\n{said}")

/-- A case that the judgment refuses, saying `reason`. -/
def refused (work : System.FilePath) (title text reason : String)
    (proposition := "mark = mark") : IO Unit := do
  let (ok, said) ← judged work title text proposition
  if ok then throw (IO.userError s!"{title}: the judgment accepts the pair")
  unless said.contains reason do
    throw (IO.userError s!"{title}: refused for another reason than `{reason}`\n{said}")

/-- A text that writes over a file beside the project and over the challenge of its own pair.
The comparator builds it in its sandbox: both writes fail, the build of the solution fails with
them, and the files are as the check wrote them. -/
def written (work : System.FilePath) : IO Unit := do
  let beside := (← IO.FS.realPath work) / "beside.txt"
  IO.FS.writeFile beside "as the check wrote it\n"
  let project := (← IO.FS.realPath work) / "writer"
  let target := project / "Fixture" / "Challenge.lean"
  let (ok, said) ← judged work "writer"
    (s!"#eval IO.FS.writeFile {reprStr beside.toString} \"rewritten by the text\"\n" ++
      s!"#eval IO.FS.writeFile {reprStr target.toString} \"theorem Fixture.g_sound : True := trivial\"\n" ++
      "theorem g_sound : gGoal := rfl")
  if ok then throw (IO.userError "a text that writes outside its build was accepted")
  unless said.contains "read-only" do
    throw (IO.userError s!"the writes of a text were not stopped by a file system that is read-only\n{said}")
  unless (← IO.FS.readFile beside) == "as the check wrote it\n" && (← IO.FS.readFile target) == challenge do
    throw (IO.userError "a text wrote a file beside its project or over its challenge")

def run (work : System.FilePath) : IO Unit := do
  accepted work "honest" "theorem g_sound : gGoal := rfl"
  refused work "proposition" "theorem g_sound : mark = mark := rfl"
    "Challenge and solution theorem statement do not match: 'Fixture.g_sound'"
  -- the solution is exported by its published names: the exporter does not find the name
  refused work "missing" "theorem other : gGoal := rfl"
    "Constant Fixture.g_sound not found in environment"
  refused work "axiom"
    "axiom extra : True\ntheorem helper : True := extra\ntheorem g_sound : gGoal := (fun _ : True => rfl) helper"
    "Illegal axiom detected: 'Fixture.extra'"
  refused work "unchecked"
    "set_option «debug».skipKernelTC true in\ntheorem g_sound : gGoal := by\n  show (0 : Nat) = 1\n  decide +kernel"
    "kernel rejected the solution" (proposition := "(0 : Nat) = 1")
  written work
  IO.println ("The judgment accepts the pair that is as stated, and refuses a proof of another " ++
    "proposition under the published name, a proof module without the published theorem, a " ++
    "theorem that rests on an axiom through another theorem, and a false proposition proved " ++
    "with the kernel's check turned off, each with its reason; a text that writes beside its " ++
    "project and over its challenge is stopped by the sandbox in which the comparator builds " ++
    "it, and the files are as the check wrote them.")

end OutsideReading

#eval show IO Unit from
  IO.FS.withTempDir fun work => OutsideReading.run work
