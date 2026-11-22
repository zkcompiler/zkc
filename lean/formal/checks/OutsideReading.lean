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
- a false proposition proved with the kernel's check turned off by the module.

The modules import nothing, so the program's own steps are what is run: the replay, the
comparison with the reference, and the walk of the proofs for axioms.
-/

open Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open Zkc.Tests.Frontend.WrittenSubject

namespace OutsideReading

/-- What the generator would state: a definition, and a proposition that uses it. -/
def stated (proposition : String) : String :=
  "namespace Fixture\ndef mark : Nat := 0\n" ++ s!"def gGoal : Prop := {proposition}\n"

/-- A module of the fixture: the statements, a text, and the published theorem. -/
def fixture (text : String) (mark := "0") (proposition := "mark = mark") : Module where
  text := (stated proposition).replace "def mark : Nat := 0" s!"def mark : Nat := {mark}" ++ text ++
    "\nend Fixture\n"
  theorems := []
  reference := stated proposition ++ "end Fixture\n"
  published := [("Fixture.g_sound", "Fixture.gGoal")]

/-- A module that Lean accepts and the reading outside refuses, saying `place`. -/
def refused (work : System.FilePath) (title : String) (module : Module) (place : String) : IO Unit := do
  let outside ← readOutside (work / title) "Fixture" module
  unless outside.lean.1 do
    throw (IO.userError s!"{title}: Lean refused the module\n{outside.lean.2}")
  match outside.verified with
  | some (false, said) =>
    unless said.contains place do
      throw (IO.userError s!"{title}: refused outside the file for another reason\n{said}")
  | _ => throw (IO.userError s!"{title}: the module was accepted outside the file")

def run (work : System.FilePath) : IO Unit := do
  -- the module that is as the generator states it
  let honest ← readOutside (work / "honest") "Fixture" (fixture "theorem g_sound : gGoal := rfl")
  unless honest.lean.1 && honest.verified.map (·.1) == some true do
    throw (IO.userError s!"the honest module is refused\n{honest.lean.2}\n{honest.verified.map (·.2)}")
  refused work "axiom"
    (fixture "axiom extra : True\ntheorem helper : True := extra\ntheorem g_sound : gGoal := (fun _ : True => rfl) helper")
    "`Fixture.g_sound` rests on"
  refused work "definition"
    (fixture "theorem g_sound : gGoal := rfl" (mark := "1"))
    "`Fixture.mark` is not the declaration that the reference has"
  refused work "proposition"
    (fixture "theorem g_sound : mark = mark := rfl")
    "`Fixture.g_sound` is not of the proposition `Fixture.gGoal`"
  refused work "missing"
    (fixture "theorem other : gGoal := rfl")
    "the candidate does not declare the theorem `Fixture.g_sound`"
  refused work "unchecked"
    (fixture ("set_option «debug».skipKernelTC true in\n" ++
      "theorem g_sound : gGoal := by\n  show (0 : Nat) = 1\n  decide +kernel") (proposition := "(0 : Nat) = 1"))
    "while replaying declaration 'Fixture.g_sound"
  IO.println ("The reading outside the file accepts the module that is as stated and refuses five " ++
    "that Lean accepts: an axiom through another theorem, a definition that is not the " ++
    "reference's, another proposition, a missing theorem, and a false proposition proved with " ++
    "the kernel's check turned off.")

end OutsideReading

#eval show IO Unit from
  IO.FS.withTempDir fun work => OutsideReading.run work
