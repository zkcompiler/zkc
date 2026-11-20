import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Driver.Files

/-!
What a check of a printed package needs beside the package: the roots of a source file as the
frontend admits them, the comparison of a program by names that Lean read from a printed module
with the program that the frontend gave to admission, and the run of Lean on a module with what
is expected of its output.
-/

namespace Zkc.Tests.Frontend.PrintedPackageSupport
open Zkc.Core Zkc.Frontend

/-- A source file, with each of the edits applied where its text occurs exactly once. -/
def source (path : System.FilePath) (edits : List (String × String) := []) : IO SourceInput := do
  let mut text ← IO.FS.readFile path
  for (before, after) in edits do
    unless (text.splitOn before).length == 2 do
      throw (IO.userError s!"{path}: expected exactly one occurrence of {reprStr before}")
    text := text.replace before after
  return ⟨path.toString, Syntax.parseString path.toString text⟩

/-- The compiled state of an example of the project: the entry with its edits, and the modules
it uses from the examples and the libraries. -/
def compile (project : System.FilePath) (file : String) (edits : List (String × String)) :
    IO Compile.State := do
  let entry ← source (project / "examples" / file) edits
  let assembly ← Driver.assembleFiles entry
    [project / "examples", project / "libraries", project / "examples/support"]
  IO.ofExcept (Written.sourceState assembly)

/-- A program over the vocabulary of bindings, over the vocabulary of their rows written out. -/
def atRows : {b : Zkc.Vocabulary.Project.Bindings} → {rows : List (Zkc.Vocabulary.Project.PrimitiveName × Zkc.Vocabulary.Project.PrimitiveSignature)} →
    {distinct : (rows.map Prod.fst).Nodup} → b.rows = rows → NamedProgram b.vocabulary →
      NamedProgram (Zkc.Vocabulary.Project.Bindings.mk rows distinct).vocabulary
  | ⟨_, _⟩, _, _, rfl, program => program

/-- The program by names and the association of a printed package are those that the frontend
gives to admission for the root: the same external rows, the same definitions, and the
association that the package was printed with. The comparison is of values, so a printer that
wrote a different program or a different association, or lost a part of one, is found here. -/
def expectEmission (title : String) (emission : Emit.RootEmission) (expected : Association)
    {rows : List (Zkc.Vocabulary.Project.PrimitiveName × Zkc.Vocabulary.Project.PrimitiveSignature)}
    {distinct : (rows.map Prod.fst).Nodup}
    (stored : NamedProgram (Zkc.Vocabulary.Project.Bindings.mk rows distinct).vocabulary)
    (association : Association) : IO Unit := do
  if same : emission.bindings.rows = rows then
    unless decide (atRows (distinct := distinct) same emission.named = stored) do
      throw (IO.userError s!"{title}: the printed program differs from the stored program")
  else
    throw (IO.userError s!"{title}: the printed external rows differ from the bindings")
  unless decide (association = expected) do
    throw (IO.userError s!"{title}: the printed association differs from the package's")

/-- The comparison for a root of an example of the project. -/
def expectStored (project : System.FilePath) (file : String) (edits : List (String × String))
    (root : Nat) (expected : Association) {rows : List (Zkc.Vocabulary.Project.PrimitiveName × Zkc.Vocabulary.Project.PrimitiveSignature)}
    {distinct : (rows.map Prod.fst).Nodup}
    (stored : NamedProgram (Zkc.Vocabulary.Project.Bindings.mk rows distinct).vocabulary)
    (association : Association) : IO Unit := do
  let state ← compile project file edits
  let admitted ← IO.ofExcept (Written.admitInstance state root default)
  expectEmission s!"{file}, root {root}" admitted.emission expected stored association

/-- The root that a soundness goal of a source selects, the source given as text. -/
def goalRoot (text goal : String) : Except String Written.AdmittedRoot :=
  Written.admitSoundnessGoal
    (Id.run <| assemble #[⟨"source.zkc", Syntax.parseString "source.zkc" text⟩] fun _ => pure none) goal

/-- The comparison for the root that a soundness goal of a source selects. -/
def expectGoalRoot (text goal : String) (expected : Association)
    {rows : List (Zkc.Vocabulary.Project.PrimitiveName × Zkc.Vocabulary.Project.PrimitiveSignature)}
    {distinct : (rows.map Prod.fst).Nodup}
    (stored : NamedProgram (Zkc.Vocabulary.Project.Bindings.mk rows distinct).vocabulary)
    (association : Association) : IO Unit := do
  let admitted ← IO.ofExcept (goalRoot text goal)
  expectEmission s!"goal {goal}" admitted.emission expected stored association

/-! ## Lean on a module -/

/-- A string as Lean writes it. -/
def literal (text : String) : String := reprStr text

/-- Lean's output on a module, and whether it ended without an error. -/
def runLean (path : System.FilePath) (options : Array String := #[]) : IO (Bool × String) := do
  let out ← IO.Process.output { cmd := "lean", args := options.push path.toString }
  return (out.exitCode == 0, out.stdout ++ out.stderr)

/-- Lean's output on a module in the workspace of the current directory, through `lake`: with
the options of the package, and with the modules of every package of the workspace, which two
packages that share a root name do not give to a bare `lean`. -/
def runLakeLean (path : System.FilePath) : IO (Bool × String) := do
  let out ← IO.Process.output { cmd := "lake", args := #["-q", "lean", path.toString] }
  return (out.exitCode == 0, out.stdout ++ out.stderr)

/-- The axioms that Lean's output says a theorem rests on, when the output has them. -/
def axiomsOf (theorem_ output : String) : Option (List String) :=
  if output.contains s!"'{theorem_}' does not depend on any axioms" then some []
  else match output.splitOn s!"'{theorem_}' depends on axioms: [" with
    | _ :: after :: _ => some ((((after.splitOn "]").headD "").splitOn ",").map fun name =>
        String.ofList (name.toList.filter (!·.isWhitespace)))
    | _ => none

/-- What is expected of an accepted module: Lean ends without an error, nothing in it is left
to `sorry`, and each of the theorems rests on the allowed axioms at most. -/
def acceptedOutput (name : String) (ok : Bool) (output : String) (theorems : List String)
    (allowed : List String := ["propext", "Quot.sound"]) : IO Unit := do
  unless ok do throw (IO.userError s!"{name}: Lean refused the module\n{output}")
  if output.contains "sorry" then throw (IO.userError s!"{name}: the module uses sorry")
  if output.contains "PANIC" then throw (IO.userError s!"{name}: Lean panicked on the module\n{output}")
  for theorem_ in theorems do
    match axiomsOf s!"{name}.{theorem_}" output with
    | some found =>
      unless found.all allowed.contains do
        throw (IO.userError s!"{name}: {theorem_} rests on {found}, beyond {allowed}")
    | none => throw (IO.userError s!"{name}: the axioms of {theorem_} are not printed\n{output}")

/-- What is expected of a refused module: Lean ends with an error, and its output has each of
the texts expected of the control. With `only`, the module has exactly one error for each
text. -/
def refusedOutput (name : String) (ok : Bool) (output : String) (expected : List String)
    (only := false) : IO Unit := do
  if ok then throw (IO.userError s!"{name}: Lean accepted a control that must be refused")
  let errors := (output.splitOn "error").length - 1
  unless expected.all (fun text => output.contains text) && (!only || errors == expected.length) do
    throw (IO.userError s!"{name}: the control was refused for another reason\n{output}")

/-- Lean accepts the module, and each of its theorems rests on the allowed axioms at most. -/
def expectAccepted (name : String) (path : System.FilePath) (theorems : List String)
    (allowed : List String := ["propext", "Quot.sound"]) : IO Unit := do
  let (ok, output) ← runLean path
  acceptedOutput name ok output theorems allowed

/-- Lean refuses the module, for the reasons expected of the control. -/
def expectRefused (name : String) (expected : List String) (path : System.FilePath)
    (only := false) : IO Unit := do
  let (ok, output) ← runLean path
  refusedOutput name ok output expected only

end Zkc.Tests.Frontend.PrintedPackageSupport
