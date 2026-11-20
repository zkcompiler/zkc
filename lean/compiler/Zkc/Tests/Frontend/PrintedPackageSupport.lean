import Zkc.Frontend.Written.Root
import Zkc.Frontend.Driver.Files

/-!
What a check of a printed package needs beside the package: the roots of a source file as the
frontend admits them, and the comparison of a program by names that Lean read from a printed
module with the program that the frontend gave to admission.
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
def atRows : {b : Emit.Bindings} → {rows : List (Emit.PrimitiveName × Emit.PrimitiveSignature)} →
    {distinct : (rows.map Prod.fst).Nodup} → b.rows = rows → NamedProgram b.vocabulary →
      NamedProgram (Emit.Bindings.mk rows distinct).vocabulary
  | ⟨_, _⟩, _, _, rfl, program => program

/-- The program by names of a printed package is the program that the frontend gives to
admission for the root: the same external rows, and the same definitions. The comparison is of
values, so a printer that wrote a different program, or lost a part of one, is found here. -/
def expectStored (project : System.FilePath) (file : String) (edits : List (String × String))
    (root : Nat) {rows : List (Emit.PrimitiveName × Emit.PrimitiveSignature)}
    {distinct : (rows.map Prod.fst).Nodup}
    (stored : NamedProgram (Emit.Bindings.mk rows distinct).vocabulary) : IO Unit := do
  let state ← compile project file edits
  let admitted ← IO.ofExcept (Written.admitInstance state root default)
  let emission := admitted.emission
  if same : emission.bindings.rows = rows then
    unless decide (atRows (distinct := distinct) same emission.named = stored) do
      throw (IO.userError s!"{file}, root {root}: the printed program differs from the stored program")
  else
    throw (IO.userError s!"{file}, root {root}: the printed external rows differ from the bindings")

end Zkc.Tests.Frontend.PrintedPackageSupport
