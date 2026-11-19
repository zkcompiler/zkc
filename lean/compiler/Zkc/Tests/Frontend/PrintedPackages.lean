import Zkc.Frontend.Written.Package
import Zkc.Tests.Frontend.PrintedPackageSupport

/-!
The check of printed packages. Every root of the listed examples that the frontend admits is
printed as a Lean module, and Lean is run on the module. A module passes when the kernel accepts
it, its three theorems rest on `propext` and `Quot.sound` at most, and the program by names that
Lean read from it is the program that the frontend gave to admission.

Three controls show that the check can fail. A key changed in a typed body is refused where
the erasure of that definition is compared; a key changed in a definition by names is refused
at the same place and by the comparison with the source; and a module compared with the program
of a different source is refused by that comparison.

Run from `lean/compiler` with `lake env lean --run Zkc/Tests/Frontend/PrintedPackages.lean`.
-/

open Zkc.Core Zkc.Frontend
open Zkc.Tests.Frontend.PrintedPackageSupport

namespace PrintedPackages

/-- An example, the edits of its entry file, and how many of its roots are admitted and how
many are not: a root that stops being admitted, or starts to be, is a change to look at. -/
structure Subject where
  label : String
  file : String
  edits : List (String × String) := []
  admitted : Nat
  refused : Nat

def subjects : List Subject := [
  ⟨"Schnorr", "schnorr_example.zkc", [], 1, 2⟩,
  ⟨"ChaumPedersen", "chaum_pedersen.zkc", [], 1, 0⟩,
  ⟨"Sumcheck", "sumcheck_example.zkc", [("Proof = Sumcheck<10>", "Proof = Sumcheck<2>")], 1, 0⟩,
  ⟨"SumcheckTen", "sumcheck_example.zkc", [], 1, 0⟩,
  ⟨"Gkr", "gkr_example.zkc", [], 1, 0⟩,
  ⟨"InnerProduct", "inner_product.zkc", [], 2, 0⟩,
  ⟨"Variants", "variants_example.zkc", [], 1, 1⟩,
  ⟨"Fragments", "fragments.zkc", [], 7, 5⟩]

def literal (text : String) : String := reprStr text

def edits (pairs : List (String × String)) : String :=
  "[" ++ ", ".intercalate (pairs.map fun (before, after) => s!"({literal before}, {literal after})") ++ "]"

/-- The module of a printed package with what the check asks of it: the axioms of its theorems,
and the comparison of its program by names with the source's. -/
def checkModule (name text : String) (project : System.FilePath) (file : String)
    (source : List (String × String)) (root : Nat) : String :=
  String.join (Written.packageImports.map (s!"import {·}\n")) ++
  "import Zkc.Tests.Frontend.PrintedPackageSupport\n\n" ++
  s!"open Zkc.Core\nnamespace {name}\n" ++ text ++
  "#print axioms erasure\n#print axioms readback\n#print axioms admitted_exists\n" ++
  s!"#eval Zkc.Tests.Frontend.PrintedPackageSupport.expectStored {literal project.toString} " ++
  s!"{literal file} {edits source} {root} stored\nend {name}\n"

/-- Lean's output on a module, and whether it ended without an error. -/
def runLean (path : System.FilePath) : IO (Bool × String) := do
  let out ← IO.Process.output { cmd := "lean", args := #[path.toString] }
  return (out.exitCode == 0, out.stdout ++ out.stderr)

def allowedAxioms (name theorem_ output : String) : Bool :=
  output.contains s!"'{name}.{theorem_}' depends on axioms: [propext, Quot.sound]" ||
    output.contains s!"'{name}.{theorem_}' depends on axioms: [propext]" ||
    output.contains s!"'{name}.{theorem_}' does not depend on any axioms"

/-- Lean accepts the module, and each of its theorems rests on the two axioms at most. -/
def expectAccepted (name : String) (path : System.FilePath) : IO Unit := do
  let (ok, output) ← runLean path
  unless ok do throw (IO.userError s!"{name}: Lean refused the printed package\n{output}")
  if output.contains "sorry" then throw (IO.userError s!"{name}: the printed package uses sorry")
  for theorem_ in ["erasure", "readback", "admitted_exists"] do
    unless allowedAxioms name theorem_ output do
      throw (IO.userError s!"{name}: {theorem_} is missing or rests on another axiom\n{output}")

/-- Lean refuses the module with exactly the errors expected of the control, one for each
text. -/
def expectRefused (name : String) (expected : List String) (path : System.FilePath) : IO Unit := do
  let (ok, output) ← runLean path
  if ok then throw (IO.userError s!"{name}: Lean accepted a control that must be refused")
  let errors := (output.splitOn "error").length - 1
  unless expected.all (fun text => output.contains text) && errors == expected.length do
    throw (IO.userError s!"{name}: the control was refused for another reason\n{output}")

/-- The text with the first key after `start` that an operation has raised by a thousand. -/
def changeFirstKey (text start : String) : Option String := do
  let before :: later := text.splitOn start | none
  if later.isEmpty then none
  let marker := ".op ⟨"
  let first :: second :: rest := (start.intercalate later).splitOn marker | none
  let digits := second.takeWhile Char.isDigit
  let number ← digits.toNat?
  let changed := toString (number + 1000) ++ (second.dropWhile Char.isDigit).toString
  return before ++ start ++ marker.intercalate (first :: changed :: rest)

def run (project work : System.FilePath) : IO Unit := do
  let mut printed := 0
  let mut control : Option (String × String × Subject × Nat) := none
  for subject in subjects do
    let state ← compile project subject.file subject.edits
    let mut admitted := 0
    let mut refused := 0
    for root in state.roots.toList.eraseDups do
      match Written.admitInstance state root default with
      | .error _ => refused := refused + 1
      | .ok found =>
        admitted := admitted + 1
        let package := found.emission.package ⟨[], [], [], [], []⟩
        let text ← IO.ofExcept (Written.package package found.evidence)
        let name := s!"{subject.label}{root}"
        let path := work / s!"{name}.lean"
        IO.FS.writeFile path (checkModule name text.text project subject.file subject.edits root)
        expectAccepted name path
        IO.println s!"{name}: {text.definitions.length} definitions, {package.bindings.rows.length} external rows, accepted"
        printed := printed + 1
        if subject.label == "Sumcheck" then control := some (name, text.text, subject, root)
    unless admitted == subject.admitted && refused == subject.refused do
      throw (IO.userError
        s!"{subject.label}: {admitted} roots admitted and {refused} not, expected {subject.admitted} and {subject.refused}")
  let some (name, text, subject, root) := control | throw (IO.userError "no package for the controls")
  -- The decision that fails in the first two controls is the comparison of the first definition,
  -- a function, with its erasure; Lean prints the proposition that it could not decide.
  let erasureOfFirst := "(eraseFn names"
  let differs := "the printed program differs from the stored program"
  -- A key changed in the first typed body: the erasure of that definition is not its stored form.
  let some typed := changeFirstKey text "noncomputable def body"
    | throw (IO.userError "the typed control found no operation")
  IO.FS.writeFile (work / "TypedControl.lean")
    (checkModule name typed project subject.file subject.edits root)
  expectRefused "typed control" [erasureOfFirst] (work / "TypedControl.lean")
  -- A key changed in the first definition by names: the same comparison fails, and the program
  -- by names is no longer the source's.
  let some stored := changeFirstKey text "abbrev V"
    | throw (IO.userError "the stored control found no operation")
  IO.FS.writeFile (work / "StoredControl.lean")
    (checkModule name stored project subject.file subject.edits root)
  expectRefused "stored control" [erasureOfFirst, differs] (work / "StoredControl.lean")
  -- The package of two rounds compared with the source of one round.
  let other := [("Proof = Sumcheck<10>", "Proof = Sumcheck<1>")]
  IO.FS.writeFile (work / "SourceControl.lean") (checkModule name text project subject.file other root)
  expectRefused "source control" [differs] (work / "SourceControl.lean")
  IO.println s!"{printed} printed packages accepted; 3 of 3 controls refused"

end PrintedPackages

def main : IO Unit := do
  let project := (← IO.currentDir) / ".." / ".."
  IO.FS.withTempDir fun work => PrintedPackages.run project work
