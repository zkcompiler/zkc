import Zkc.Frontend.Written.Package
import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Tests.Frontend.PrintedFixtures

/-!
The check of printed packages. Every root of the listed examples that the frontend admits is
printed as a Lean module, and Lean is run on the module. A module passes when the kernel
elaborates every definition of it, its theorems rest on `propext` and `Quot.sound` at most, and
the program by names that Lean read from it is the program that the frontend gave to admission.

A module holds one printed form of a program, so the kernel cannot find a wrong print that still
elaborates. Two things stand for that. The comparison with the frontend's program, by value, in
every module; and a fixture with every constructor of the program by names, printed, read by
Lean and compared with the fixture by value.

Four controls show that the check can fail. A program whose call names no definition does not
elaborate, and the kernel command refuses it. A key changed in a definition by names still
elaborates, and only the comparison with the source refuses it. A module compared with the
program of a different source is refused by that comparison. A module whose association alone
is changed still admits, and only the comparison of the association refuses it.

Run from `lean/compiler` with `lake env lean --run Zkc/Tests/Frontend/PrintedPackages.lean`.
-/

open Zkc.Core Zkc.Frontend Zkc.Tests.Frontend
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
  ⟨"MixedRounds", "mixed_rounds.zkc", [], 1, 0⟩,
  ⟨"Gkr", "gkr_example.zkc", [], 1, 0⟩,
  ⟨"InnerProduct", "inner_product.zkc", [], 2, 0⟩,
  ⟨"Variants", "variants_example.zkc", [], 1, 1⟩,
  ⟨"Fragments", "fragments.zkc", [], 7, 5⟩]

/-- The association that the packages of this check are printed with: none of a scheme. -/
def noAssociation : Association := ⟨[], [], [], [], []⟩

def edits (pairs : List (String × String)) : String :=
  "[" ++ ", ".intercalate (pairs.map fun (before, after) => s!"({literal before}, {literal after})") ++ "]"

def imports (others : List String) : String :=
  String.join ((Written.packageImports ++ others).map (s!"import {·}\n")) ++ "\nopen Zkc.Core\n"

/-- The module of a printed package with what the check asks of it: the axioms of its theorems,
and the comparison of its program by names with the source's. -/
def checkModule (name text : String) (project : System.FilePath) (file : String)
    (source : List (String × String)) (root : Nat) (association : Association) : String :=
  imports ["Zkc.Tests.Frontend.PrintedPackageSupport"] ++ s!"namespace {name}\n" ++ text ++
  "#print axioms readback\n#print axioms admitted_exists\n" ++
  s!"#eval Zkc.Tests.Frontend.PrintedPackageSupport.expectStored {literal project.toString} " ++
  s!"{literal file} {edits source} {root} ({Written.associationTerm association}) stored association\nend {name}\n"

/-- The fixture, printed, beside the comparison of what Lean reads with the fixture itself. -/
def fixtureModule : String :=
  let printed := PrintedFixtures.definitions.map (Written.storedDefinition (b := PrintedFixtures.bindings))
  imports ["Zkc.Tests.Frontend.PrintedFixtures"] ++ "namespace Fixture\n" ++
  s!"abbrev V : Zkc.Core.Vocabulary := {Written.vocabularyTerm PrintedFixtures.bindings}\n" ++
  String.join ((printed.zipIdx).map fun (text, i) => s!"def printed{i} : Definition V :=\n  {text}\n") ++
  s!"def printed : List (Definition V) := [{", ".intercalate ((List.range printed.length).map (s!"printed{·}"))}]\n" ++
  s!"def printedAssociation : Association := {Written.associationTerm PrintedFixtures.association}\n" ++
  "open Zkc.Tests.Frontend in\n" ++
  "theorem definitions_read : printed = PrintedFixtures.definitions := by decide +kernel\n" ++
  "open Zkc.Tests.Frontend in\n" ++
  "theorem association_read : printedAssociation = PrintedFixtures.association := by decide +kernel\n" ++
  "end Fixture\n"

/-- The text with the first number that follows `marker` after `start` raised by a thousand. -/
def raiseFirst (text start marker : String) : Option String := do
  let before :: later := text.splitOn start | none
  if later.isEmpty then none
  let first :: second :: rest := (start.intercalate later).splitOn marker | none
  let digits := second.takeWhile Char.isDigit
  let number ← digits.toNat?
  let changed := toString (number + 1000) ++ (second.dropWhile Char.isDigit).toString
  return before ++ start ++ marker.intercalate (first :: changed :: rest)

def run (project work : System.FilePath) : IO Unit := do
  -- the fixture: every constructor of the program by names, printed and read back
  IO.FS.writeFile (work / "Fixture.lean") (fixtureModule ++
    "#print axioms Fixture.definitions_read\n#print axioms Fixture.association_read\n")
  expectAccepted "Fixture" (work / "Fixture.lean") ["definitions_read", "association_read"]
  IO.println s!"fixture: {PrintedFixtures.definitions.length} definitions and the association read back"
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
        let package := found.emission.package noAssociation
        let text := Written.package package
        let name := s!"{subject.label}{root}"
        let path := work / s!"{name}.lean"
        IO.FS.writeFile path
          (checkModule name text.text project subject.file subject.edits root noAssociation)
        expectAccepted name path ["readback", "admitted_exists"]
        IO.println s!"{name}: {text.definitions.length} definitions, {package.bindings.rows.length} external rows, accepted"
        printed := printed + 1
        if subject.label == "Sumcheck" then control := some (name, text.text, subject, root)
    unless admitted == subject.admitted && refused == subject.refused do
      throw (IO.userError
        s!"{subject.label}: {admitted} roots admitted and {refused} not, expected {subject.admitted} and {subject.refused}")
  let some (name, text, subject, root) := control | throw (IO.userError "no package for the controls")
  let differs := "the printed program differs from the stored program"
  -- A call of a function that the program does not have: the definition does not elaborate.
  let some uncalled := raiseFirst text "abbrev V" "(.call ⟨"
    | throw (IO.userError "the control of elaboration found no call")
  IO.FS.writeFile (work / "ElaborationControl.lean")
    (checkModule name uncalled project subject.file subject.edits root noAssociation)
  expectRefused "elaboration control" ["kernel_ok: the kernel reduces the term to an error"]
    (work / "ElaborationControl.lean")
  -- A key changed in the first definition by names: it elaborates, and it is not the source's.
  let some rekeyed := raiseFirst text "abbrev V" ".op ⟨"
    | throw (IO.userError "the control of the stored program found no operation")
  IO.FS.writeFile (work / "StoredControl.lean")
    (checkModule name rekeyed project subject.file subject.edits root noAssociation)
  expectRefused "stored control" [differs] (work / "StoredControl.lean") (only := true)
  -- The package of two rounds compared with the source of one round.
  let other := [("Proof = Sumcheck<10>", "Proof = Sumcheck<1>")]
  IO.FS.writeFile (work / "SourceControl.lean")
    (checkModule name text project subject.file other root noAssociation)
  expectRefused "source control" [differs] (work / "SourceControl.lean") (only := true)
  -- The association alone changed: a claim that the package was not printed with.
  let written := s!"def association : Association := {Written.associationTerm noAssociation}"
  let claimed : Association := { noAssociation with claims := [⟨123⟩] }
  unless (text.splitOn written).length == 2 do
    throw (IO.userError "the control of the association found no association to change")
  let associated := text.replace written
    s!"def association : Association := {Written.associationTerm claimed}"
  IO.FS.writeFile (work / "AssociationControl.lean")
    (checkModule name associated project subject.file subject.edits root noAssociation)
  expectRefused "association control" ["the printed association differs from the package's"]
    (work / "AssociationControl.lean") (only := true)
  IO.println s!"{printed} printed packages accepted; 4 of 4 controls refused"

end PrintedPackages

def main : IO Unit := do
  let project := (← IO.currentDir) / ".." / ".."
  IO.FS.withTempDir fun work => PrintedPackages.run project work
