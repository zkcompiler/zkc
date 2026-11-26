import ZkcFormalTests.WrittenSubject


open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests.WrittenSubject

namespace WrittenBoundGuard

private def startReader (work : System.FilePath) (m : Written.Module) (reader : String) :
    IO Pending :=
  startLakeLean work (toString m.statementsName ++ "Source")
    (s!"import {m.statementsName}\nimport ZkcFormalTests.WrittenBinding\n" ++
      "import Zkc.Tests.Frontend.PrintedPackageSupport\nopen ZkcFormal.Written\n" ++
      s!"namespace {m.space}\n{reader}end {m.space}\n") (text := false)

private def check (work : System.FilePath) (file source name : String)
    (questions : List (String × String)) (formalImport := "ZkcFormal.Written.Soundness") :
    IO (IO Unit) := do
  let assembly ← Driver.assembleFiles ⟨file, Syntax.parseString file source⟩ ["../../libraries"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly "loose")
  let claims ← IO.ofExcept (goalClaims root ["loose"])
  unless claims.inputs == #["hidden", "claim"] && claims.goals.map (·.statement) == [#[1]] do
    throw <| IO.userError s!"{name}: expected IsSet(claim) at deployed input 1"
  let m ← IO.ofExcept ((Statements.mk claims claims.functionsBeforeRoot).module name {})
  unless m.refusals.isEmpty do throw <| IO.userError s!"{name}: {m.refusals}"
  let coordinates ← IO.ofExcept (ZkcFormalTests.WrittenSource.consumerAt root [("loose", "loose")] true)
  let reader := s!"#eval Zkc.Tests.Frontend.PrintedPackageSupport.expectGoalClaims {literal source} " ++
    "[\"loose\"] ⟨[], [], [], [], []⟩ stored association\n" ++
    "example : subjectPackage.stored = stored := rfl\n" ++
    "example : subjectPackage.association = association := rfl\n" ++
    "example : subjectPackage.installed = installed := rfl\n" ++ coordinates
  let scope := s!"\nnamespace {m.space}\nopen Zkc.Core\n" ++ statementOpens ++
    "open StandardInterpretation (draws covers)\n"
  let closing := s!"\nend {m.space}\n"
  let declarations := String.join <| questions.map fun (label, prop) =>
    s!"def {label}Statement : Prop := {prop}\n"
  let names := (questions.map fun (label, _) => (label, label))
  let text ← IO.FS.readFile s!"checks/{m.space}.lean.in"
  let opening := s!"import {m.statementsName}\n" ++ scope
  let issued := { m with
    statements := s!"import {formalImport}\n" ++ m.statements ++ scope ++ declarations ++ closing
    proof := opening ++ text ++ closing
    published := names.map fun (label, question) =>
      (.str m.space.toName label, .str m.space.toName (question ++ "Statement"))
    proved := names.map Prod.fst
    textLine := (opening.splitOn "\n").length
    textLines := (text.splitOn "\n").length }
  let observed ← startReader work issued reader
  let submitted ← startModule work name issued
  -- The reader imports the printed challenge even when the recipe batches judgments elsewhere.
  discard <| addChallenge work name issued
  return do
    acceptedByLean s!"{name} source reader" (← observed)
    discard submitted

def run (work : System.FilePath) : IO Unit := do
  let file := "fixtures/written-bound-guard.zkc"
  let source ← IO.FS.readFile file
  let total ← replaceOnce source "IsSet(claim: bool): claim" "IsSet(claim: bool): true"
  let args := "model written'application0 draws"
  let result := s!"Soundness.Result {args} covers"
  let witnessed := s!"Soundness.Witnessed {args}"
  let always ← check work file total "BoundTotal" [
    ("allBounds", s!"∀ b, {result} b"), ("noWitness", "¬ " ++ witnessed)]
  -- The guarded source as it is: on the rejected input its verifier draws and stops, so it is
  -- judged within a budget of zero under its own table, whose budget is one over four. The
  -- judgment's budget is its own number, not the table's.
  let guarded ← check work file source "BoundGuard" [
    ("withinZero", s!"Fees.JudgedWithin {args} looseCaps 0"),
    ("belowTable", "(0 : NNRat) < looseCaps.budget"),
    ("atZero", s!"{result} 0")] (formalImport := "ZkcFormal.Written.Fees")
  let reader ← IO.FS.readFile "checks/WrittenBoundEndpoints.lean.in"
  let observed ← startLakeLean work "BoundEndpoints" reader (text := false)
  acceptedByLean "written bound endpoints" (← observed)
  [always, guarded].forM id

end WrittenBoundGuard

#eval IO.FS.withTempDir WrittenBoundGuard.run
