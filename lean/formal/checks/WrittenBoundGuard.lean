import ZkcFormalTests.WrittenSubject


open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests.WrittenSubject

namespace WrittenBoundGuard

private def startReader (work : System.FilePath) (m : Module) (reader : String) :
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
  -- the issuer's data module; the questions of this check are stated after it, and the pair that
  -- the comparator judges is this check's own
  let data ← IO.ofExcept ((Statements.mk claims).publication name)
  unless data.refusals.isEmpty do throw <| IO.userError s!"{name}: {data.refusals}"
  let m : Module :=
    { space := data.space, statementsName := data.dataName, statements := data.data, stated := data.stated,
      proof := "", proved := [], textLine := 0, textLines := 0 }
  let coordinates ← IO.ofExcept
    (ZkcFormalTests.WrittenSource.consumerAt root ["loose"])
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
    statements := String.join ((statementOpenImports ++ [formalImport]).map (s!"import {·}\n")) ++
      m.statements ++ scope ++ declarations ++ closing
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

/-- The guarded source at a ceiling of zero, through the issuer: the goal is issued at zero, below
the total of its table, so the fees module gives its row no fee facts; the text proves a fee
judgment within zero under the issued table by itself, reaches the installed bound on its view
and closes the published `sound` by the declared step; `lake comparator` judges the pair
against the issuer's challenge. -/
private def atZero (work : System.FilePath) (file source : String) : IO (IO Unit) := do
  let zero ← replaceOnce source "stage = written) <= 1 / 4" "stage = written) <= 0"
  let assembly ← Driver.assembleFiles ⟨file, Syntax.parseString file zero⟩ ["../../libraries"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly "loose")
  let claims ← IO.ofExcept (goalClaims root ["loose"])
  let issued ← IO.ofExcept ((Statements.mk claims).publication "AtZero")
  unless issued.refusals.isEmpty && issued.limits.isEmpty do
    throw <| IO.userError s!"AtZero: {issued.refusals} {issued.limits}"
  unless issued.published == [`AtZero.guard_bound.loose.sound, `AtZero.guard_bound.loose.met] &&
      issued.data.contains "def written'bound0 : Zkc.Subject.Bound := ⟨0, 1, by decide⟩" do
    throw <| IO.userError s!"AtZero: the goal is not issued at zero: {issued.published}"
  let text ← IO.FS.readFile "checks/BoundGuard.lean.in"
  let module := Module.ofPublication issued text
    ["withinZero", "belowTable", "guard_bound.loose.sound", "guard_bound.loose.met"]
  let compared ← startSourceComparison work "AtZeroSource" module zero ["loose"]
  let submitted ← startModule work "AtZero" module
  let fees := leanOn work issued.feesName
  return do
    acceptedByLean "AtZero source reader" (← compared)
    discard submitted
    let (ok, output) ← fees
    unless ok && output.contains "is above the bound 0/1; no fee facts" do
      throw <| IO.userError s!"AtZero: the fees module does not say that the row has no fee facts\n{output}"

def run (work : System.FilePath) : IO Unit := do
  let file := "fixtures/written-bound-guard.zkc"
  let source ← IO.FS.readFile file
  let total ← replaceOnce source "IsSet(claim: bool): claim" "IsSet(claim: bool): true"
  let args := "model written'application0 draws"
  let result := s!"Soundness.Result {args} covers"
  let witnessed := s!"Soundness.Witnessed {args}"
  let always ← check work file total "BoundTotal" [
    ("allBounds", s!"∀ b, {result} b"), ("noWitness", "¬ " ++ witnessed)]
  -- The guarded source at a ceiling of zero, issued and judged: on the rejected input its verifier
  -- draws and stops, so it is judged within a budget of zero under its own table, whose budget
  -- is one over four. The judgment's budget is its own number, not the table's. (The same source
  -- at its ceiling of one quarter is judged through the fee facts in `checks/WrittenFees.lean`.)
  let guarded ← atZero work file source
  let reader ← IO.FS.readFile "checks/WrittenBoundEndpoints.lean.in"
  let observed ← startLakeLean work "BoundEndpoints" reader (text := false)
  acceptedByLean "written bound endpoints" (← observed)
  [always, guarded].forM id

end WrittenBoundGuard

#eval IO.FS.withTempDir WrittenBoundGuard.run
