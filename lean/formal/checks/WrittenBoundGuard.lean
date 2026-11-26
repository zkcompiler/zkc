import ZkcFormalTests.WrittenSubject

/-! Issue one guarded source and its two single-edit controls. The trusted propositions below
are frozen with the issued statements. Each proof template is judged against those propositions
by the ordinary written-subject comparator. -/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests.WrittenSubject

namespace WrittenBoundGuard

private def startReader (work : System.FilePath) (m : Written.Module) (reader : String) :
    IO Pending :=
  startLakeLean work (toString m.statementsName ++ "Source")
    (s!"import {m.statementsName}\nimport ZkcFormalTests.WrittenBinding\n" ++
      "import Zkc.Tests.Frontend.PrintedPackageSupport\nopen ZkcFormal.Written\n" ++
      s!"namespace {m.space}\n{reader}end {m.space}\n") (text := false)

private def wrongOrdinal (work : System.FilePath) (m : Written.Module) (reader : String) :
    IO (IO Unit) := do
  -- Change only the source place of the decision, leaving its table slot and relation intact.
  let statements ← replaceOnce m.statements "⟨0, written'fn0," "⟨1, written'fn0,"
  let mutant := { m with statementsName := `WrongOrdinal.Stated, statements }
  let stated ← addStated work mutant
  let observed ← startReader work mutant reader
  return do
    stated.accepted "wrong decision ordinal"
    let (ok, output) ← observed
    let expected := "ZkcFormalTests.WrittenBinding.operands (written'subject.goalAt ⟨0, ⋯⟩)" ++
      " = (0, 0, 1, [1], some [])"
    refusedOutput "wrong decision ordinal" ok output [": error: Type mismatch", expected]
    unless (output.splitOn ": error").length == 2 do
      throw (IO.userError s!"wrong decision ordinal: expected one operand type mismatch\n{output}")

private def check (work : System.FilePath) (file source name : String)
    (questions : List (String × String)) (otherProofs : List (String × String) := [])
    (checkOrdinal := false) : IO (IO Unit) := do
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
  let names := (questions.map fun (label, _) => (label, label)) ++ otherProofs
  let text ← IO.FS.readFile s!"checks/{m.space}.lean.in"
  let opening := s!"import {m.statementsName}\n" ++ scope
  let formalImport := "ZkcFormal.Written.Soundness"
  let issued := { m with
    statedImports := formalImport :: m.statedImports
    statements := s!"import {formalImport}\n" ++ m.statements ++ scope ++ declarations ++ closing
    proof := opening ++ text ++ closing
    published := names.map fun (label, question) =>
      (.str m.space.toName label, .str m.space.toName (question ++ "Statement"))
    proved := names.map Prod.fst
    textLine := (opening.splitOn "\n").length
    textLines := (text.splitOn "\n").length }
  let observed ← startReader work issued reader
  let submitted ← startModule work name issued
  let control ← if checkOrdinal then wrongOrdinal work issued reader else pure (pure ())
  return do
    acceptedByLean s!"{name} source reader" (← observed)
    control
    discard submitted

def run (work : System.FilePath) : IO Unit := do
  let file := "fixtures/written-bound-guard.zkc"
  let source ← IO.FS.readFile file
  let unguarded ← replaceOnce source "guard @V claim" "guard @V true"
  let total ← replaceOnce source "IsSet(claim: bool): claim" "IsSet(claim: bool): true"
  let args := "model written'decision0 draws"
  let installed := s!"Soundness.Installed {args}"
  let admitted := s!"Soundness.AdmittedBound {args}"
  let result := s!"Soundness.Result {args} covers"
  let witnessed := s!"Soundness.Witnessed {args}"
  let rejected := "Soundness.Rejected model written'decision0 installed looseMember " ++
    "(.cons () (.cons false .nil))"
  let guard ← check work file source "BoundGuard" [
    ("directZero", installed ++ " 0"), ("directQuarter", installed ++ " (1/4)"),
    ("coveredZero", result ++ " 0"),
    ("rejectedFalse", rejected), ("met", witnessed),
    ("missingCount", s!"let t : CapTable := ⟨[]⟩; {result} t.total ∧ t.counted stored rootKey = false")]
    [("feeQuarter", "directQuarter")] (checkOrdinal := true)
  let returns ← check work file unguarded "BoundReturn" [
    ("rejectedFalse", rejected), ("met", witnessed),
    ("refutesInstalled", "¬ " ++ installed ++ " 0"), ("refutesAdmitted", "¬ " ++ admitted ++ " 0"),
    ("countedAtZero", "let t : CapTable := ⟨[⟨rootKey, .nil⟩]⟩; " ++
      s!"t.counted stored rootKey = true ∧ t.total = 0 ∧ ¬ {installed} t.total")]
  let always ← check work file total "BoundTotal" [
    ("allBounds", s!"∀ b, {result} b"), ("noWitness", "¬ " ++ witnessed)]
  [guard, returns, always].forM id

end WrittenBoundGuard

#eval IO.FS.withTempDir WrittenBoundGuard.run
