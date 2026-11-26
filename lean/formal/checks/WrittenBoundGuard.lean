import ZkcFormalTests.WrittenSubject

/-! Issue one guarded source and its two single-edit controls. The trusted propositions below
are frozen with the issued statements. Each proof template is judged against those propositions
by the ordinary written-subject comparator. -/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests.WrittenSubject

namespace WrittenBoundGuard

private def issue (file source name : String) : IO Written.Module := do
  let assembly ← Driver.assembleFiles ⟨file, Syntax.parseString file source⟩ ["../../libraries"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly "loose")
  let claims ← IO.ofExcept (goalClaims root ["loose"])
  unless claims.inputs == #["hidden", "claim"] && claims.goals.map (·.statement) == [#[1]] do
    throw <| IO.userError s!"{name}: expected IsSet(claim) at deployed input 1"
  let m ← IO.ofExcept ((Statements.mk claims claims.functionsBeforeRoot).module name {})
  unless m.refusals.isEmpty do throw <| IO.userError s!"{name}: {m.refusals}"
  return m

private def check (work : System.FilePath) (m : Written.Module)
    (questions : List (String × String)) (otherProofs : List (String × String) := []) : IO Pending := do
  let scope := s!"\nnamespace {m.space}\nopen Zkc.Core\n" ++ statementOpens ++
    "open StandardInterpretation (draws covers)\n"
  let closing := s!"\nend {m.space}\n"
  let declarations := String.join <| questions.map fun (label, prop) =>
    s!"def {label}Statement : Prop := {prop}\n"
  let names := (questions.map fun (label, _) => (label, label)) ++ otherProofs
  let text ← IO.FS.readFile s!"checks/{m.space}.lean.in"
  let opening := s!"import {m.statementsName}\n" ++ scope
  let formalImport := "ZkcFormal.Written.Soundness"
  startModule work m.space { m with
    statedImports := formalImport :: m.statedImports
    statements := s!"import {formalImport}\n" ++ m.statements ++ scope ++ declarations ++ closing
    proof := opening ++ text ++ closing
    published := names.map fun (label, question) =>
      (.str m.space.toName label, .str m.space.toName (question ++ "Statement"))
    proved := names.map Prod.fst
    textLine := (opening.splitOn "\n").length
    textLines := (text.splitOn "\n").length }

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
  let guard ← check work (← issue file source "BoundGuard") [
    ("directZero", installed ++ " 0"), ("directQuarter", installed ++ " (1/4)"),
    ("coveredZero", result ++ " 0"),
    ("rejectedFalse", rejected), ("met", witnessed),
    ("missingCount", s!"let t : CapTable := ⟨[]⟩; {result} t.total ∧ t.counted stored rootKey = false")]
    [("feeQuarter", "directQuarter")]
  let returns ← check work (← issue file unguarded "BoundReturn") [
    ("rejectedFalse", rejected), ("met", witnessed),
    ("refutesInstalled", "¬ " ++ installed ++ " 0"), ("refutesAdmitted", "¬ " ++ admitted ++ " 0"),
    ("countedAtZero", "let t : CapTable := ⟨[⟨rootKey, .nil⟩]⟩; " ++
      s!"t.counted stored rootKey = true ∧ t.total = 0 ∧ ¬ {installed} t.total")]
  let always ← check work (← issue file total "BoundTotal") [
    ("allBounds", s!"∀ b, {result} b"), ("noWitness", "¬ " ++ witnessed)]
  for submitted in [guard, returns, always] do discard submitted

end WrittenBoundGuard

#eval IO.FS.withTempDir WrittenBoundGuard.run
