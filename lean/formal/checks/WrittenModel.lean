import ZkcFormalTests.WrittenSubject

open Zkc.Frontend Zkc.Frontend.Written ZkcFormalTests.WrittenSubject
open Zkc.Tests.Frontend.PrintedPackageSupport

private def statementsFor (input : SourceInput) (goals : List String) : IO Statements := do
  let first :: _ := goals | throw (IO.userError "expected a goal")
  let assembly ← Driver.assembleFiles input ["../../libraries", "../../examples", "../../examples/support"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly first)
  let claims ← IO.ofExcept (goalClaims root goals)
  return ⟨claims, claims.functionsBeforeRoot⟩

def checkLinkedCeilings (work : System.FilePath) : IO Unit := do
  let file := "../../examples/gkr_example.zkc"
  let scheme ← IO.FS.readFile file
  let subject (bound : Nat) := statementsFor ⟨file, Syntax.parseString file
    (scheme ++ s!"\ngoal bound = soundness(Proof, stage = written, statement = fixed) <= {bound}\n")⟩ ["bound"]
  let high ← subject 1
  unless !high.package.bindings.rows.isEmpty do throw (IO.userError "expected project bindings")
  let issued ← IO.ofExcept (high.ceilingModule "LayerCeiling")
  match (← subject 0).ceilingModule "LayerCeiling" with
  | .error why => unless why.contains "GL4" do throw (IO.userError why)
  | .ok _ => throw (IO.userError "accepted a ceiling below the total")
  let checked ← startLakeLean work "LayerCeiling" issued.text (text := false)
  let (ok, output) ← checked
  acceptedOutput "LayerCeiling" ok output issued.theorems allowed

/-- A subject of a check asks for every one of its goals: the harness refuses a subject one of
whose goals is not issued, and does not judge the rest in its place. -/
def checkEveryGoalIssued : IO Unit := do
  let statements ← statementsFor (← source "fixtures/hash-relation.zkc" []) ["good", "bad"]
  let subject : Subject := ⟨"", statements⟩
  let attempt ← (subject.module "HashRelation" { text := "", theorems := [] }).toBaseIO
  match attempt with
  | .ok _ => throw (IO.userError "a subject with a refused goal was assembled")
  | .error why =>
    unless (toString why).contains "bad:" && (toString why).contains "sha256" do throw why

/-- Interleaved goals reuse their relation's coverage decision. Refusals keep the
name of each goal, including a second goal for the unsupported relation. -/
def checkSharedCoverage : IO Unit := do
  let bad := "goal bad = soundness(Checked, spec e = 1)"
  let more := bad ++ "\ngoal again = soundness(Checked, spec e = 0)\ngoal alsoBad = soundness(Checked, spec e = 1)"
  let input ← source "fixtures/hash-relation.zkc" [(bad, more)]
  let statements ← statementsFor input ["good", "bad", "again", "alsoBad"]
  let issued ← IO.ofExcept (statements.coverageModule "SharedCoverage")
  unless issued.theorems == ["good_covered", "again_covered"] &&
      issued.text.contains "rootKey goodKey = true := by decide +kernel" &&
      issued.text.contains "rootKey againKey = true := good_covered" do
    throw (IO.userError "expected two coverage names and one decision")
  let [first, second] := issued.refusals | throw (IO.userError s!"unexpected refusals {issued.refusals}")
  unless first.startsWith "bad:" && second.startsWith "alsoBad:" &&
      first.contains "sha256" && second.contains "sha256" do
    throw (IO.userError s!"unexpected refusals {issued.refusals}")

/-- Check both sides of issuance with exactly their declared imports. The shared package
has two labels that used to collide with fixed declarations; a second source calls a
helper whose old fallback label was itself the goal's name. -/
private def checkPublicationNames (work : System.FilePath) : IO Unit := do
  let goal (name : String) := s!"goal {name} = soundness(Checked, spec e = 0)"
  let long := String.ofList (List.replicate 42 '가')
  let input ← source "fixtures/hash-relation.zkc"
    [(goal "good", "\n".intercalate (["root", "verifier", long].map goal))]
  let shared ← statementsFor input ["root", "verifier"]
  unless (shared.publicationPairs "SharedLabels").map (·.1.getString!) ==
      ["root_installed", "root_sound", "root_result", "root_met",
       "verifier_installed", "verifier_sound", "verifier_result", "verifier_met"] do
    throw (IO.userError "the public challenge lost the source names")
  let assembly ← Driver.assembleFiles input ["../../libraries"]
  let #[result] := issueSoundnessGoals assembly [long] | throw (IO.userError "missing goal")
  let issued ← IO.ofExcept result.outcome
  let helper := "module calling\nuse zkc::security::{soundness}\ndef root(b: bool) -> bool: b\n" ++
    "def sound_cap_r(b: bool) -> bool: b\nrelation Holds(b: bool): b\n" ++
    "protocol Check roles(P,V)(b: bool @(P,V)):\n    covered <- draw index<2> from V to P\n" ++
    "    rKey <- draw index<2> from V to P\n    guard @V sound_cap_r(root(b))\n" ++
    "spec for Check:\n    proves @V Holds(b)\n    charge sites.rKey <= 1 / 2\n" ++
    "scheme Checked = Check:\n    prover P\n    construction interactive\n" ++
    "goal root0 = soundness(Checked)\ngoal sound = soundness(Checked)\ngoal site = soundness(Checked)\n"
  let called ← statementsFor ⟨"calling.zkc", Syntax.parseString "calling.zkc" helper⟩ ["root0", "sound", "site"]
  unless (called.functions.map Prod.snd).contains 0 do throw (IO.userError "expected the helper at key zero")
  let binders ← source "fixtures/hash-relation.zkc" [(goal "good", goal "input_b"),
    ("(b: bool @(P,V), xs:", "(bCaps: bool @(P,V), xs:"),
    ("guard @V b", "guard @V bCaps"), ("Holds(b, xs)", "Holds(bCaps, xs)")]
  let binderStatements ← statementsFor binders ["input_b"]
  let modules := [← IO.ofExcept (shared.module "SharedLabels" {}), issued.publication,
    ← IO.ofExcept (called.module "HelperLabels" {}), ← IO.ofExcept (binderStatements.module "InputLabels" {})]
  let pending ← modules.mapM fun publication => do
    let stated ← addStated work publication
    let challenge ← addChallenge work publication.space publication
    return (stated, challenge)
  for (stated, challenge) in pending do
    stated.accepted stated.space
    let (ok, output) ← leanOn work challenge
    unless ok do throw (IO.userError s!"{challenge}: {output}")

#eval IO.FS.withTempDir checkLinkedCeilings
#eval checkEveryGoalIssued
#eval checkSharedCoverage
#eval IO.FS.withTempDir checkPublicationNames
