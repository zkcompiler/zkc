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
    "relation Holds(b: bool): b\nprotocol Check roles(P,V)(b: bool @(P,V)):\n    guard @V root(b)\n" ++
    "spec for Check:\n    proves @V Holds(b)\nscheme Checked = Check:\n    prover P\n" ++
    "    construction interactive\ngoal root0 = soundness(Checked)\n"
  let called ← statementsFor ⟨"calling.zkc", Syntax.parseString "calling.zkc" helper⟩ ["root0"]
  unless called.functions.map Prod.snd == [0] do throw (IO.userError "expected the helper at key zero")
  let modules := [← IO.ofExcept (shared.module "SharedLabels" {}), issued.publication,
    ← IO.ofExcept (called.module "HelperLabels" {})]
  let pending ← modules.mapM fun publication => do
    let stated ← addStated work publication
    let challenge ← addChallenge work publication.space publication
    return (stated, challenge)
  for (stated, challenge) in pending do
    stated.accepted stated.space
    let (ok, output) ← leanOn work challenge
    unless ok do throw (IO.userError s!"{challenge}: {output}")

/-- Elaborate the propositions issued for these goals with their proofs at the source field. -/
def checkClaims (work : System.FilePath) (name fixture : String) (goals theorems : List String)
    (edits : List (String × String) := []) (refusedHash := false) : IO Unit := do
  let statements ← statementsFor (← source s!"fixtures/{fixture}.zkc" edits) goals
  let issued ← IO.ofExcept (statements.module name {})
  match issued.refusals with
  | [] => if refusedHash then throw (IO.userError "issued the goal that reaches SHA-256")
  | [why] => unless refusedHash && why.contains "bad:" && why.contains "sha256" do
      throw (IO.userError why)
  | other => throw (IO.userError s!"unexpected refusals {other}")
  let proof ← IO.FS.readFile s!"checks/{name}.lean.in"
  if refusedHash then
    let publication ← IO.ofExcept (statements.module name
      {text := proof, theorems := ["good_judged", "good_witnessed"]})
    unless publication.published.map (·.1.getString!) ==
        ["good_installed", "good_sound", "good_result", "good_met"] do
      throw (IO.userError s!"unexpected publication {publication.published}")
    let checked ← startLakeLean work name (asOne [publication])
    let (ok, output) ← checked
    acceptedOutput name ok output (publication.stated ++ publication.proved) allowed
    return
  let checked ← startLakeLean work name (issued.statements ++ proof)
  let (ok, output) ← checked
  acceptedOutput name ok output (issued.stated ++ theorems) allowed

#eval IO.FS.withTempDir checkLinkedCeilings
#eval checkEveryGoalIssued
#eval checkSharedCoverage
#eval IO.FS.withTempDir checkPublicationNames
#eval IO.FS.withTempDir fun w => checkClaims w "ThirdElement" "third-element" ["sound"]
  ["sound_judged", "field_claim", "hypotheses_met"]
#eval IO.FS.withTempDir fun w => checkClaims w "Unguarded" "third-element" ["sound"]
  ["false_at_source"] [("        guard @V b\nspec", "spec")]
#eval IO.FS.withTempDir fun w => checkClaims w "ScalarLiteral" "scalar-literal" ["sound"] ["literal_claim"]
#eval IO.FS.withTempDir fun w => checkClaims w "ZeroRounds" "zero-round-sumcheck" ["sound"] ["evaluate_one", "sum_claim"]
#eval IO.FS.withTempDir fun w => checkClaims w "PointSum" "point-sum" ["sound"] ["checked", "hypotheses_met"]
#eval IO.FS.withTempDir fun w => checkClaims w "Siblings" "sibling-relations" ["zero"] ["zero_checked", "zero_met"]
#eval IO.FS.withTempDir fun w => checkClaims w "Siblings" "sibling-relations" ["zero", "one"] ["zero_checked", "zero_met"]
#eval IO.FS.withTempDir fun w => checkClaims w "HashRelation" "hash-relation" ["good", "bad"] ["result"] (refusedHash := true)

/-- Submit the surviving target from a mixed request to the same comparator as all other
written subjects. The proof consumes the exact trusted module that the batch issued. -/
private def judgeIssuedGoal (work : System.FilePath) : IO Unit := do
  let assembly ← Driver.assembleFiles (← source "fixtures/hash-relation.zkc" []) ["../../libraries"]
  let results := issueSoundnessGoals assembly ["bad", "mixed::good", "good"]
  let #[bad, good, alias_] := results | throw (IO.userError "lost a requested goal")
  unless bad.outcome.isOk == false && !allGoalsIssued results && good.path == alias_.path do
    throw (IO.userError "unexpected mixed issuance")
  let issued ← IO.ofExcept good.outcome
  let proof ← IO.FS.readFile "checks/HashRelation.lean.in"
  let publication ← IO.ofExcept (issued.statements.module issued.publication.space
    { text := proof, theorems := ["good_judged", "good_witnessed"] })
  unless publication.statements == issued.publication.statements &&
      publication.challenge == issued.publication.challenge do
    throw (IO.userError "the submission changed the issued challenge")
  let finish ← startModule work publication.space publication
  discard finish

#eval IO.FS.withTempDir judgeIssuedGoal
