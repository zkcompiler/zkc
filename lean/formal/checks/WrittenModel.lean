import ZkcFormalTests.WrittenSubject

open Zkc.Frontend Zkc.Frontend.Written ZkcFormalTests.WrittenSubject
open Zkc.Tests.Frontend.PrintedPackageSupport

private def statementsFor (input : SourceInput) (goals : List String) : IO Statements := do
  let first :: _ := goals | throw (IO.userError "expected a goal")
  let assembly ← Driver.assembleFiles input ["../../libraries", "../../examples", "../../examples/support"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly first)
  let claims ← IO.ofExcept (goalClaims root goals)
  return ⟨claims, claims.functionsBeforeRoot⟩

/-- A package that links a project primitive has no model of it: its goals are not issued, with or
without a ceiling. -/
def checkLinkedPrimitive : IO Unit := do
  let file := "../../examples/gkr_example.zkc"
  let scheme ← IO.FS.readFile file
  let subject (bound : String) := statementsFor ⟨file, Syntax.parseString file
    (scheme ++ s!"\ngoal bound = soundness(Proof, stage = written, statement = fixed) <= {bound}\n")⟩ ["bound"]
  for bound in ["1 / 2", "0"] do
    let statements ← subject bound
    unless !statements.package.bindings.rows.isEmpty do throw (IO.userError "expected project bindings")
    match statements.publication "LayerCeiling" with
    | .error why => unless why.contains "project primitive" do throw (IO.userError why)
    | .ok _ => throw (IO.userError "issued the goals of a package that links a project primitive")

/-- Interleaved goals of one scheme: a goal whose relation the standard interpretation does not
cover is reported by its name, also a second one of the same relation, and the rows that are
issued are the covered goals', named by their paths. -/
def checkSharedCoverage : IO Unit := do
  let bad := "goal bad = soundness(Checked, spec e = 1)"
  let more := bad ++ "\ngoal again = soundness(Checked, spec e = 0)\ngoal alsoBad = soundness(Checked, spec e = 1)"
  let input ← source "fixtures/hash-relation.zkc" [(bad, more)]
  let statements ← statementsFor input ["good", "bad", "again", "alsoBad"]
  let issued ← IO.ofExcept (statements.publication "SharedCoverage")
  let rows := issued.published.map fun name => (name.toString.splitOn ".").reverse.take 2 |>.reverse
  unless rows == [["good", "sound"], ["good", "met"], ["again", "sound"], ["again", "met"]] do
    throw (IO.userError s!"expected the published theorems of good and again, got {issued.published}")
  let [first, second] := issued.refusals | throw (IO.userError s!"unexpected refusals {issued.refusals}")
  unless first.startsWith "bad:" && second.startsWith "alsoBad:" &&
      first.contains "sha256" && second.contains "sha256" do
    throw (IO.userError s!"unexpected refusals {issued.refusals}")

/-- Check both sides of issuance with exactly their declared imports: the data module and the
challenge of each publication are read by Lean. The shared package has goals named `root` and
`verifier`, whose labels are names of the installation; a second source calls helpers whose
names are like generated ones; a third names a goal and a port like a view's binders. A
published theorem is named by the path of its goal. -/
private def checkPublicationNames (work : System.FilePath) : IO Unit := do
  let goal (name : String) := s!"goal {name} = soundness(Checked, spec e = 0)"
  let long := String.ofList (List.replicate 42 '가')
  let input ← source "fixtures/hash-relation.zkc"
    [(goal "good", "\n".intercalate (["root", "verifier", long].map goal))]
  let shared ← statementsFor input ["root", "verifier"]
  let sharedIssued ← IO.ofExcept (shared.publication "SharedLabels")
  unless sharedIssued.published.map (fun name => (name.toString.splitOn ".").reverse.take 2 |>.reverse) ==
      [["root", "sound"], ["root", "met"], ["verifier", "sound"], ["verifier", "met"]] do
    throw (IO.userError s!"the published theorems lost the source names: {sharedIssued.published}")
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
  let modules := [sharedIssued, issued.publication,
    ← IO.ofExcept (called.publication "HelperLabels"), ← IO.ofExcept (binderStatements.publication "InputLabels")].map
      (Module.ofPublication ·)
  let pending ← modules.mapM fun publication => do
    let stated ← addStated work publication
    let challenge ← addChallenge work publication.space publication
    return (stated, challenge)
  for (stated, challenge) in pending do
    stated.accepted stated.space
    let (ok, output) ← leanOn work challenge
    unless ok do throw (IO.userError s!"{challenge}: {output}")

#eval checkLinkedPrimitive
#eval checkSharedCoverage
#eval IO.FS.withTempDir checkPublicationNames
