import ZkcFormalTests.WrittenSubject

/-!
A goal proved on the form of its program.

The subject is the guessing protocol of three rounds: in each round the verifier hears a
position and draws one, and it returns where the claim holds or a round hit. A module of one
line publishes the forms of the subject (`publish_forms`), and the text
(`checks/FormProof.lean.in`) proves the goal's judgment by fees on the registered form of the
verifier's program by Lean's `vcgen` with the rule of each effect: an invariant of the loop and
the choice at its draw are what the text gives, and its conditions are closed with `simp` and
arithmetic. The pair is judged by `lake comparator` against the issuer's challenge.

With `ZKC_WORK` naming a folder the check's project is kept there.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace FormProof

/-- What the issuer publishes for a goal of a source, in the name space `space`, with the
modules that the author's text imports. -/
def publicationOf (text goal space : String) (imports : List String) : IO Publication := do
  let assembly ← Driver.assembleFiles ⟨"source.zkc", Syntax.parseString "source.zkc" text⟩
    ["../../libraries"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly goal)
  let claims ← IO.ofExcept (goalClaims root [goal])
  let issued ← IO.ofExcept ((⟨claims⟩ : Statements).publication space imports)
  unless issued.refusals.isEmpty do throw (IO.userError s!"{issued.refusals}")
  return issued

/-- The source: three rounds of guessing a position of eight. -/
def guessSource : String :=
  "module t\nuse zkc::security::{soundness}\nsection <n: nat>:\n" ++
  "    relation Holds(claim: bool): claim\n" ++
  "    protocol Guess roles(P, V)(claim: bool @(P, V), guess: index<8> @P):\n" ++
  "        mut hit = false\n        for i in 0..n:\n" ++
  "            g <- send guess from P to V\n            r <- draw index<8> from V to P\n" ++
  "            hit := hit or (r == g)\n        guard @V claim or hit\n" ++
  "    spec for Guess:\n        proves @V Holds(claim)\n        charge sites.r <= 1 / 8\n" ++
  "scheme Checked = Guess<3>:\n    prover P\n    construction interactive\n" ++
  "goal guessing = soundness(Checked, stage = written)\n"

/-- The source of two applications of a round that calls a function: the round's verifier hears
a position, draws one and returns whether they are the same; the root returns where the claim
holds or a round hit. -/
def twiceSource : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "def same(a: index<4>, b: index<4>) -> bool: a == b\n" ++
  "protocol Round roles(P, V)(sent: index<4> @P) -> (hit: bool @(P, V), drawn: index<4> @(P, V)):\n" ++
  "    x <- send sent from P to V\n    r <- draw index<4> from V to P\n" ++
  "    return (same(r, x), r)\n" ++
  "spec for Round:\n    charge sites.r <= 1 / 4\n" ++
  "protocol Twice roles(P, V)(claim: bool @(P, V), first: index<4> @P, second: index<4> @P):\n" ++
  "    a <- Round(first)\n    b <- Round(second)\n" ++
  "    guard @V claim or a.hit or b.hit\n" ++
  "spec for Twice:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Twice:\n    prover P\n    construction interactive\n" ++
  "goal twice = soundness(Checked, stage = written)\n"

def run (work : System.FilePath) : IO Unit := do
  let project := projectOf work
  let add (name text : String) (kind : SubjectProject.Kind) : IO Unit :=
    discard <| SubjectProject.add project name.toName text kind
  -- each subject: its name space, its source, its goal, the author's text, and what the text shows
  let subjects := [
    ("Guess", guessSource, "guessing", "checks/FormProof.lean.in",
      "a loop's invariant and the choice at its draw"),
    ("Twice", twiceSource, "twice", "checks/FormProofCall.lean.in",
      "one contract of the round, proved on the round's form with the function it calls, used at the two applications in the root's form")]
  for (space, source, goal, text, _) in subjects do
    let issued ← publicationOf source goal space
      ["ZkcFormal.Written.FeeRules", s!"{space}.Forms"]
    add (toString issued.dataName) issued.data .statements
    -- the forms of the subject: one line, on the solution's side
    add s!"{space}.Forms"
      (s!"import {issued.dataName}\nimport ZkcFormal.Form.Publish\n\nopen Zkc.Core\n" ++
        s!"namespace {space}\n\npublish_forms written'subject\n\nend {space}\n") .module
    add (toString issued.challengeName) issued.challenge .challenge
    add (toString issued.viewsName) issued.views .statements
    add (toString issued.feesName) issued.fees .statements
    add s!"{space}.Proof" (issued.proof (← IO.FS.readFile text)) .module
    SubjectProject.expect project space [(issued.challengeName, s!"{space}.Proof".toName)]
      issued.published WrittenSubject.allowed
  for (space, _, _, _, shown) in subjects do
    let (ok, output) ← SubjectProject.result project s!"{space}.Proof".toName
    unless ok do throw (IO.userError s!"{space}: Lean refused the text\n{output}")
    -- the register is read where it is imported: the text's module did not publish the forms
    unless output.contains s!"registered forms:\n" &&
        output.contains s!"{space}.protocol" && output.contains s!"{space}.function" do
      throw (IO.userError s!"{space}: the text's module does not read the register of forms\n{output}")
    let (verdict, words) ← SubjectProject.judge project space
    unless verdict == .accepted do
      throw (IO.userError s!"{space}: the proof on the registered forms was not accepted\n{words}")
    IO.println s!"{space}: judgment accepted (the goal proved on its registered forms: {shown})"

end FormProof

#eval show IO Unit from do
  match ← IO.getEnv "ZKC_WORK" with
  | some work => FormProof.run work
  | none => IO.FS.withTempDir FormProof.run
