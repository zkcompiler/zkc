import ZkcFormalTests.WrittenSubject

/-!
A goal proved on the form of its program.

The subject is the guessing protocol of three rounds: in each round the verifier hears a
position and draws one, and it returns where the claim holds or a round hit. The text
(`checks/FormProof.lean.in`) declares the form of the verifier's program with its equation
(`form_of_role`), and proves the goal's judgment by fees on that form by Lean's `vcgen` with the
rule of each effect: an invariant of the loop and the choice at its draw are what the text
gives. The pair is judged by `lake comparator` against the issuer's challenge.

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

def run (work : System.FilePath) : IO Unit := do
  let project := projectOf work
  let add (name text : String) (kind : SubjectProject.Kind) : IO Unit :=
    discard <| SubjectProject.add project name.toName text kind
  let issued ← publicationOf guessSource "guessing" "Guess"
    ["ZkcFormal.Written.FeeRules", "ZkcFormal.Form.Produce"]
  add (toString issued.dataName) issued.data .statements
  add (toString issued.challengeName) issued.challenge .challenge
  add (toString issued.viewsName) issued.views .statements
  add (toString issued.feesName) issued.fees .statements
  add "Guess.Proof" (issued.proof (← IO.FS.readFile "checks/FormProof.lean.in")) .module
  SubjectProject.expect project "Guess" [(issued.challengeName, `Guess.Proof)] issued.published
    WrittenSubject.allowed
  let (ok, output) ← SubjectProject.result project `Guess.Proof
  unless ok do throw (IO.userError s!"Guess: Lean refused the text\n{output}")
  let (verdict, words) ← SubjectProject.judge project "Guess"
  unless verdict == .accepted do
    throw (IO.userError s!"Guess: the proof on the form was not accepted\n{words}")
  IO.println "Guess: judgment accepted (the goal proved on the form of its program)"

end FormProof

#eval show IO Unit from do
  match ← IO.getEnv "ZKC_WORK" with
  | some work => FormProof.run work
  | none => IO.FS.withTempDir FormProof.run
