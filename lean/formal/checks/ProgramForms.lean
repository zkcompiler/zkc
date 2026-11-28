import ZkcFormalTests.WrittenSubject

/-!
The form of a stored program, with its equation, on the issued subjects.

For each source the issuer's data module is built, and `form_of_role` declares the form of the
root's deciding role and the equation that it is the reading of the role's meaning, whose proof
is one application of the library's theorem. The kernel accepts the equation, and it rests on
`propext` and `Quot.sound` at most: the form holds for every model.

The sources between them have a loop with a carried value (Guess), a choice with a guard in each
arm (Either), a stepped loop written out as blocks (Steps), and two applications of a protocol
that calls a function (Twice).

With `ZKC_WORK` naming a folder the check's project is kept there.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace ProgramForms

def guess : String :=
  "module t\nuse zkc::security::{soundness}\nsection <n: nat>:\n" ++
  "    relation Holds(claim: bool): claim\n" ++
  "    protocol Guess roles(P, V)(claim: bool @(P, V), guess: index<8> @P):\n" ++
  "        mut hit = false\n        for i in 0..n:\n" ++
  "            g <- send guess from P to V\n            r <- draw index<8> from V to P\n" ++
  "            hit := hit or (r == g)\n        guard @V claim or hit\n" ++
  "    spec for Guess:\n        proves @V Holds(claim)\n        charge sites.r <= 1 / 8\n" ++
  "scheme Checked = Guess<3>:\n    prover P\n    construction interactive\n" ++
  "goal guessing = soundness(Checked, stage = written)\n"

def either : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "protocol Either roles(P, V)(claim: bool @(P, V), first: index<8> @P, second: index<4> @P):\n" ++
  "    if claim:\n" ++
  "        a <- send first from P to V\n        x <- draw index<8> from V to P\n" ++
  "        guard @V x == a\n" ++
  "    else:\n" ++
  "        b <- send second from P to V\n        guard @V b != 3\n" ++
  "        y <- draw index<4> from V to P\n        guard @V y == b\n" ++
  "spec for Either:\n    proves @V Holds(claim)\n    charge sites.x <= 1 / 8\n" ++
  "    charge sites.y <= 1 / 4\n" ++
  "scheme Checked = Either:\n    prover P\n    construction interactive\n" ++
  "goal either = soundness(Checked, stage = written)\n"

def stepped : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "protocol Steps roles(P, V)(claim: bool @(P, V)):\n" ++
  "    for i in 0..3:\n        r <- draw index<i + 2> from V to P\n        guard @V r != 0\n" ++
  "    guard @V claim\n" ++
  "spec for Steps:\n    proves @V Holds(claim)\n    charge sites.r <= 1 / 4\n" ++
  "scheme Checked = Steps:\n    prover P\n    construction interactive\n" ++
  "goal stepped = soundness(Checked, stage = written)\n"

def twice : String :=
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

/-- The data module that the issuer writes for a goal of a source, in the name space `space`. -/
def dataOf (text goal space : String) : IO Publication := do
  let assembly ← Driver.assembleFiles ⟨"source.zkc", Syntax.parseString "source.zkc" text⟩
    ["../../libraries"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly goal)
  let claims ← IO.ofExcept (goalClaims root [goal])
  let issued ← IO.ofExcept ((⟨claims⟩ : Statements).publication space)
  unless issued.refusals.isEmpty do throw (IO.userError s!"{issued.refusals}")
  return issued

def run (work : System.FilePath) : IO Unit := do
  let project := projectOf work
  let subjects := [("Guess", guess, "guessing"), ("Either", either, "either"),
    ("Steps", stepped, "stepped"), ("Twice", twice, "twice")]
  for (space, text, goal) in subjects do
    let issued ← dataOf text goal space
    discard <| SubjectProject.add project issued.dataName issued.data .statements
    discard <| SubjectProject.add project s!"{space}Forms".toName
      (s!"import {issued.dataName}\nimport ZkcFormal.Form.Produce\n\nopen Zkc.Core {space}\n\n" ++
        "form_of_role Root : installed, rootMember, verifierRole\n\n#print axioms Root.reads\n")
      .statements
  for (space, _, _) in subjects do
    let (ok, output) ← SubjectProject.result project s!"{space}Forms".toName
    unless ok do throw (IO.userError s!"{space}: the form of the root's deciding role is refused\n{output}")
    unless output.contains "'Root.reads' depends on axioms: [propext, Quot.sound]" do
      throw (IO.userError s!"{space}: the form's equation does not rest on propext and Quot.sound alone\n{output}")
    IO.println s!"{space}: the root's form and its equation are accepted"

end ProgramForms

#eval show IO Unit from do
  match ← IO.getEnv "ZKC_WORK" with
  | some work => ProgramForms.run work
  | none => IO.FS.withTempDir ProgramForms.run
