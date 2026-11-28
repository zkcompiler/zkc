import ZkcFormalTests.WrittenSubject

/-!
A contract of a call, used where the call is.

The subject applies a protocol twice: `Round` hears a position, draws one and returns whether
they are the same; the root applies it to two positions and returns where the claim holds or a
round hit. The text (`checks/CallContract.lean.in`) proves one contract of `Round` (it returns
no hit, for a fee of one quarter, which its draw needs), at every start and under every
allowance that covers it, on the round's computation written out by hand, by Lean's `vcgen`.
It then judges the root twice from that one contract: on the root's process, by the rule of a
call at each of the two applications (`Contract.call`); and on the root's computation written
out by hand, by `vcgen` with the contract as the rule of each call (`FeeRules.call`, under the
renaming of the callee's roles). At each application the table's allowance covers the contract
below the application's path. The pair is judged by `lake comparator` against the issuer's
challenge. With the contract's fee at one eighth the text is refused.

With `ZKC_WORK` naming a folder the check's project is kept there.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace CallContract

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

/-- The source: the root applies `Round` twice. -/
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
  let issued ← publicationOf twiceSource "twice" "Twice" ["ZkcFormal.Written.FeeRules"]
  add (toString issued.dataName) issued.data .statements
  add (toString issued.challengeName) issued.challenge .challenge
  add (toString issued.viewsName) issued.views .statements
  add (toString issued.feesName) issued.fees .statements
  let text ← IO.FS.readFile "checks/CallContract.lean.in"
  add "Twice.Proof" (issued.proof text) .module
  -- the same text with the contract's fee at one eighth, below what its draw is paid
  add "Twice.Cheap" (issued.proof (← replaceOnce text "fee := 1 / 4" "fee := 1 / 8")) .module
  SubjectProject.expect project "Twice" [(issued.challengeName, `Twice.Proof)] issued.published
    WrittenSubject.allowed
  let (ok, output) ← SubjectProject.result project `Twice.Proof
  unless ok do throw (IO.userError s!"Twice: Lean refused the text\n{output}")
  let (verdict, words) ← SubjectProject.judge project "Twice"
  unless verdict == .accepted do
    throw (IO.userError s!"Twice: the proof through the contract was not accepted\n{words}")
  IO.println "Twice: judgment accepted (one contract of the round, used at its two applications)"
  let (ok, output) ← SubjectProject.result project `Twice.Cheap
  if ok then throw (IO.userError "a contract with a fee below what its draw is paid was proved to hold")
  -- the first error is in the proof that the contract holds: the fee does not hold what the
  -- draw is paid
  let line (name : String) : Nat :=
    ((text.splitOn s!"theorem {name}").head!.splitOn "\n").length + issued.textLine - 1
  let firstError := ((output.splitOn "Twice/Cheap.lean:").filterMap fun piece =>
    (piece.takeWhile (· != ':')).toNat?).head?
  unless firstError.any fun at_ => line "roundHolds" ≤ at_ ∧ at_ < line "judged" do
    throw (IO.userError s!"the cheap contract is not refused in the proof that it holds\n{output}")
  IO.println "Twice.Cheap: refused (a contract's fee below what its draw is paid is not proved to hold)"

end CallContract

#eval show IO Unit from do
  match ← IO.getEnv "ZKC_WORK" with
  | some work => CallContract.run work
  | none => IO.FS.withTempDir CallContract.run
