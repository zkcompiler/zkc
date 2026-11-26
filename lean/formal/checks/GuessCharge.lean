import ZkcFormalTests.WrittenSubject

/-! The source rounds, draw count, relation and witness of Guess. -/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace GuessCharge

/-- The source, with its number of rounds and the charge of the draw. -/
def source (rounds charge : String) : String :=
  "module t\nuse zkc::security::{soundness}\nsection <n: nat>:\n" ++
  "    relation Holds(claim: bool): claim\n" ++
  "    protocol Guess roles(P, V)(claim: bool @(P, V), guess: index<8> @P):\n" ++
  "        mut hit = false\n        for i in 0..n:\n" ++
  "            g <- send guess from P to V\n            r <- draw index<8> from V to P\n" ++
  "            hit := hit or (r == g)\n        guard @V claim or hit\n" ++
  s!"    spec for Guess:\n        proves @V Holds(claim)\n        charge sites.r <= {charge}\n" ++
  s!"scheme Checked = Guess<{rounds}>:\n    prover P\n    construction interactive\n" ++
  "goal guessing = soundness(Checked, stage = written)\n"

/-- What the check asserts of what the frontend read of a source of the subject: the goal
selects the root; it reads the clause `proves @V Holds(claim)` on the first of the two ports,
decided by the verifier of the scheme; it gives no proof argument; and its coins are positions,
so the statements are about the standard model. -/
def reading : Reading where
  goals := ["guessing"]
  ports := #["claim", "guess"]
  clause := ⟨"proves", none, "V", "Holds", ["claim"], []⟩
  operands := #[0]

def run (template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let template ← IO.FS.readFile template
  let written ← read (source "3" "1 / 8") reading
  let goal ← written.goal
  let claims := written.statements.claims
  unless claims.root == 0 && (claims.verifier, claims.prover) == (1, 0) do
    throw (IO.userError "the root and the roles of the source are not where they were")
  -- The table of caps, as the frontend read it: the draw of the loop's body, at one eighth,
  -- three times.
  unless goal.caps == ⟨[(.flat ⟨0⟩ [⟨⟨3⟩, 1, 8, 3⟩] [])]⟩ && goal.total == 3 / 8 do
    throw (IO.userError s!"the table of caps is not the draw at 1/8, three times: {repr goal.caps}")

  -- The charge halved in the source: the program is what it was, and the cap is another.
  let halved ← read (source "3" "1 / 16") reading
  unless halved.package == written.package &&
      (halved.goals.map (·.caps)) == [⟨[(.flat ⟨0⟩ [⟨⟨3⟩, 1, 16, 3⟩] [])]⟩] do
    throw (IO.userError "the halved charge changed the package, or is not half at the draw")
  -- Four rounds: the count of the draw is four.
  let four ← read (source "4" "1 / 8") reading
  unless (four.goals.map fun goal => (goal.caps, goal.total)) ==
      [(⟨[(.flat ⟨0⟩ [⟨⟨3⟩, 1, 8, 4⟩] [])]⟩, 1 / 2)] do
    throw (IO.userError "with four rounds the draw is not counted four times")
  let m ← written.module "Guess" { text := template, theorems := [] }
  let lemmas ← startLemmas work "Guess" m template ["guessing_relation", "guessing_witnessed"] written
  lemmas

end GuessCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work => GuessCharge.run "checks/GuessCharge.lean.in" work
