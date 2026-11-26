import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Written.Package
import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SyntaxHarness
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import ZkcFormalTests.WrittenSubject
import Zkc.Core.Admission.Theorems
import Zkc.Kernel
import Zkc.Vocabulary.Project

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace EitherCharge

/-- The source, with the charges of its two draws. -/
def source (first second : String) : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "protocol Either roles(P, V)(claim: bool @(P, V), first: index<8> @P, second: index<4> @P):\n" ++
  "    if claim:\n" ++
  "        a <- send first from P to V\n        x <- draw index<8> from V to P\n" ++
  "        guard @V x == a\n" ++
  "    else:\n" ++
  "        b <- send second from P to V\n        guard @V b != 3\n" ++
  "        y <- draw index<4> from V to P\n        guard @V y == b\n" ++
  s!"spec for Either:\n    proves @V Holds(claim)\n    charge sites.x <= {first}\n" ++
  s!"    charge sites.y <= {second}\n" ++
  "scheme Checked = Either:\n    prover P\n    construction interactive\n" ++
  "goal either = soundness(Checked, stage = written)\n"

/-- What the check asserts of what the frontend read of a source of the subject: the goal
selects the root; it reads the clause `proves @V Holds(claim)` on the first of the three ports,
decided by the verifier of the scheme; it gives no proof argument; and its coins are positions. -/
def reading : Reading where
  goals := ["either"]
  ports := #["claim", "first", "second"]
  clause := ⟨"proves", none, "V", "Holds", ["claim"], []⟩
  operands := #[0]

/-- A root with a stepped loop: three draws of positions of two, three and four, each followed
by a guard that it is not the first position, and then a guard on the claim. Each draw is
charged one half, which the text does not need: on a false claim the last guard stops the
run. -/
def steppedSource : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "protocol Steps roles(P, V)(claim: bool @(P, V)):\n" ++
  "    for i in 0..3:\n        r <- draw index<i + 2> from V to P\n        guard @V r != 0\n" ++
  "    guard @V claim\n" ++
  "spec for Steps:\n    proves @V Holds(claim)\n    charge sites.r <= 1 / 2\n" ++
  "scheme Checked = Steps:\n    prover P\n    construction interactive\n" ++
  "goal stepped = soundness(Checked, stage = written)\n"

def run : IO Unit := do
  let written ← read (source "1 / 8" "1 / 4") reading
  let goal ← written.goal
  -- The table of caps: the draws of the two arms, once each, as the arms of a choice, whose
  -- total is the larger arm.
  unless goal.total == 1 / 4 && (goal.caps.uses.map (·.caps)) ==
      [.choice (.item (.draw ⟨⟨1⟩, 1, 8, 1⟩) .nil) (.item (.draw ⟨⟨12⟩, 1, 4, 1⟩) .nil) .nil] && (goal.caps.uses.map fun use => use.draws.map fun draw =>
      (draw.numerator, draw.denominator, draw.count)) == [[(1, 8, 1), (1, 4, 1)]] do
    throw (IO.userError s!"the table of caps is not the two draws at 1/8 and 1/4: {repr goal.caps}")
  unless goal.siteLabels.map (·.2.1) == ["x", "y"] do
    throw (IO.userError s!"the draws are not named `x` and `y`: {goal.siteLabels.map (·.2.1)}")
  -- The stepped loop: three blocks, each with its draw.
  let stepped ← read steppedSource
    { goals := ["stepped"], ports := #["claim"],
      clause := ⟨"proves", none, "V", "Holds", ["claim"], []⟩, operands := #[0] }
  unless (stepped.goals.map fun goal => goal.siteLabels.map (·.2.1)) == [["r_0", "r_1", "r_2"]] do
    throw (IO.userError "the stepped loop has not a draw in each of three blocks")
  let low ← read (source "1 / 16" "1 / 16") reading
  unless (low.goals.map (·.total)) == [1 / 16] do
    throw (IO.userError "the low charges do not give a total of one sixteenth")

end EitherCharge

#eval show IO Unit from
  EitherCharge.run
