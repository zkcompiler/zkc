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
open Zkc.Subject (Cap CapTable)
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace TwiceCharge

/-- The function and the protocol that the roots apply, with the charge of its draw and the
body of the function. -/
def round (charge : String) (same : String := "a == b") : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  s!"def same(a: index<4>, b: index<4>) -> bool: {same}\n" ++
  "protocol Round roles(P, V)(sent: index<4> @P) -> (hit: bool @(P, V), drawn: index<4> @(P, V)):\n" ++
  "    x <- send sent from P to V\n    r <- draw index<4> from V to P\n" ++
  "    return (same(r, x), r)\n" ++
  s!"spec for Round:\n    charge sites.r <= {charge}\n"

/-- The source: the root applies `Round` twice. -/
def source (charge : String) (same : String := "a == b") : String :=
  round charge same ++
  "protocol Twice roles(P, V)(claim: bool @(P, V), first: index<4> @P, second: index<4> @P):\n" ++
  "    a <- Round(first)\n    b <- Round(second)\n" ++
  "    guard @V claim or a.hit or b.hit\n" ++
  "spec for Twice:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Twice:\n    prover P\n    construction interactive\n" ++
  "goal twice = soundness(Checked, stage = written)\n"

/-- A root that applies a protocol that applies `Round` twice. The root names its roles in the
other order: its verifier is its first role, and the second role of `Pair` and of `Round`. -/
def nestedSource : String :=
  round "1 / 4" ++
  "protocol Pair roles(P, V)(first: index<4> @P, second: index<4> @P) -> (hit: bool @(P, V), last: index<4> @(P, V)):\n" ++
  "    a <- Round(first)\n    b <- Round(second)\n" ++
  "    return (a.hit or b.hit, b.drawn)\n" ++
  "protocol Nested roles(V, P)(claim: bool @(P, V), first: index<4> @P, second: index<4> @P):\n" ++
  "    pair <- Pair(first, second)\n" ++
  "    guard @V claim or pair.hit\n" ++
  "spec for Nested:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Nested:\n    prover P\n    construction interactive\n" ++
  "goal nested = soundness(Checked, stage = written)\n"

/-- A root whose loop applies `Round` three times to one position and returns where the claim
holds or a round hit: an application in the body of a loop. -/
def loopedSource : String :=
  round "1 / 4" ++
  "protocol Looped roles(P, V)(claim: bool @(P, V), guess: index<4> @P):\n" ++
  "    mut hit = false\n    for i in 0..3:\n" ++
  "        a <- Round(guess)\n        hit := hit or a.hit\n" ++
  "    guard @V claim or hit\n" ++
  "spec for Looped:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Looped:\n    prover P\n    construction interactive\n" ++
  "goal looped = soundness(Checked, stage = written)\n"

/-- A root that applies `Round` and then a protocol of the prover alone. `Round` is then not
the last protocol before the root, and in the second application the verifier plays no role. -/
def asideSource : String :=
  round "1 / 4" ++
  "protocol Keep roles(P)(x: index<4> @P) -> y: index<4> @P:\n    return x\n" ++
  "protocol Aside roles(P, V)(claim: bool @(P, V), first: index<4> @P):\n" ++
  "    a <- Round(first)\n    k <- Keep(first)\n" ++
  "    guard @V claim or a.hit\n" ++
  "spec for Aside:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Aside:\n    prover P\n    construction interactive\n" ++
  "goal aside = soundness(Checked, stage = written)\n"

/-- A root whose callees fork. `Gate` has a guard after its draw, and `Pick` chooses by an input
and has a draw and a guard in each arm; the root applies the first and passes its result, with
the claim, to the second. The comparison of the arm of a false side is a parameter. -/
def forkedSource (second : String := "s == x") : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "def same(a: index<4>, b: index<4>) -> bool: a == b\n" ++
  "protocol Gate roles(P, V)(sent: index<4> @P) -> (hit: bool @(P, V), drawn: index<4> @(P, V)):\n" ++
  "    x <- send sent from P to V\n    r <- draw index<4> from V to P\n" ++
  "    guard @V r != 3\n" ++
  "    return (same(r, x), r)\n" ++
  "spec for Gate:\n    charge sites.r <= 1 / 4\n" ++
  "protocol Pick roles(P, V)(pass: bool @(P, V), side: bool @(P, V), sent: index<4> @P):\n" ++
  "    x <- send sent from P to V\n" ++
  "    if side:\n" ++
  "        r <- draw index<4> from V to P\n        guard @V pass or r == x\n" ++
  "    else:\n" ++
  s!"        s <- draw index<4> from V to P\n        guard @V pass or {second}\n" ++
  "spec for Pick:\n    charge sites.r <= 1 / 4\n    charge sites.s <= 1 / 4\n" ++
  "protocol Forked roles(P, V)(claim: bool @(P, V), side: bool @(P, V), first: index<4> @P, second: index<4> @P):\n" ++
  "    a <- Gate(first)\n    Pick(claim or a.hit, side, second)\n" ++
  "spec for Forked:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Forked:\n    prover P\n    construction interactive\n" ++
  "goal forked = soundness(Checked, stage = written)\n"

/-- What the check asserts of what the frontend read of a source of the subject: the goal
selects the root; it reads the clause `proves @V Holds(claim)` on the first of the three ports,
decided by the verifier of the scheme; it gives no proof argument; and its coins are positions. -/
def reading (goal : String) (ports : Array String := #["claim", "first", "second"]) : Reading where
  goals := [goal]
  ports := ports
  clause := ⟨"proves", none, "V", "Holds", ["claim"], []⟩
  operands := #[0]

/-- The draws and the applications of each use of a table: the caps of the draws with their
counts, and the uses that the applications call with their counts. -/
def shape (caps : CapTable) : List (List (Nat × Nat × Nat) × List (Nat × Nat)) :=
  caps.uses.map fun use =>
    (use.draws.map fun draw => (draw.numerator, draw.denominator, draw.count),
      use.calls.map fun call => (call.callee, call.count))

/-- Whether what a use adds up is one choice of two arms, a charged draw in each, and nothing
after it. -/
def twoArms : Tally Cap → Bool
  | .choice (.item (.draw _) .nil) (.item (.draw _) .nil) .nil => true
  | _ => false

def run : IO Unit := do
  let written ← read (source "1 / 4") (reading "twice")
  let goal ← written.goal
  -- The table of caps: the draw of `Round` in its use, and the two applications of the root,
  -- each of that use.
  unless goal.total == some (1 / 2) && goal.caps.map shape == some [([(1, 4, 1)], []), ([], [(0, 1), (0, 1)])] do
    throw (IO.userError s!"the table of caps is not the draw at 1/4 under two applications: {repr goal.caps}")
  -- The charge halved: the program is what it was, and the cap of the draw is one eighth.
  let halved ← read (source "1 / 8") (reading "twice")
  unless halved.package == written.package && (halved.goals.map (·.total)) == [some (1 / 4)] do
    throw (IO.userError "halving the charge changed the package, or the budget is not one quarter")
  -- The nested root: one application in the root, two in the protocol that it applies.
  let nested ← read nestedSource (reading "nested")
  let nestedGoal ← nested.goal
  unless nestedGoal.total == some (1 / 2) && nestedGoal.caps.map shape == some
      [([(1, 4, 1)], []), ([], [(0, 1), (0, 1)]), ([], [(1, 1)])] do
    throw (IO.userError s!"the table of the nested root is not one application of two: {repr nestedGoal.caps}")
  -- The looped root: one application in the body of a loop of three iterations.
  let looped ← read loopedSource (reading "looped" #["claim", "guess"])
  let loopedGoal ← looped.goal
  unless loopedGoal.total == some (3 / 4) && loopedGoal.caps.map shape == some [([(1, 4, 1)], []), ([], [(0, 3)])] do
    throw (IO.userError s!"the table of the looped root is not three applications: {repr loopedGoal.caps}")
  -- The root beside a protocol of the prover alone: one application of `Round`, which is the
  -- second protocol before the root, and one in which the verifier takes no part.
  let aside ← read asideSource (reading "aside" #["claim", "first"])
  let asideGoal ← aside.goal
  unless asideGoal.total == some (1 / 4) do
    throw (IO.userError s!"the table of the root beside a protocol is not one draw: {repr asideGoal.caps}")
  -- The root whose callees fork:
  -- the draw of `Gate`, the draws of both arms of `Pick`, and one application of each.
  let forked ← read (forkedSource) (reading "forked" #["claim", "side", "first", "second"])
  let forkedGoal ← forked.goal
  unless forkedGoal.total == some (1 / 2) && forkedGoal.caps.map shape == some
      [([(1, 4, 1)], []), ([(1, 4, 1), (1, 4, 1)], []), ([], [(0, 1), (1, 1)])] &&
      -- the two draws of `Pick` are the two arms of a choice, with nothing after it
      (forkedGoal.caps.map fun table => table.uses.map fun use => twoArms use.caps) == some [false, true, false] do
    throw (IO.userError s!"the table of the forked root is not three draws under two applications, with the larger arm of the choice: {repr forkedGoal.caps}")

end TwiceCharge

#eval show IO Unit from
  TwiceCharge.run
