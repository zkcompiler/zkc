import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Written.Package
import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SyntaxHarness
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Core.Admission.Theorems
import Zkc.Kernel
import Zkc.Vocabulary.Project

/-!
A protocol with a charged draw and a guard in each arm of a choice, judged within the charges
that its source declares.

The subject is `Either`: by the claim the verifier takes one of two arms. In each it gets a
position from the prover, draws one, and rejects unless the draw is the position that it got;
in the second it first rejects the last position. Its contract charges the draw of the first
arm one eighth and the draw of the second one quarter. The table of caps has both draws once,
and its total is three eighths, though a run pays in one arm only. It is the fourth subject of
a written soundness goal, and differs from the others in the shape of its program:

- **a choice.** The walk goes into the arm that the condition chooses, and inside it every
  rule is as outside: the values of the arm have variables, its effects are met, and at its
  end the goal is the judgment of what follows the choice. The text proves the judgment twice:
  with the claim decided beforehand, where the kernel computes the condition, and with the
  choice left open, where the walk forks on the claim and the text names the fork;
- **a guard inside an arm, after an effect of that arm**, on which the walk was stuck before
  it went into the arms of a choice;
- **a guard on a computed value before an effect.** The text names the guard (`walk as`), and
  the process goes on to the draw: the hypothesis that the guard passed is restated of the
  position sent, where the walk stops at the draw, and the text uses it there. This is the
  one check in which the walk restates a hypothesis while a process goes on.

The check reads the source with the frontend and writes modules on which Lean is run: the
proof module (the printed package, what `Written.Statements` writes, and the text of
`EitherCharge.lean.in` between), and the comparison module of the package with the frontend.

One control is refused by Lean, at the place that the check names and at no other: the two
charges exchanged in the source. The program and the budget are what they were; the cap of
the draw of the second arm is one eighth, and the fee of one quarter that the text pays there
is refused with the name of that site.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

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

structure Subject where
  text : String
  statements : Statements

def Subject.package (s : Subject) : String := (Written.package s.statements.package).text

def noAssociation : Association := ⟨[], [], [], [], []⟩

/-- A source read: the goal selects the root, reads the clause `proves @V Holds(claim)` on the
first of the three ports, decided by the verifier of the scheme, and gives no proof argument. -/
def read (text : String) : IO Subject := do
  let c ← IO.ofExcept (goalRoot text "either")
  let head ← IO.ofExcept (SourceClause.rootHead c)
  unless head.ports.map (·.binder.name) == #["claim", "first", "second"] do
    throw (IO.userError "the protocol has other ports than the claim and the two positions")
  let claims ← IO.ofExcept (goalClaims c ["either"])
  let [claimed] := claims.goals | throw (IO.userError "the claims are not of one goal")
  let clause ← IO.ofExcept (SourceClause.seen c "either")
  unless clause == ⟨"proves", none, "V", "Holds", ["claim"], []⟩ do
    throw (IO.userError s!"the goal reads another clause: {repr clause}")
  unless claimed.statement == #[0] && claimed.witness == some #[] && claimed.specification.isEmpty do
    throw (IO.userError "the relation is applied to other inputs than the claim")
  unless (head.roster[claims.verifier]?, head.roster[claims.prover]?) == (some "V", some "P") do
    throw (IO.userError "the verifier and the prover of the scheme are not the roles V and P")
  return ⟨text, ⟨claims, claims.functionsBeforeRoot⟩⟩

/-- The theorems of the text of the proofs. -/
def ofText : List String :=
  ["either_relation", "either_judged", "either_judged_forked", "either_witnessed"]

/-- What rests on the walk of the verifier. -/
def ofWalk : List String :=
  ["either_judged", "either_judged_forked", "either_installed", "either_sound", "either_result"]

/-- The proof module, as the generator assembles it. -/
def proofModule (name : String) (s : Subject) (template : String) : IO Module :=
  IO.ofExcept (s.statements.module standardModelText name { text := template, theorems := ofText })

def run (template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let template ← IO.FS.readFile template
  let written ← read (source "1 / 8" "1 / 4")
  let [goal] := written.statements.claims.goals
    | throw (IO.userError "the statements are not of one goal")
  -- The table of caps: the draws of the two arms, once each, and the two arms added.
  unless goal.total == 3 / 8 && (goal.caps.uses.map fun use => use.draws.map fun draw =>
      (draw.numerator, draw.denominator, draw.count)) == [[(1, 8, 1), (1, 4, 1)]] do
    throw (IO.userError s!"the table of caps is not the two draws at 1/8 and 1/4: {repr goal.caps}")
  unless goal.siteLabels.map (·.2.1) == ["x", "y"] do
    throw (IO.userError s!"the draws are not named `x` and `y`: {goal.siteLabels.map (·.2.1)}")
  -- The charges exchanged: the program and the budget are what they were, and the caps are
  -- exchanged.
  let exchanged ← read (source "1 / 4" "1 / 8")
  unless exchanged.package == written.package &&
      (exchanged.statements.claims.goals.map (·.total)) == [3 / 8] do
    throw (IO.userError "exchanging the charges changed the package or the budget")

  let module ← proofModule "Either" written template
  let theorems := module.theorems
  let proof ← startLakeLean work "Either" module.text
  let comparison ← startLakeLean work "EitherSource"
    (comparisonModule "EitherSource" written.text ["either"] written.package)
  let exchangedProof ← startLakeLean work "CapControl"
    (← proofModule "CapControl" exchanged template).text

  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  let (ok, output) ← finishLean proof
  acceptedOutput "Either" ok output theorems allowed
  let (ok, output) ← finishLean comparison
  acceptedOutput "EitherSource" ok output []
  -- The fee of one quarter at the draw of the second arm is over its cap of one eighth.
  expectUnproved "the charges exchanged" "CapControl" theorems exchangedProof ofWalk
  expectPlaces "the charges exchanged" exchangedProof
    ["the fee is not within the cap that the table gives the draw `site_y`\n  1 / 4 ≤ 1 / 8",
      "the fee is not within the cap that the table gives the draw `site_y`\n  1 / 4 ≤ 1 / 8"]
  IO.println ("Either is judged within the table of caps of its goal (the draws of its two arms " ++
    "at 1/8 and 1/4: 3/8), with a guard inside each arm and a guard before the draw; " ++
    "1 of 1 control refused, at the place that the check names and at no other.")

end EitherCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work => EitherCharge.run "checks/EitherCharge.lean.in" work
