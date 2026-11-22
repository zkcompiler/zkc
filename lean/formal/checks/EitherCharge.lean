import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Written.Package
import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SyntaxHarness
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Tests.Frontend.WrittenSubject
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
as the two arms of a choice, and its total is the larger arm, one quarter: a run pays in one
arm only. It is the fourth subject of
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
  position sent, where the walk stops at the draw, and the text asserts its statement there.
  This is the one check in which the walk restates a hypothesis while a process goes on.

The check reads the source with the frontend and writes modules on which Lean is run: the
proof module (the printed package, what `Written.Statements` writes, and the text of
`EitherCharge.lean.in` between), and the comparison module of the package with the frontend.

A second, small module is of a root with a stepped loop (`Steps`: a draw whose type depends on
the iteration, so that the loop is emitted as one block for each iteration, with a guard on
the draw in each). The walk goes into each block as it goes into an arm: the guard after the
draw of a block is where a walk that computed a block as one instruction was stuck. Its text
is in this check.

Every module that the check accepts is also read outside the file (`startModule`): its object
is replayed by the kernel and its published theorems are compared with the module that the
generator writes without the text. One control is of that reading: a text that turns the
kernel's check off and proves a false bound, on a source whose charges are too low. Lean
accepts it, with the allowed axioms for every theorem, and the reading outside refuses it at
the false equation.

One control is refused by Lean, at the place that the check names and at no other: the two
charges exchanged in the source. The program and the budget are what they were; the cap of
the draw of the second arm is one eighth, and the fee of one quarter that the text pays there
is refused with the name of that site.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open Zkc.Tests.Frontend.WrittenSubject

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
decided by the verifier of the scheme; it gives no proof argument; and its coins are positions,
so the statements are about the standard model. -/
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

/-- The text of the stepped loop: the walk goes into each block, meets its draw at no fee,
names the guard on the draw, and ends at the guard on the claim, which a false claim does not
pass. -/
def steppedText : String :=
  "noncomputable section\n\n" ++
  "theorem stepped_relation {F G : Type} (D : StandardModel.Data F G) [DecidableEq F]\n" ++
  "    [DecidableEq G] (claim : Bool) :\n" ++
  "    functionResult (t := .bool)\n" ++
  "      (fnMeaning (StandardModel.model D) installed steppedMember (.cons claim .nil)) =\n" ++
  "        some claim := by\n  kernel_rfl\n\n" ++
  "theorem stepped_judged : steppedJudged := by\n" ++
  "  claim_intro\n" ++
  "  obtain rfl : input_claim = false :=\n" ++
  "    Option.some.inj ((stepped_relation D input_claim).symm.trans rejected)\n" ++
  "  walk_free as first\n" ++
  "  walk as firstKept\n" ++
  "  -- inside a block as outside, a value of a step has a variable: the guard is stated of the draw\n" ++
  "  guard_hyp firstKept : (!first.beq 0) = true\n" ++
  "  walk_free as second\n" ++
  "  walk as secondKept\n  walk_free as third\n" ++
  "  walk as thirdKept\n\n" ++
  "theorem stepped_witnessed : steppedWitnessed :=\n" ++
  "  stepped_witnessed_of Zkc.Formal.Written.FiniteModel.data false trivial\n" ++
  "    (stepped_relation _ false)\n\nend\n"

/-- A text that turns the kernel's check off and proves the judgment from a false equation.
The option is spelled so that the generator's search for it does not find it. Lean accepts the
module and reports the allowed axioms for every theorem; the kernel, asked outside the file,
refuses the equation. -/
def uncheckedText : String :=
  "noncomputable section\n\n" ++
  "theorem either_relation {F G : Type} (D : StandardModel.Data F G) [DecidableEq F]\n" ++
  "    [DecidableEq G] (claim : Bool) :\n" ++
  "    functionResult (t := .bool)\n" ++
  "      (fnMeaning (StandardModel.model D) installed eitherMember (.cons claim .nil)) =\n" ++
  "        some claim := by\n  kernel_rfl\n\n" ++
  "set_option «debug».skipKernelTC true in\n" ++
  "theorem either_judged : eitherJudged := by\n" ++
  "  claim_intro\n" ++
  "  have h : (0 : Nat) = 1 := by decide +kernel\n" ++
  "  exact absurd h (by decide)\n\n" ++
  "theorem either_judged_forked : eitherJudged := either_judged\n\n" ++
  "theorem either_witnessed : eitherWitnessed :=\n" ++
  "  either_witnessed_of Zkc.Formal.Written.FiniteModel.data false trivial\n" ++
  "    (either_relation _ false)\n\nend\n"

/-- The theorems of the text of the proofs. -/
def ofText : List String :=
  ["either_relation", "either_judged", "either_judged_forked", "either_witnessed"]

/-- What rests on the walk of the verifier. -/
def ofWalk : List String :=
  ["either_judged", "either_judged_forked", "either_installed", "either_sound", "either_result"]

def run (template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let template ← IO.FS.readFile template
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
  -- The charges exchanged: the program and the budget (the larger arm) are what they were,
  -- and the caps are exchanged.
  let exchanged ← read (source "1 / 4" "1 / 8") reading
  unless exchanged.package == written.package && (exchanged.goals.map (·.total)) == [1 / 4] do
    throw (IO.userError "exchanging the charges changed the package or the budget")
  -- The fee of one quarter at the draw of the second arm is over its cap of one eighth: at
  -- two places and no other, one in each proof of the judgment.
  let refusal := "the fee is not within the cap that the table gives the draw `site_y`\n  1 / 4 ≤ 1 / 8"
  let exchangedControl : Control :=
    { title := "the charges exchanged", name := "CapControl", subject := exchanged,
      text := template, unproved := ofWalk, places := [refusal, refusal], only := true,
      occurrences := [(refusal, 2)] }

  -- The stepped loop: three blocks, each with its draw.
  let stepped ← read steppedSource
    { goals := ["stepped"], ports := #["claim"],
      clause := ⟨"proves", none, "V", "Holds", ["claim"], []⟩, operands := #[0] }
  unless (stepped.goals.map fun goal => goal.siteLabels.map (·.2.1)) == [["r_0", "r_1", "r_2"]] do
    throw (IO.userError "the stepped loop has not a draw in each of three blocks")
  let steppedModule ← stepped.module "Steps"
    { text := steppedText, theorems := ["stepped_relation", "stepped_judged", "stepped_witnessed"] }
  let steppedProof ← startModule work "Steps" steppedModule

  -- The kernel's check turned off by the text, on a source whose charges are too low for the
  -- protocol (one sixteenth each: the table's total is one sixteenth, the larger arm, and a
  -- false claim is accepted with probability one quarter). Lean accepts the module; outside the file the
  -- kernel refuses the false equation that the judgment was proved from.
  let low ← read (source "1 / 16" "1 / 16") reading
  unless (low.goals.map (·.total)) == [1 / 16] do
    throw (IO.userError "the low charges do not give a total of one sixteenth")
  let unchecked ← low.module "Unchecked" { text := uncheckedText, theorems := ofText }

  let _ ← check work "Either" written { text := template, theorems := ofText }
    [exchangedControl]
  let (ok, output) ← finishLean steppedProof
  acceptedOutput "Steps" ok output steppedModule.theorems allowed
  refusedOutside work "the kernel's check turned off by the text" "Unchecked" unchecked
    ["the kernel refuses a declaration of the candidate on replay", "Unchecked.either_judged"]
  IO.println ("Either is judged within the table of caps of its goal (the draws of its two arms " ++
    "at 1/8 and 1/4, of which a run takes one: 1/4), with a guard inside each arm and a guard " ++
    "before the draw; " ++
    "the blocks of a stepped loop are walked; " ++
    "1 of 1 control refused, at the place that the check names and at no other; a text that " ++
    "turns the kernel's check off is accepted by Lean and refused outside the file.")

end EitherCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work => EitherCharge.run "checks/EitherCharge.lean.in" work
