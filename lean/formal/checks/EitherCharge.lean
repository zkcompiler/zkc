import ZkcFormalTests.WrittenSubject

/-! The two arms of Either and the sites of the stepped loop. -/

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

/-- A text that turns the kernel's check off and proves the judgment from a false equation.
Lean accepts the module; the kernel of the judgment refuses the equation. -/
def uncheckedText : String :=
  "noncomputable section\n\n" ++
  "theorem either_relation {F G : Type} (D : StandardModel.Data F G) [DecidableEq F]\n" ++
  "    [DecidableEq G] (claim : Bool) :\n" ++
  "    functionResult (t := .bool)\n" ++
  "      (fnMeaning (StandardModel.model D) installed eitherMember (.cons claim .nil)) =\n" ++
  "        some claim := by\n  kernel_rfl\n\n" ++
  "set_option debug.skipKernelTC true in\n" ++
  "theorem either_judged : eitherJudged := by\n" ++
  "  claim_intro\n" ++
  "  have h : (0 : Nat) = 1 := by decide +kernel\n" ++
  "  exact absurd h (by decide)\n\n" ++
  "theorem either_judged_forked : eitherJudged := either_judged\n\n" ++
  "theorem either_witnessed : eitherWitnessed :=\n" ++
  "  either_witnessed_of false trivial\n" ++
  "    (either_relation StandardInterpretation.D false)\n\nend\n"

/-- The theorems of the text of the proofs. -/
def ofText : List String :=
  ["either_relation", "either_judged", "either_judged_forked", "either_witnessed"]

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
  -- The stepped loop: three blocks, each with its draw.
  let stepped ← read steppedSource
    { goals := ["stepped"], ports := #["claim"],
      clause := ⟨"proves", none, "V", "Holds", ["claim"], []⟩, operands := #[0] }
  unless (stepped.goals.map fun goal => goal.siteLabels.map (·.2.1)) == [["r_0", "r_1", "r_2"]] do
    throw (IO.userError "the stepped loop has not a draw in each of three blocks")
  -- The kernel's check turned off by the text, on a source whose charges are too low for the
  -- protocol (one sixteenth each: the table's total is one sixteenth, the larger arm, and a
  -- false claim is accepted with probability one quarter). Lean accepts the module; in the
  -- judgment the kernel refuses the false equation that the judgment of the process was proved from.
  let low ← read (source "1 / 16" "1 / 16") reading
  unless (low.goals.map (·.total)) == [1 / 16] do
    throw (IO.userError "the low charges do not give a total of one sixteenth")
  let unchecked ← low.module "Unchecked" { text := uncheckedText, theorems := ofText }
  let m ← written.module "Either" { text := template, theorems := [] }
  let lemmas ← startLemmas work "Either" m template ["either_relation", "either_witnessed"] written
  let stepText := template.replace "either" "stepped"
  let steps ← stepped.module "Steps" { text := stepText, theorems := [] }
  let stepCheck ← startLemmas work "Steps" steps stepText ["stepped_relation", "stepped_witnessed"]
  let uncheckedRefused ← refusedOutside work "the kernel's check turned off by the text" "Unchecked" unchecked
    -- the checker ended with 1, as on a declaration that it refuses, and was not killed
    ["Lean default kernel rejected the solution", "Lean default exited with 1"]
  lemmas
  stepCheck
  uncheckedRefused

end EitherCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work => EitherCharge.run "checks/EitherCharge.lean.in" work
