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

/-!
A protocol of three rounds, judged within the charges that its source declares.

The subject is `Guess<3>`: in each of three rounds the verifier gets a position from the prover
and draws one, and it rejects unless the claim holds or some round drew the position that it
got. Its contract charges the draw one eighth, and its goal is soundness of the claim. It is the
third subject of a written soundness goal, and the first whose charge is paid more than once: a
draw inside a kept loop, with a fee at every round. Its table of caps has the draw once, with
the count three, and its total is three eighths.

The check reads the source with the frontend and writes modules on which Lean is run.

- The proof module has the printed package of what the goal claims and, around the text of
  `GuessCharge.lean.in`, what `Written.Statements` writes. Among it is the judgment that the
  method of fees has to establish (`guessingJudged`), with the theorem that the claim follows
  from it; the text proves that judgment and the witness, and states neither the claim nor
  where the walk starts. It walks the verifier's loop by an invariant (no round has hit yet;
  `(3 - i) / 8` of the budget is left), meets the message for free (`walk_free`) and pays one
  eighth at the draw (`walk_pay`), which is compared with the cap that the generated theorem
  `guessing_cap_r` states for the site `site_r`; the text names neither. After the generated theorems stands a consumer that names no
  generated proposition, writes the verifier as its place in the roster and the bound as the
  number `3 / 8`, and proves it from the published theorem.
- The comparison module has the same printed package and the frontend.

What the source says and the proof module takes as given is asserted here against the source:
the ports, the clause, the operand and the table of caps, as literals.

Four controls are refused: three by Lean, each at the places that the check names and at no
other, and one by the judgment.

- A text that proves nothing of the judgment: after its last `end` it declares the judgment as
  an instance variable of the module's scope, with the two linters that would report that
  switched off, and takes the judgment from the variable. Every theorem that the generator
  writes after the text takes the variable as a hypothesis; Lean proves each and accepts the
  module. The judgment (`lake comparator`) refuses it: the statement of a published theorem is
  not the challenge's.

- The charge of the source halved (`1 / 16`): the program is what it was, the cap of the draw
  is another and so is the budget, three sixteenths. The module is refused at three places:
  where the invariant starts with three fees of one eighth within the budget, where the text
  pays one eighth at the draw and the generated cap of the draw is one sixteenth, and where
  the consumer states the bound as `3 / 8`. A source cannot lower the cap of this draw and keep the budget, since the draw is
  the only charged one, so no control of this subject separates the cap from the budget; the
  text of `Count<8>` proves that separation (`misplaced_judges_nothing`: a table with the same
  budget whose cap is on another instruction judges the verifier at no budget).
- Four rounds for three (`Guess<4>`): the count of the draw and the budget are other numbers
  (four, and one half). The module is refused at two places: in the goal of the loop's body,
  where the invariant of the text has paid three rounds and has nothing for the fourth, and
  where the consumer states the bound as `3 / 8`.
- An invariant that leaves one fee too few (`(2 - i) / 8` for `(3 - i) / 8`), which is the
  negative test of the walk's loop rule: the rule is applied and its first goal is met, and the
  text is refused at one place, in the goal of the body, where the fee of the third round is
  not within what the invariant leaves.
-/

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

/-- The theorems of the text of the proofs. -/
def ofText : List String :=
  ["guessing_relation", "guessing_judged", "guessing_witnessed"]

/-- What rests on the walk of the verifier. -/
def ofWalk : List String :=
  ["guessing_judged", "guessing_installed", "guessing_sound", "guessing_result", "consumer"]

/-- A reader's statement of the goal, with no generated proposition, the verifier as its place
in the roster and the bound as a number: in every admitted program with the protocol and the
relation found by their keys, where the relation returns false of the false claim, the second
role on that claim returns with probability at most three eighths under the service of the
laws. Its proof is the published theorem and the budget that the module states. -/
def consumer : String :=
  "noncomputable section\n" ++
  "open ZkcFormal.Written.StandardModel\n" ++
  "open ZkcFormal.Written.FiniteModel (data)\n\n" ++
  "theorem consumer {a : Admitted V} (admitted : admit stored association = .ok a) :\n" ++
  "    ∃ root : Member a.program.headers.protocols rootHeader,\n" ++
  "      a.program.findProtocol rootKey = some ⟨rootHeader, root⟩ ∧\n" ++
  "      ∃ relation : Member a.program.headers.fns guessingHeader,\n" ++
  "        a.program.find guessingKey = some (.fn relation) ∧\n" ++
  "        (functionResult (t := .bool)\n" ++
  "            (fnMeaning (StandardModel.model data) a.program relation (.cons false .nil)) = some false →\n" ++
  "          Pr{let out ← (simulateQ (handlerOf (serveLaws (StandardModel.model data) (draws data))) (embed\n" ++
  "              (roleMeaning (StandardModel.model data) a.program root 1 []\n" ++
  "                (.cons false (.cons () .nil))))).run.run ()}[\n" ++
  "            ∃ results, out.1 = some (.inl results)] ≤ 3 / 8) := by\n" ++
  "  have total : guessingCaps.total = 3 / 8 := by\n" ++
  "    rw [CapTable.total, guessing_budget, toProbability_natCast_div 3 8 (by decide)]\n" ++
  "    norm_num\n" ++
  "  obtain ⟨root, found, relation, foundRelation, claim⟩ := guessing_sound admitted\n" ++
  "  refine ⟨root, found, relation, foundRelation, fun rejected => ?_⟩\n" ++
  "  rw [← total]\n" ++
  "  simpa using claim data [] false trivial rejected _ (serveLaws (StandardModel.model data) (draws data))\n" ++
  "    ⟨serveLaws_follows _ _, serveLaws_permitted _ _ (StandardModel.draws_permitted data)⟩ ()\n\n" ++
  "end\n"

def run (template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let template ← IO.FS.readFile template
  let proof : Proof :=
    { text := template, theorems := ofText, after := { text := consumer, theorems := ["consumer"] } }
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
  -- An invariant that leaves one fee too few.
  let short ← replaceOnce template "((3 - i : ℕ) : ℚ≥0) * (1 / 8) ≤ budget"
    "((2 - i : ℕ) : ℚ≥0) * (1 / 8) ≤ budget"
  let short ← replaceOnce short "have split : (3 - i : ℕ) = (3 - (i + 1)) + 1 := by omega"
    "have split : (2 - i : ℕ) = (2 - (i + 1)) + 1 := by omega"
  -- A text that proves nothing of the judgment: after its last `end` it declares the judgment
  -- as an instance variable of the module's scope, with the two linters that would report that
  -- switched off, and takes the judgment from the variable.
  let assumed := (← replaceOnce template "theorem guessing_judged : guessingJudged := by"
      "theorem guessing_established : guessingJudged := by") ++
    "\nset_option linter.unusedSectionVars false\nset_option linter.concreteInstances false\n" ++
    "variable [assumed : Fact guessingJudged]\n" ++
    "theorem guessing_judged : guessingJudged := assumed.out\n"

  let _ ← check work "Guess" written proof [
    -- The cap of the draw is one sixteenth: the invariant does not start within the budget of
    -- three sixteenths, the fee of one eighth that the text pays is not within the cap that
    -- the module states for the draw, which the refusal names as the source does, and the
    -- consumer's number is not the budget.
    { title := "the charge halved", name := "CapControl", subject := halved, text := template,
      unproved := ofWalk, only := true,
      places := ["↑(3 - 0) * (1 / 8) ≤ guessingCaps.budget",
        "the fee is not within the cap that the table gives the draw `site_r`\n  1 / 8 ≤ 1 / 16",
        "toProbability (↑3 / ↑16) = 3 / 8"] },
    -- Four rounds: the invariant of the text pays three, and the body at the fourth round has
    -- nothing left to pay with; the consumer's number is not the budget of one half.
    { title := "four rounds", name := "RoundsControl", subject := four, text := template,
      unproved := ofWalk, only := true,
      places := ["omega could not prove the goal", "toProbability (↑1 / ↑2) = 3 / 8"] },
    -- An invariant that leaves one fee too few: the loop rule is applied and its first goal
    -- is met; in the goal of the body the fee of the third round is not within what is left.
    { title := "an invariant one fee short", name := "InvariantControl", subject := written,
      text := short, unproved := ofWalk, only := true,
      places := ["omega could not prove the goal"] },
    -- The judgment taken as a hypothesis: every theorem that the generator writes after the
    -- text takes the variable, so Lean proves each and accepts the module; none is of its
    -- proposition, and the judgment refuses the module: the statement of a published theorem
    -- is not the challenge's.
    { title := "a judgment taken as a hypothesis", name := "AssumedControl", subject := written,
      text := assumed, refusal := .outside,
      -- the comparator stops at the first published theorem whose statement is another
      places := ["Challenge and solution theorem statement do not match: 'Guess.guessing_installed'"] }]
  IO.println ("Guess<3> is judged within the table of caps of its goal (the draw at 1/8, three " ++
    "times: 3/8), a fee at every round of the loop; a consumer written apart states the bound " ++
    "as 3/8; 4 of 4 controls refused, three by Lean at the places that the check names and at " ++
    "no other, and one by the judgment, where a published theorem has not the statement of its " ++
    "challenge.")

end GuessCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work => GuessCharge.run "checks/GuessCharge.lean.in" work
