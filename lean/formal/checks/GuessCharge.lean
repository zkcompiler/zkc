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
A protocol of three rounds, judged within the charges that its source declares.

The subject is `Guess<3>`: in each of three rounds the verifier gets a position from the prover
and draws one, and it rejects unless the claim holds or some round drew the position that it
got. Its contract charges the draw one eighth, and its goal is soundness of the claim. It is the
third subject of a written soundness goal, and the first whose charge is paid more than once: a
draw inside a kept loop, with a fee at every round. Its table of caps has the draw once, with
the count three, and its total is three eighths.

The check reads the source with the frontend and writes modules on which Lean is run.

- The proof module has the printed package of what the goal claims and, around the text of
  `GuessCharge.lean.in`, what `Written.Statements` writes. The text walks the verifier's loop by
  an invariant (no round has hit yet; `(3 - i) / 8` of the budget is left), meets the message
  for free and pays at the draw with its occurrence read from the effect and its cap read from
  the table by the kernel. After the generated theorems stands a consumer that names no
  generated proposition, writes the verifier as its place in the roster and the bound as the
  number `3 / 8`, and proves it from the published theorem.
- The comparison module has the same printed package and the frontend.

What the source says and the proof module takes as given is asserted here against the source:
the ports, the clause, the operand and the table of caps, as literals.

Three controls are refused by Lean, each at the places that the check names and at no other.

- The charge of the source halved (`1 / 16`): the program is what it was, the cap of the draw
  is another and so is the budget, three sixteenths. The module is refused at three places:
  where the text reads the cap of the draw from the table, where the invariant starts with
  three fees of one eighth within the budget, and where the consumer states the bound as
  `3 / 8`. A source cannot lower the cap of this draw and keep the budget, since the draw is
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

structure Subject where
  text : String
  statements : Statements

def Subject.package (s : Subject) : String := (Written.package s.statements.package).text

def noAssociation : Association := ⟨[], [], [], [], []⟩

/-- A source read: the goal selects the root, reads the clause `proves @V Holds(claim)` on the
first of the two ports, decided by the verifier of the scheme, and gives no proof argument. -/
def read (text : String) : IO Subject := do
  let c ← IO.ofExcept (goalRoot text "guessing")
  let head ← IO.ofExcept (SourceClause.rootHead c)
  unless head.ports.map (·.binder.name) == #["claim", "guess"] do
    throw (IO.userError "the protocol has other ports than the claim and the guess")
  let claims ← IO.ofExcept (goalClaims c ["guessing"])
  let [claimed] := claims.goals | throw (IO.userError "the claims are not of one goal")
  let clause ← IO.ofExcept (SourceClause.seen c "guessing")
  unless clause == ⟨"proves", none, "V", "Holds", ["claim"], []⟩ do
    throw (IO.userError s!"the goal reads another clause: {repr clause}")
  unless claimed.statement == #[0] && claimed.witness == some #[] && claimed.specification.isEmpty do
    throw (IO.userError "the relation is applied to other inputs than the claim")
  unless (head.roster[claims.verifier]?, head.roster[claims.prover]?) == (some "V", some "P") do
    throw (IO.userError "the verifier and the prover of the scheme are not the roles V and P")
  return ⟨text, ⟨claims, claims.functionsBeforeRoot⟩⟩

/-- The theorems of the text of the proofs. -/
def ofText : List String :=
  ["guessing_relation", "cap_of_draw", "walked_within", "guessing_installed", "guessing_witnessed"]

/-- What rests on the walk of the verifier. -/
def ofWalk : List String :=
  ["walked_within", "guessing_installed", "guessing_sound", "guessing_result", "consumer"]

/-- A reader's statement of the goal, with no generated proposition, the verifier as its place
in the roster and the bound as a number: in every admitted program with the protocol and the
relation found by their keys, where the relation returns false of the false claim, the second
role on that claim returns with probability at most three eighths under the service of the
laws. Its proof is the published theorem and the budget that the module states. -/
def consumer : String :=
  "noncomputable section\n" ++
  "open Zkc.Formal.Written.StandardModel\n" ++
  "open Zkc.Formal.Written.FiniteModel (data)\n\n" ++
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

/-- The proof module, as the generator assembles it: the package of the claims and what is
generated around the proofs written for the protocol, then the consumer. -/
def proofModule (name : String) (s : Subject) (template : String) : IO Module :=
  IO.ofExcept (s.statements.module standardModelText name { text := template, theorems := ofText, method := .direct }
    (after := { text := consumer, theorems := ["consumer"] }))

/-- A control is refused at the places that are named and at no other: Lean's output has as many
errors as there are places, and the text of each. -/
def expectPlaces (title : String) (task : Task (Except IO.Error (Bool × String)))
    (places : List String) : IO Unit := do
  let (_, output) ← finishLean task
  let errors := (output.splitOn "error:").length - 1
  unless errors == places.length do
    throw (IO.userError s!"{title}: refused at {errors} places, not at {places.length}\n{output}")
  for place in places do
    unless output.contains place do
      throw (IO.userError s!"{title}: not refused at `{place}`\n{output}")

def run (template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let template ← IO.FS.readFile template
  let written ← read (source "3" "1 / 8")
  let stated := written.statements
  let [goal] := stated.claims.goals | throw (IO.userError "the statements are not of one goal")
  unless stated.claims.root == 0 && (stated.claims.verifier, stated.claims.prover) == (1, 0) do
    throw (IO.userError "the root and the roles of the source are not where they were")
  -- The table of caps, as the frontend read it: the draw of the loop's body, at one eighth,
  -- three times.
  unless goal.caps == ⟨[⟨⟨0⟩, [⟨⟨3⟩, 1, 8, 3⟩], []⟩]⟩ && goal.total == 3 / 8 do
    throw (IO.userError s!"the table of caps is not the draw at 1/8, three times: {repr goal.caps}")

  -- The charge halved in the source: the program is what it was, and the cap is another.
  let halved ← read (source "3" "1 / 16")
  unless halved.package == written.package &&
      (halved.statements.claims.goals.map (·.caps)) == [⟨[⟨⟨0⟩, [⟨⟨3⟩, 1, 16, 3⟩], []⟩]⟩] do
    throw (IO.userError "the halved charge changed the package, or is not half at the draw")
  -- Four rounds: the count of the draw is four.
  let four ← read (source "4" "1 / 8")
  unless (four.statements.claims.goals.map fun goal => (goal.caps, goal.total)) ==
      [(⟨[⟨⟨0⟩, [⟨⟨3⟩, 1, 8, 4⟩], []⟩]⟩, 1 / 2)] do
    throw (IO.userError "with four rounds the draw is not counted four times")
  -- An invariant that leaves one fee too few.
  let short := template.replace "((3 - i : ℕ) : ℚ≥0) * (1 / 8) ≤ budget" "((2 - i : ℕ) : ℚ≥0) * (1 / 8) ≤ budget"
    |>.replace "have split : (3 - i9 : ℕ) = (3 - (i9 + 1)) + 1 := by omega"
      "have split : (2 - i9 : ℕ) = (2 - (i9 + 1)) + 1 := by omega"
  if short == template then throw (IO.userError "the text has not the invariant that the control alters")

  let module ← proofModule "Guess" written template
  let theorems := module.theorems
  let proof ← startLakeLean work "Guess" module.text
  let comparison ← startLakeLean work "GuessSource" (comparisonModule "GuessSource" written.text ["guessing"] written.package)
  let halvedProof ← startLakeLean work "CapControl" (← proofModule "CapControl" halved template).text
  let fourProof ← startLakeLean work "RoundsControl" (← proofModule "RoundsControl" four template).text
  let shortProof ← startLakeLean work "InvariantControl"
    (← proofModule "InvariantControl" written short).text

  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  let (ok, output) ← finishLean proof
  acceptedOutput "Guess" ok output theorems allowed
  let (ok, output) ← finishLean comparison
  acceptedOutput "GuessSource" ok output []
  -- The cap of the draw is one sixteenth: the text reads another cap from the table than the
  -- one that it pays, the invariant does not start within the budget of three sixteenths, and
  -- the consumer's number is not the budget.
  expectUnproved "the charge halved" "CapControl" theorems halvedProof ("cap_of_draw" :: ofWalk)
  expectPlaces "the charge halved" halvedProof
    ["guessingCaps.capFrom guessingCaps.root [] { number := 3 } = 1 / 8",
      "↑(3 - 0) * (1 / 8) ≤ guessingCaps.budget", "toProbability (↑3 / ↑16) = 3 / 8"]
  -- Four rounds: the invariant of the text pays three, and the body at the fourth round has
  -- nothing left to pay with; the consumer's number is not the budget of one half.
  expectUnproved "four rounds" "RoundsControl" theorems fourProof ofWalk
  expectPlaces "four rounds" fourProof
    ["omega could not prove the goal", "toProbability (↑1 / ↑2) = 3 / 8"]
  -- An invariant that leaves one fee too few: the loop rule is applied and its first goal is
  -- met; in the goal of the body the fee of the third round is not within what is left.
  expectUnproved "an invariant one fee short" "InvariantControl" theorems shortProof ofWalk
  expectPlaces "an invariant one fee short" shortProof ["omega could not prove the goal"]
  IO.println ("Guess<3> is judged within the table of caps of its goal (the draw at 1/8, three " ++
    "times: 3/8), a fee at every round of the loop; a consumer written apart states the bound " ++
    "as 3/8; 3 of 3 controls refused, each at the places that the check names and at no other.")

end GuessCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work => GuessCharge.run "checks/GuessCharge.lean.in" work
