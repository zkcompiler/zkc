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
A root that applies a protocol twice, judged within the charges that the protocol's contract
declares.

The subject is `Twice`: the root applies `Round` to each of two positions that the prover
holds and returns where the claim holds or one of the rounds hit. In `Round` the verifier gets
the position, draws a position of four, and returns whether the two are the same, computed by
the function `same`, with the draw. The contract of `Round` charges its draw one quarter. The
table of caps has the draw once, in the use of `Round`, and the two applications in the use of
the root; its total is one half. It is the fifth subject of a written soundness goal, and
differs from the others in the shape of its program:

- **an application.** The walk goes into the protocol that the root applies, as it goes into
  the arm of a choice: the effects of the callee are met at the path of the application, its
  values have variables, and at its end the goal is the judgment of what follows in the root,
  on the results that the application carried back. The text of the root is the text of the
  callee's body, twice;
- **a draw that is charged in the callee's contract**, whose cap the table gives the root
  through the application, at each of the two applications;
- **a function called inside the callee**, which reads the table of the definitions before the
  callee. The text states the law of the function once, in the table of the definitions
  before the root, and the walk takes the call by it;
- **a walk of a hypothesis through the application** (`twice_pays_first`, written by the check
  after the text): for every judgment with fees that reads no peer of an effect.

The check reads the source with the frontend and writes modules on which Lean is run: the
proof module (the printed package, what `Written.Statements` writes, and the text of
`TwiceCharge.lean.in` between), and the comparison module of the package with the frontend.

A second module is of a root that applies a protocol that applies `Round` twice, with its own
roles in the other order (`Nested`): the walk goes through both applications, and the role
that it follows is the first of the root and the second of the two protocols below it. Its
text is the text of `Twice` with the names of the goal.

A third module is of a root that applies `Round` in the body of a loop of three iterations
(`Looped`). The loop is taken by an invariant, as the loop of `Guess` is; in its body the walk
goes into the application at the path of the iteration, and the fee of the callee's draw is
within the cap that the table gives it under that iteration.

One control is refused by Lean, at the place that the check names and at no other: the charge
of the draw halved in the source. The program is what it was; the cap that the table gives the
draw through the application is one eighth, and the fee of one quarter that the text pays at
the first application is refused there, with the name that the module gives that draw below
that application.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open Zkc.Tests.Frontend.WrittenSubject

namespace TwiceCharge

/-- The function and the protocol that the roots apply, with the charge of its draw. -/
def round (charge : String) : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "def same(a: index<4>, b: index<4>) -> bool: a == b\n" ++
  "protocol Round roles(P, V)(sent: index<4> @P) -> (hit: bool @(P, V), drawn: index<4> @(P, V)):\n" ++
  "    x <- send sent from P to V\n    r <- draw index<4> from V to P\n" ++
  "    return (same(r, x), r)\n" ++
  s!"spec for Round:\n    charge sites.r <= {charge}\n"

/-- The source: the root applies `Round` twice. -/
def source (charge : String) : String :=
  round charge ++
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

/-- The text of the looped root: the loop is taken by an invariant, as the loop of `Guess` is,
and in its body the walk goes into the application, pays at the callee's draw under the frame
of the iteration, and takes the call of `same` by the law stated before the root. -/
def loopedText : String :=
  "noncomputable section\n\n" ++
  "theorem looped_relation {F G : Type} (D : StandardModel.Data F G) [DecidableEq F]\n" ++
  "    [DecidableEq G] (claim : Bool) :\n" ++
  "    functionResult (t := .bool)\n" ++
  "      (fnMeaning (StandardModel.model D) installed loopedMember (.cons claim .nil)) =\n" ++
  "        some claim := by\n  kernel_rfl\n\n" ++
  "theorem same_law {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]\n" ++
  "    (a b : ℕ) :\n" ++
  "    fnMeaning (StandardModel.model D) calleeProgram sameMember (.cons a (.cons b .nil)) =\n" ++
  "      .done (.cons (a.beq b) .nil) := by\n" ++
  "  refine done_of_judged ?_\n  repeat walk_step\n  subst_vars\n  rfl\n\n" ++
  "theorem looped_judged : loopedJudged := by\n" ++
  "  claim_intro\n" ++
  "  obtain rfl : input_claim = false :=\n" ++
  "    Option.some.inj ((looped_relation D input_claim).symm.trans rejected)\n" ++
  "  walk\n" ++
  "  walk_loop fun i (hit : Bool) budget => hit = false ∧ ((3 - i : ℕ) : ℚ≥0) * (1 / 4) ≤ budget\n" ++
  "  case first => exact ⟨rfl, by decide +kernel⟩\n" ++
  "  case step =>\n" ++
  "    obtain ⟨rfl, enough⟩ := invariant_i\n" ++
  "    have split : (3 - i : ℕ) = (3 - (i + 1)) + 1 := by omega\n" ++
  "    rw [split, Nat.cast_add, Nat.cast_one, add_mul, one_mul] at enough\n" ++
  "    -- the application in the body: the message and the draw of `Round`\n" ++
  "    walk_free as sent\n" ++
  "    walk_pay (1 / 4) excluding (fun drawn : ℕ => drawn = sent) as drawn differs\n" ++
  "    case weight => simpa using prEvent_drawPosition_eq_le 3 sent\n" ++
  "    case within => exact le_trans le_add_self enough\n" ++
  "    walk\n    walk_law same_law D drawn sent\n    walk\n" ++
  "    refine ⟨?_, le_tsub_of_add_le_right enough⟩\n" ++
  "    exact Bool.eq_false_iff.mpr fun same => differs (Nat.eq_of_beq_eq_true same)\n" ++
  "  case after =>\n    obtain ⟨rfl, _⟩ := invariant_i\n    walk\n\n" ++
  "theorem looped_witnessed : loopedWitnessed :=\n" ++
  "  looped_witnessed_of Zkc.Formal.Written.FiniteModel.data false trivial\n" ++
  "    (looped_relation _ false)\n\nend\n"

/-- A theorem after the text of `Twice` that walks a hypothesis: a judgment of the verifier is
given, and the walk goes through the first application on it. The judgment is any judgment with
fees that reads no peer of an effect, which the theorem states as a hypothesis; the walk takes
the proof from there. The path of the application is the root's, so the theorem is of `Twice`
and not of the nested root. -/
def converseText : String :=
  "\n" ++
  "/-- **A walk of a hypothesis goes through an application.** Every judgment with fees that reads\n" ++
  "no peer of an effect and judges the verifier, on a false claim, never to return pays at the\n" ++
  "first effect of the run, which is the message of `Round` at the path of the first\n" ++
  "application. -/\n" ++
  "theorem twice_pays_first {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]\n" ++
  "    (allowed : ∀ op, (RSig (StandardModel.model D)).Reply op → Prop)\n" ++
  "    (pays : (op : ROp (StandardModel.model D)) → ℚ≥0 →\n" ++
  "      ((RSig (StandardModel.model D)).Reply op → Prop) → Prop)\n" ++
  "    (blind : ∀ ρ : Role → Role, Blind ρ (ProcessJudgment.charged allowed pays))\n" ++
  "    (path : List Frame) (within : ℚ≥0)\n" ++
  "    (judged : (roleMeaning (StandardModel.model D) installed rootMember verifierRole path\n" ++
  "        (.cons false (.cons () (.cons () .nil)))).interpret (.charged allowed pays)\n" ++
  "      (fun _ _ => False) (fun _ _ => True) within) :\n" ++
  "    ∃ fee excluded, fee ≤ within ∧\n" ++
  "      pays (.get .message 0 ⟨path ++ [.application ⟨0⟩], ⟨0⟩⟩ (.fin 4)) fee excluded := by\n" ++
  "  walk at judged\n" ++
  "  obtain ⟨fee, excluded, least, paid, _⟩ := judged\n" ++
  "  exact ⟨fee, excluded, least, paid⟩\n"

/-- What the check asserts of what the frontend read of a source of the subject: the goal
selects the root; it reads the clause `proves @V Holds(claim)` on the first of the three ports,
decided by the verifier of the scheme; it gives no proof argument; and its coins are positions,
so the statements are about the standard model. -/
def reading (goal : String) (ports : Array String := #["claim", "first", "second"]) : Reading where
  goals := [goal]
  ports := ports
  clause := ⟨"proves", none, "V", "Holds", ["claim"], []⟩
  operands := #[0]

/-- The theorems of the text of the proofs of a goal. -/
def ofText (goal : String) : List String :=
  [s!"{goal}_relation", "same_law", s!"{goal}_judged", s!"{goal}_witnessed"]

/-- What rests on the walk of the verifier. -/
def ofWalk : List String :=
  ["twice_judged", "twice_installed", "twice_sound", "twice_result"]

/-- The draws and the applications of each use of a table: the caps of the draws with their
counts, and the uses that the applications call with their counts. -/
def shape (caps : CapTable) : List (List (Nat × Nat × Nat) × List (Nat × Nat)) :=
  caps.uses.map fun use =>
    (use.draws.map fun draw => (draw.numerator, draw.denominator, draw.count),
      use.calls.map fun call => (call.callee, call.count))

def run (template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let template ← IO.FS.readFile template
  let written ← read (source "1 / 4") (reading "twice")
  let goal ← written.goal
  -- The table of caps: the draw of `Round` in its use, and the two applications of the root,
  -- each of that use.
  unless goal.total == 1 / 2 && shape goal.caps == [([(1, 4, 1)], []), ([], [(0, 1), (0, 1)])] do
    throw (IO.userError s!"the table of caps is not the draw at 1/4 under two applications: {repr goal.caps}")
  -- The charge halved: the program is what it was, and the cap of the draw is one eighth.
  let halved ← read (source "1 / 8") (reading "twice")
  unless halved.package == written.package && (halved.goals.map (·.total)) == [1 / 4] do
    throw (IO.userError "halving the charge changed the package, or the budget is not one quarter")
  -- The fee of one quarter at the draw of the first application is over its cap of one eighth:
  -- at that place and no other.
  let refusal := "the fee is not within the cap that the table gives the draw `site_at_0_1`\n  1 / 4 ≤ 1 / 8"
  let halvedControl : Control :=
    { title := "the charge of the callee halved", name := "CapControl", subject := halved,
      text := template ++ converseText, unproved := ofWalk, places := [refusal], only := true,
      occurrences := [(refusal, 1)] }

  -- The nested root: one application in the root, two in the protocol that it applies.
  let nested ← read nestedSource (reading "nested")
  let nestedGoal ← nested.goal
  unless nestedGoal.total == 1 / 2 && shape nestedGoal.caps ==
      [([(1, 4, 1)], []), ([], [(0, 1), (0, 1)]), ([], [(1, 1)])] do
    throw (IO.userError s!"the table of the nested root is not one application of two: {repr nestedGoal.caps}")
  let nestedModule ← nested.module "Nested"
    { text := template.replace "twice" "nested", theorems := ofText "nested" }
  let nestedProof ← startLakeLean work "Nested" nestedModule.text

  -- The looped root: one application in the body of a loop of three iterations.
  let looped ← read loopedSource (reading "looped" #["claim", "guess"])
  let loopedGoal ← looped.goal
  unless loopedGoal.total == 3 / 4 && shape loopedGoal.caps == [([(1, 4, 1)], []), ([], [(0, 3)])] do
    throw (IO.userError s!"the table of the looped root is not three applications: {repr loopedGoal.caps}")
  let loopedModule ← looped.module "Looped" { text := loopedText, theorems := ofText "looped" }
  let loopedProof ← startLakeLean work "Looped" loopedModule.text

  let _ ← check work "Twice" written
    { text := template ++ converseText, theorems := ofText "twice" ++ ["twice_pays_first"] }
    [halvedControl]
  let (ok, output) ← finishLean nestedProof
  acceptedOutput "Nested" ok output nestedModule.theorems allowed
  let (ok, output) ← finishLean loopedProof
  acceptedOutput "Looped" ok output loopedModule.theorems allowed
  IO.println ("Twice is judged within the table of caps of its goal (the draw of the protocol " ++
    "that it applies at 1/4, under two applications: 1/2), with the call of a function inside " ++
    "the callee taken by a law stated before the root; a root that applies a protocol that " ++
    "applies it, with the roles in the other order, is judged by the same text, and a root " ++
    "that applies it in the body of a loop by an invariant; " ++
    "1 of 1 control refused, at the place that the check names and at no other.")

end TwiceCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work => TwiceCharge.run "checks/TwiceCharge.lean.in" work
