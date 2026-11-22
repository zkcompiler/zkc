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
  after the text): for every judgment with fees that reads no peer of an effect;
- **a walk under another judgment** (`twice_returns`): on every permitted reply;
- **a walk under a judgment that reads peers** (`twice_first_effect`, with `twice_recorded`,
  a run that meets its hypothesis): the judgment that records the effects of a run. The walk
  goes into the application under every judgment; the callee is then judged under the judgment
  with its peers renamed. The nested root, whose roles are in the other order, shows the
  renaming: the peer of the first effect is the caller's (`nested_first_effect`), and a module
  that states the callee's is refused.

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

A fourth module is of a root that applies `Round` and then a protocol of the prover alone
(`Aside`). `Round` is then the second protocol before the root, and its entry equation is of
that place; in the application of the prover's protocol the verifier plays no role, its
program there has no effect, and the walk passes it as any other instruction.

A fifth module is of a root whose callees fork (`Forked`): one has a guard after its draw, the
other chooses by an input and has a draw and a guard in each arm. The text of the root names
the forks: the guard is a hypothesis of the walk, and the choice gives one goal for each arm.
The table has the draws of both arms as the arms of a choice, and its total is one half: the
draw of the first callee and the larger arm of the second.

Five controls are refused by Lean, each at the place that the check names and at no other:

- the charge of the draw halved in the source. The program is what it was; the cap that the
  table gives the draw through the application is one eighth, and the fee of one quarter that
  the text pays at the first application is refused there, with the name that the module gives
  that draw below that application;
- the body of the function that the callee calls turned. The law that the text states of it is
  refused, and nothing else is: the walks take the call by the law;
- a tactic of an effect inside an application, under a judgment with fees of which nothing
  says that it reads no peer: the goal in the callee is under the renamed judgment, and the
  tactic says so and names what would say it;
- a call of the callee's function taken by a true law of another function of the same types:
  refused at that line, since the header of a function has its key and the law is of another
  type than the call;
- the comparison of one arm of the forking callee turned. The walk is what it was, and the text
  is refused at the end of that arm.

A sixth module that Lean must refuse holds two programs. A law about a function of the same
header in another program, with another body, is of the type of the call, and what refuses it
is the equation between the two tables that the kernel checks where the law is used. The module
of a second source, whose `same` compares its first operand with itself, stands before the
module of `Twice`, and the text of `Twice` takes its first call by the law of the other: refused
at that line and nowhere else.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open Zkc.Tests.Frontend.WrittenSubject

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

/-- The text of that root: one application of `Round`, as in `Twice`; the walk passes the
application of the prover's protocol as it passes any instruction without an effect. The call
of `same` inside `Round` is taken by its value (`walk_compute`), with the law of the text as
the proof of the goal that this leaves. -/
def asideText : String :=
  "noncomputable section\n\n" ++
  "theorem aside_relation {F G : Type} (D : StandardModel.Data F G) [DecidableEq F]\n" ++
  "    [DecidableEq G] (claim : Bool) :\n" ++
  "    functionResult (t := .bool)\n" ++
  "      (fnMeaning (StandardModel.model D) installed asideMember (.cons claim .nil)) =\n" ++
  "        some claim := by\n  kernel_rfl\n\n" ++
  "theorem same_law {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]\n" ++
  "    (a b : ℕ) :\n" ++
  "    fnMeaning (StandardModel.model D) calleeProgram sameMember (.cons a (.cons b .nil)) =\n" ++
  "      .done (.cons (a.beq b) .nil) := by\n" ++
  "  refine done_of_judged ?_\n  repeat walk_step\n  subst_vars\n  rfl\n\n" ++
  "theorem aside_judged : asideJudged := by\n" ++
  "  claim_intro\n" ++
  "  obtain rfl : input_claim = false :=\n" ++
  "    Option.some.inj ((aside_relation D input_claim).symm.trans rejected)\n" ++
  "  walk_free as sent\n" ++
  "  walk_pay (1 / 4) excluding (fun drawn : ℕ => drawn = sent) as drawn differs\n" ++
  "  case weight => simpa using prEvent_drawPosition_eq_le 3 sent\n" ++
  "  -- the call of `same` in `Round`, by its value: the law is left where the module states\n" ++
  "  -- the function, in the table before the root, and the law of the text closes it\n" ++
  "  walk\n  walk_compute (.cons (drawn.beq sent) .nil)\n" ++
  "  case law => exact same_law D drawn sent\n" ++
  "  -- the application of `Keep` is passed, and the guard of the root is met\n" ++
  "  walk as hit\n" ++
  "  exact differs (Nat.eq_of_beq_eq_true hit)\n\n" ++
  "theorem aside_witnessed : asideWitnessed :=\n" ++
  "  aside_witnessed_of Zkc.Formal.Written.FiniteModel.data false trivial\n" ++
  "    (aside_relation _ false)\n\nend\n"

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

/-- The text of that root. The forks are inside the callees and the text of the root names
them: the guard of `Gate` after its draw is a hypothesis of the walk (`kept`), and the choice of
`Pick` forks the walk on the input that the root passed (`chosen`), into one goal for each arm.
In each arm the fee of the draw pays for the position that was sent, and the guard passes only
where one of the two draws is the position sent. -/
def forkedText : String :=
  "noncomputable section\n\n" ++
  "theorem forked_relation {F G : Type} (D : StandardModel.Data F G) [DecidableEq F]\n" ++
  "    [DecidableEq G] (claim : Bool) :\n" ++
  "    functionResult (t := .bool)\n" ++
  "      (fnMeaning (StandardModel.model D) installed forkedMember (.cons claim .nil)) =\n" ++
  "        some claim := by\n  kernel_rfl\n\n" ++
  "theorem same_law {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]\n" ++
  "    (a b : ℕ) :\n" ++
  "    fnMeaning (StandardModel.model D) calleeProgram sameMember (.cons a (.cons b .nil)) =\n" ++
  "      .done (.cons (a.beq b) .nil) := by\n" ++
  "  refine done_of_judged ?_\n  repeat walk_step\n  subst_vars\n  rfl\n\n" ++
  "theorem forked_judged : forkedJudged := by\n" ++
  "  claim_intro\n" ++
  "  obtain rfl : input_claim = false :=\n" ++
  "    Option.some.inj ((forked_relation D input_claim).symm.trans rejected)\n" ++
  "  -- the first application: the message and the draw of `Gate`\n" ++
  "  walk_free as first\n" ++
  "  walk_pay (1 / 4) excluding (fun drawn : ℕ => drawn = first) as one differs_one\n" ++
  "  case weight => simpa using prEvent_drawPosition_eq_le 3 first\n" ++
  "  -- the guard of `Gate` after its draw: a fork inside the callee, named here\n" ++
  "  walk as kept\n" ++
  "  guard_hyp kept : (!one.beq 3) = true\n" ++
  "  walk_law same_law D one first\n" ++
  "  -- the second application: the message of `Pick`, then its choice, which forks the walk\n" ++
  "  walk_free as second\n" ++
  "  walk as chosen\n" ++
  "  · -- the arm of a false side: its draw and its guard\n" ++
  "    guard_hyp chosen : input_side = false\n" ++
  "    walk_pay (1 / 4) excluding (fun drawn : ℕ => drawn = second) as two differs_two\n" ++
  "    case weight => simpa using prEvent_drawPosition_eq_le 3 second\n" ++
  "    walk as hit\n" ++
  "    rcases Bool.or_eq_true _ _ |>.mp hit with h | h\n" ++
  "    · exact differs_one (Nat.eq_of_beq_eq_true h)\n" ++
  "    · exact differs_two (Nat.eq_of_beq_eq_true h)\n" ++
  "  · -- the arm of a true side, as the other\n" ++
  "    guard_hyp chosen : input_side = true\n" ++
  "    walk_pay (1 / 4) excluding (fun drawn : ℕ => drawn = second) as two differs_two\n" ++
  "    case weight => simpa using prEvent_drawPosition_eq_le 3 second\n" ++
  "    walk as hit\n" ++
  "    rcases Bool.or_eq_true _ _ |>.mp hit with h | h\n" ++
  "    · exact differs_one (Nat.eq_of_beq_eq_true h)\n" ++
  "    · exact differs_two (Nat.eq_of_beq_eq_true h)\n\n" ++
  "theorem forked_witnessed : forkedWitnessed :=\n" ++
  "  forked_witnessed_of Zkc.Formal.Written.FiniteModel.data false trivial true trivial\n" ++
  "    (forked_relation _ false)\n\nend\n"

/-- The source of `Twice` with a second function of the same types, `other`, which a protocol of
the prover alone calls, so that the package has it; the root applies that protocol after the two
rounds, and the verifier takes no part in it. -/
def otherSource : String :=
  let same := "def same(a: index<4>, b: index<4>) -> bool: a == b\n"
  ((source "1 / 4").replace same (same ++
    "def other(a: index<4>, b: index<4>) -> bool: a != b\n" ++
    "protocol Spare roles(P)(x: index<4> @P) -> y: bool @P:\n    return other(x, x)\n")).replace
    "    b <- Round(second)\n" "    b <- Round(second)\n    k <- Spare(first)\n"

/-- The law of `other`, which is true of it, for a text that takes a call of `same` by it. -/
def otherLaw : String :=
  "/-- What `other` computes: a true law of another function of the same types. -/\n" ++
  "theorem other_law {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]\n" ++
  "    (a b : ℕ) :\n" ++
  "    fnMeaning (StandardModel.model D) calleeProgram otherMember (.cons a (.cons b .nil)) =\n" ++
  "      .done (.cons (!a.beq b) .nil) := by\n" ++
  "  refine done_of_judged ?_\n  repeat walk_step\n  subst_vars\n  rfl\n\n"

/-- A second program whose function `same` has the header of the one of `Twice` (its key and its
types) and another body: it compares its first operand with itself. Every round then hits, so
the root returns on the claim alone. -/
def sideSource : String :=
  round "1 / 4" "a == a" ++
  "protocol Twice roles(P, V)(claim: bool @(P, V), first: index<4> @P, second: index<4> @P):\n" ++
  "    a <- Round(first)\n    b <- Round(second)\n" ++
  "    guard @V claim\n" ++
  "spec for Twice:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Twice:\n    prover P\n    construction interactive\n" ++
  "goal twice = soundness(Checked, stage = written)\n"

/-- A walk of the verifier of `Twice` under the judgment that records the effects of a run,
which reads who gives and who gets. The rule of an application holds for every judgment: the
walk goes into the application, and the hypothesis is then stated under the judgment with its
peers renamed. A run that the judgment accepts begins with the message of `Round` at the path
of the first application, read from that hypothesis. -/
def tracedText : String :=
  "\n" ++
  "/-- **Under a judgment that reads peers the walk goes into an application too.** A run of\n" ++
  "the verifier that the judgment of recorded effects accepts begins with the message of\n" ++
  "`Round` at the path of the first application. -/\n" ++
  "theorem twice_first_effect {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]\n" ++
  "    (path : List Frame) (effects : EffectTrace (RSig (StandardModel.model D)))\n" ++
  "    (judged : (roleMeaning (StandardModel.model D) installed rootMember verifierRole path\n" ++
  "        (.cons true (.cons () (.cons () .nil)))).interpret\n" ++
  "      (ProcessJudgment.trace (RSig (StandardModel.model D)))\n" ++
  "      (fun _ _ => True) (fun _ _ => True) effects) :\n" ++
  "    ∃ first tail, effects =\n" ++
  "      ⟨.get .message 0 ⟨path ++ [.application ⟨0⟩], ⟨0⟩⟩ (.fin 4), first⟩ :: tail := by\n" ++
  "  walk at judged\n" ++
  "  obtain ⟨first, tail, said, _⟩ := judged\n" ++
  "  exact ⟨first, tail, said⟩\n" ++
  "\n" ++
  "/-- **The hypothesis of `twice_first_effect` is met**: the judgment of recorded effects accepts\n" ++
  "the record of a run of the verifier, two rounds of a message and a draw. The walk goes through\n" ++
  "both applications under the renamed judgment; at each effect the record is read off. -/\n" ++
  "theorem twice_recorded {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]\n" ++
  "    (path : List Frame) :\n" ++
  "    (roleMeaning (StandardModel.model D) installed rootMember verifierRole path\n" ++
  "        (.cons true (.cons () (.cons () .nil)))).interpret\n" ++
  "      (ProcessJudgment.trace (RSig (StandardModel.model D)))\n" ++
  "      (fun _ _ => True) (fun _ _ => True)\n" ++
  "      [⟨.get .message 0 ⟨path ++ [.application ⟨0⟩], ⟨0⟩⟩ (.fin 4), (0 : ℕ)⟩,\n" ++
  "       ⟨.own (.coin (Zkc.Vocabulary.LawKey.uniform (.fin 4))) [0]\n" ++
  "          ⟨path ++ [.application ⟨0⟩], ⟨1⟩⟩ [] .nil (.fin 4), (1 : ℕ)⟩,\n" ++
  "       ⟨.get .message 0 ⟨path ++ [.application ⟨1⟩], ⟨0⟩⟩ (.fin 4), (2 : ℕ)⟩,\n" ++
  "       ⟨.own (.coin (Zkc.Vocabulary.LawKey.uniform (.fin 4))) [0]\n" ++
  "          ⟨path ++ [.application ⟨1⟩], ⟨1⟩⟩ [] .nil (.fin 4), (3 : ℕ)⟩] := by\n" ++
  "  walk\n" ++
  "  refine ⟨_, _, rfl, ?_⟩\n" ++
  "  walk\n" ++
  "  refine ⟨_, _, rfl, ?_⟩\n" ++
  "  walk\n" ++
  "  walk_law same_law D 1 0\n" ++
  "  walk\n" ++
  "  refine ⟨_, _, rfl, ?_⟩\n" ++
  "  walk\n" ++
  "  refine ⟨_, _, rfl, ?_⟩\n" ++
  "  walk\n" ++
  "  walk_law same_law D 3 2\n" ++
  "  walk\n"

/-- The same reading in the nested root, whose roles are in the other order: the prover is role 1
of `Nested` and role 0 of `Pair` and of `Round`. The peer of the first effect is the caller's,
role `peer`: with 1 the theorem is proved, and with 0, the callee's, Lean refuses it, so a walk
that judged the callee under the judgment itself, not renamed, would be seen here. In `Twice`
it would not: there the two orders of roles are one. -/
def nestedTracedText (peer : Nat) : String :=
  "\n" ++
  "theorem nested_first_effect {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]\n" ++
  "    (path : List Frame) (effects : EffectTrace (RSig (StandardModel.model D)))\n" ++
  "    (judged : (roleMeaning (StandardModel.model D) installed rootMember verifierRole path\n" ++
  "        (.cons true (.cons () (.cons () .nil)))).interpret\n" ++
  "      (ProcessJudgment.trace (RSig (StandardModel.model D)))\n" ++
  "      (fun _ _ => True) (fun _ _ => True) effects) :\n" ++
  "    ∃ first tail, effects =\n" ++
  s!"      ⟨.get .message {peer} ⟨path ++ [.application ⟨0⟩] ++ [.application ⟨0⟩], ⟨0⟩⟩ (.fin 4), first⟩ :: tail := by\n" ++
  "  walk at judged\n" ++
  "  obtain ⟨first, tail, said, _⟩ := judged\n" ++
  "  exact ⟨first, tail, said⟩\n"

/-- A walk under a judgment with fees of which nothing says that it reads no peer (what is
permitted is written otherwise than the library's theorem has it): the walk goes into the
application, the goal in the callee is under the renamed judgment, and the tactic of an effect,
whose rule is about the judgment with fees itself, says so. -/
def unblindText : String :=
  "\n" ++
  "theorem twice_unblind {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]\n" ++
  "    (draws : LawDraws (StandardModel.model D)) (path : List Frame) :\n" ++
  "    (roleMeaning (StandardModel.model D) installed rootMember verifierRole path\n" ++
  "        (.cons false (.cons () (.cons () .nil)))).interpret\n" ++
  "      (.charged (fun op v => Permitted (StandardModel.model D) op v ∧ True)\n" ++
  "        (paysWithin (lawSamplers (StandardModel.model D) draws)\n" ++
  "          (twiceCaps.allowance (StandardModel.model D) path)))\n" ++
  "      (fun _ _ => False) (fun _ _ => True) twiceCaps.budget := by\n" ++
  "  walk_free as first\n"

/-- Three theorems after the text of `Twice` under other judgments than the goal's (the third is
`tracedText`, under a judgment that reads peers). The first
walks a hypothesis: a judgment of the verifier is given, and the walk goes through the first
application on it. The judgment is any judgment with
fees that reads no peer of an effect, which the theorem states as a hypothesis; the walk takes
the proof from there. The path of the application is the root's, so the theorem is of `Twice`
and not of the nested root. The second is under the judgment "on every permitted reply", which
the library proves reads no peer: on a true claim the verifier returns on every run, through
both applications. -/
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
  "  exact ⟨fee, excluded, least, paid⟩\n" ++
  "\n" ++
  "/-- **On a true claim the verifier returns on every run**, through both applications: the\n" ++
  "judgment \"on every permitted reply\" reads no peer either, and the walk goes into `Round` under\n" ++
  "it. -/\n" ++
  "theorem twice_returns {F G : Type} (D : StandardModel.Data F G) [DecidableEq F] [DecidableEq G]\n" ++
  "    (path : List Frame) :\n" ++
  "    (roleMeaning (StandardModel.model D) installed rootMember verifierRole path\n" ++
  "        (.cons true (.cons () (.cons () .nil)))).interpret\n" ++
  "      (.every (Permitted (StandardModel.model D))) (fun _ => True) (fun _ => False) := by\n" ++
  "  walk\n" ++
  "  intro first _\n" ++
  "  walk\n" ++
  "  intro one _\n" ++
  "  walk\n" ++
  "  walk_law same_law D one first\n" ++
  "  walk\n" ++
  "  intro second _\n" ++
  "  walk\n" ++
  "  intro two _\n" ++
  "  walk\n" ++
  "  walk_law same_law D two second\n" ++
  "  walk\n" ++
  tracedText

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

/-- Whether what a use adds up is one choice of two arms, a charged draw in each, and nothing
after it. -/
def twoArms : Tally Cap → Bool
  | .choice (.item (.draw _) .nil) (.item (.draw _) .nil) .nil => true
  | _ => false

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
  let refusal := "the fee is not within the cap that the table gives the draw `site_0_1`\n  1 / 4 ≤ 1 / 8"
  let halvedControl : Control :=
    { title := "the charge of the callee halved", name := "CapControl", subject := halved,
      text := template ++ converseText, unproved := ofWalk, places := [refusal], only := true,
      occurrences := [(refusal, 1)] }
  -- The body of the function that the callee calls turned: the law of the text is no longer
  -- what the function computes, and is refused there; the walks that take the call by it are
  -- left unproved and meet no other refusal.
  let turned ← read (source "1 / 4" "a != b") (reading "twice")
  let turnedControl : Control :=
    { title := "the function that the callee calls turned", name := "LawControl", subject := turned,
      text := template ++ converseText,
      unproved := "same_law" :: ofWalk ++ ["twice_returns", "twice_recorded"],
      places := ["The left-hand side\n  HList.cons (!a.beq b) HList.nil\n" ++
        "is not definitionally equal to the right-hand side\n  HList.cons (a.beq b) HList.nil"],
      only := true }
  -- A tactic of an effect inside an application, under a judgment with fees of which nothing
  -- says that it reads no peer: refused there, with the reason.
  let unblindControl : Control :=
    { title := "a fee tactic under a judgment that nothing says reads no peer", name := "UnblindControl",
      subject := written, text := template ++ converseText ++ unblindText, unproved := [],
      places := ["walk_free: the effect is inside an application, under a judgment with its peers " ++
        "renamed: nothing says that the judgment reads no peer of an effect"],
      only := true }
  -- A true law of another function of the same types, used at the first call of `same`: the
  -- header of a function has its key, so the law is of another type than the call, and the
  -- text is refused at that line.
  let other ← read otherSource (reading "twice")
  let beforeJudged := "/-- **Within the table.**"
  let otherText ← replaceOnce (← replaceOnce template beforeJudged (otherLaw ++ beforeJudged))
    "  walk_law same_law D one first\n" "  walk_law other_law D one first\n"
  let otherControl : Control :=
    { title := "a call taken by the law of another function", name := "OtherControl",
      subject := other, text := otherText ++ converseText, unproved := ofWalk,
      places := ["Type mismatch\n  other_law D one first"], only := true }
  -- A law about a function of the same header in another program: the module of the second
  -- source, with the text of its own proofs, and after it the module of `Twice`, whose text
  -- takes its first call of `same` by the law of the other program. The law is of the type of
  -- the call; the equation between the two tables is what the kernel refuses, at that line.
  let side ← read sideSource (reading "twice")
  let sideText ← replaceOnce (← replaceOnce template ".done (.cons (a.beq b) .nil)" ".done (.cons (a.beq a) .nil)")
    ("  walk as hit\n  rcases Bool.or_eq_true _ _ |>.mp hit with h | h\n" ++
      "  · exact differs_one (Nat.eq_of_beq_eq_true h)\n  · exact differs_two (Nat.eq_of_beq_eq_true h)\n")
    "  walk\n"
  let sideModule ← side.module "Side" { text := sideText, theorems := ofText "twice" }
  let foreignText ← replaceOnce template "  walk_law same_law D one first\n"
    "  walk_law Side.same_law D one first\n"
  let foreignModule ← written.module "Foreign" { text := foreignText, theorems := ofText "twice" }
  let foreign ← startLakeLean work "ForeignLaw" (asOne [sideModule, foreignModule])

  -- The nested root: one application in the root, two in the protocol that it applies.
  let nested ← read nestedSource (reading "nested")
  let nestedGoal ← nested.goal
  unless nestedGoal.total == 1 / 2 && shape nestedGoal.caps ==
      [([(1, 4, 1)], []), ([], [(0, 1), (0, 1)]), ([], [(1, 1)])] do
    throw (IO.userError s!"the table of the nested root is not one application of two: {repr nestedGoal.caps}")
  -- A control of it, the same with the callee's number for the peer: refused where the
  -- statement is concluded.
  let nestedPeer : Control :=
    { title := "the callee's number for the peer of an effect under a renamed judgment",
      name := "NestedPeer", subject := nested,
      text := template.replace "twice" "nested" ++ nestedTracedText 0,
      unproved := ["nested_first_effect"], places := ["Application type mismatch"], only := true }
  let nestedCheck ← start work "Nested" nested
    { text := template.replace "twice" "nested" ++ nestedTracedText 1,
      theorems := ofText "nested" ++ ["nested_first_effect"] } [nestedPeer]

  -- The looped root: one application in the body of a loop of three iterations.
  let looped ← read loopedSource (reading "looped" #["claim", "guess"])
  let loopedGoal ← looped.goal
  unless loopedGoal.total == 3 / 4 && shape loopedGoal.caps == [([(1, 4, 1)], []), ([], [(0, 3)])] do
    throw (IO.userError s!"the table of the looped root is not three applications: {repr loopedGoal.caps}")
  let loopedModule ← looped.module "Looped" { text := loopedText, theorems := ofText "looped" }
  let loopedProof ← startModule work "Looped" loopedModule

  -- The root beside a protocol of the prover alone: one application of `Round`, which is the
  -- second protocol before the root, and one in which the verifier takes no part.
  let aside ← read asideSource (reading "aside" #["claim", "first"])
  let asideGoal ← aside.goal
  unless asideGoal.total == 1 / 4 do
    throw (IO.userError s!"the table of the root beside a protocol is not one draw: {repr asideGoal.caps}")
  let asideModule ← aside.module "Aside" { text := asideText, theorems := ofText "aside" }
  unless (asideModule.statements.splitOn "(Member.tail Member.head)").length > 1 do
    throw (IO.userError "the protocol that the root applies first is the last before the root")
  let asideProof ← startModule work "Aside" asideModule
  -- The same module after the module of another program that has the same function `same`
  -- (the module of `Twice`): the entry equations of both are then in scope, and the value step
  -- of the text states its law in the text's own program, so that the text is accepted there
  -- as it is alone.
  let earlier ← written.module "Earlier"
    { text := template ++ converseText,
      theorems := ofText "twice" ++
        ["twice_pays_first", "twice_returns", "twice_first_effect", "twice_recorded"] }
  let twoPrograms ← startLakeLean work "TwoPrograms" (asOne [earlier, asideModule])

  let _ ← check work "Twice" written
    { text := template ++ converseText,
      theorems := ofText "twice" ++
        ["twice_pays_first", "twice_returns", "twice_first_effect", "twice_recorded"] }
    [halvedControl, turnedControl, unblindControl, otherControl]
  let (ok, output) ← finishLean foreign
  refusedOutput "a call taken by the law of a function of another program" ok output
    ["walk_law: the law is about a function that this call does not read"] (only := true)
  -- each of these tasks ends when its two modules are accepted, the proof module outside the
  -- file as well
  let _ ← nestedCheck.finish
  let _ ← finishLean loopedProof
  let _ ← finishLean asideProof
  let (ok, output) ← finishLean twoPrograms
  acceptedOutput "Aside" ok output (asideModule.stated ++ asideModule.proved) allowed

  -- The root whose callees fork, after the modules above (each is a run of Lean of its own):
  -- the draw of `Gate`, the draws of both arms of `Pick`, and one application of each.
  let forked ← read (forkedSource) (reading "forked" #["claim", "side", "first", "second"])
  let forkedGoal ← forked.goal
  unless forkedGoal.total == 1 / 2 && shape forkedGoal.caps ==
      [([(1, 4, 1)], []), ([(1, 4, 1), (1, 4, 1)], []), ([], [(0, 1), (1, 1)])] &&
      -- the two draws of `Pick` are the two arms of a choice, with nothing after it
      (forkedGoal.caps.uses.map fun use => twoArms use.caps) == [false, true, false] do
    throw (IO.userError s!"the table of the forked root is not three draws under two applications, with the larger arm of the choice: {repr forkedGoal.caps}")
  -- The comparison of one arm of `Pick` turned: the walk is what it was, and the text is
  -- refused at the end of that arm, where the guard no longer says that the draw is the
  -- position sent, and nowhere before.
  let arm ← read (forkedSource "s != x") (reading "forked" #["claim", "side", "first", "second"])
  let armControl : Control :=
    { title := "the comparison of an arm of the callee turned", name := "ArmControl", subject := arm,
      text := forkedText,
      unproved := ["forked_judged", "forked_installed", "forked_sound", "forked_result"],
      places := ["has type\n  (!two.beq second) = true\nbut is expected to have type\n  two.beq second = true"],
      only := true }
  let _ ← check work "Forked" forked { text := forkedText, theorems := ofText "forked" } [armControl]
  IO.println ("Twice is judged within the table of caps of its goal (the draw of the protocol " ++
    "that it applies at 1/4, under two applications: 1/2), with the call of a function inside " ++
    "the callee taken by a law stated before the root; a root that applies a protocol that " ++
    "applies it, with the roles in the other order, is judged by the same text, and a root " ++
    "that applies it in the body of a loop by an invariant, and a root that applies it and " ++
    "then a protocol of the prover alone, and a root whose callees have a guard after a draw " ++
    "and a choice, with the forks named by the root's text; " ++
    "under the judgment of recorded effects, which reads peers, the walk goes into the " ++
    "application as well; " ++
    "5 of 5 controls refused, at the places that the check names and at no other, and a law " ++
    "about a function of the same header in another program refused where it is used.")

end TwiceCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work => TwiceCharge.run "checks/TwiceCharge.lean.in" work
