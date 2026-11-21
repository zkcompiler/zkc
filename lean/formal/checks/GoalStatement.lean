import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Written.Package
import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SyntaxHarness
import Zkc.Tests.Frontend.PrintedPackageSupport

/-!
The statement of a written soundness goal is about the goal of the source.

A statement names a deciding role, applies the relation of the goal's clause to operands and
bounds an event. Each of the three is read from the goal by `goalClaims`, and the generator
(`Written.Statements`) takes none of them from its caller. The check reads sources with the
frontend and asserts what a change of the source does to the statement, with the two directions
side by side: a change that leaves the goal as it is leaves the statement as it is, and a change
of the goal changes the statement or is refused.

- **The operands.** The ports of the source and the inputs of the deployed header are two
  lists, since a `spec` port is erased. With a `spec` port that nothing uses in front of the
  operand, or behind it, the operand is the same input of the header and the claim is the same
  text; with another port of the same type as operand, the operand is another input and the
  claim another text. A claim names its inputs as the source names its ports: the relation is
  applied to `input_flag`, and the deciding role is run on `input_flag` and `input_other`.
- **Which values a statement may be about** (GL3 with SC4). An operand that the verifier holds
  alone is refused under GL3, though the deciding role can read it; one that the prover holds
  alone is refused under SX6, as before; one that is a `spec` port is refused as not issued yet.
  Each refusal names the operand.
- **The deciding role.** Two schemes of one protocol with the provers `P` and `V` have the
  verifiers `V` and `P`. A goal of each, read alone, has its own verifier. The goals of two
  schemes are refused as one package, in either order, also where the two schemes have one
  verifier; two goals of one scheme are one package, and the claim of each is the text that it
  has when the goal is read alone.
- **The event.** A goal that reads a `reduces` clause has its claims read, and gets no
  statement: its statement is about a return on which the reduced statement is true.
- **The budget.** The table of caps of a goal is read with the goal: every charge that the root
  reaches, by use (SX8). Two charged draws of the root are both in it; a callee at two proof
  arguments is two uses, each call names its own, and exchanging the arguments exchanges the
  caps of the two calls while the total stays; two calls at one argument share a use; a call in
  a kept loop has the loop's count; the blocks of a stepped loop each have a draw. A charge on
  an application is refused as not in a table yet. No caller names a draw.
- **The records.** The goals of statements are those of their claims, and Lean refuses a module
  that alters the operands or the table of caps of a claimed goal, or the verifier of a
  package: the two records are made by the reader alone.

Then Lean is run on two more modules. Both have a consumer that a reader of the source could write
without the generator: a theorem that names none of the generated propositions, has the
verifier as its place in the roster, and says, of every admitted program, that this role of the
protocol with the inputs `flag = false` and `other = true` returns with probability at most zero when the relation is false of `false`,
under the service that draws by the laws. It writes the probability of the simulation out, and
does not use the library's name for the experiment (`ReturnsWithin`): its proof is the
published theorem of the goal at those inputs and that service, so it also checks that the
experiment of the statement is the one that a reader would write.

- In the first module the source has a `spec` port in front of `flag` and its clause is
  `proves @V IsSet(flag)`. The published theorem and the consumer are proved.
- In the control the clause is `proves @V IsSet(other)`, with a verifier that guards `other`.
  The published theorem is proved, and it is about the other input: the consumer is refused,
  where it gives the published theorem its premise.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

namespace GoalStatementCheck

def expect (title : String) (holds : Bool) : IO Unit :=
  unless holds do throw (IO.userError title)

/-- A protocol of two flags whose verifier draws a bit and guards `flag`: its ports, and the
clause of its contract. -/
def flags (ports clause : String) : String :=
  "module t\nuse zkc::security::{soundness}\nrelation IsSet(b: bool): b\n" ++
  s!"protocol Flags roles(P, V)({ports}):\n" ++
  "    bit <- draw bool from V to P\n    guard @V flag\n" ++
  s!"spec for Flags:\n    {clause}\n    charge sites.bit <= 1 / 2\n" ++
  "scheme Checked = Flags:\n    prover P\n    construction interactive\n" ++
  "goal sound = soundness(Checked)\n"

def both : String := "flag: bool @(P, V), other: bool @(P, V)"

/-- The statements of the goals of a source. -/
def statementsOf (text : String) (goals : List String) : Except String Statements := do
  let some first := goals.head? | throw "no goal"
  return { claims := ← goalClaims (← goalRoot text first) goals }

/-- The places of the operands of the one goal of a source among the inputs of the deployed
header, and the text of its claim about the installed program. -/
def claimOf (text : String) : Except String (Array Nat × String) := do
  let s ← statementsOf text ["sound"]
  let [goal] := s.claims.goals | throw "not one goal"
  return (goal.statement, ← s.claimAt standardModelText goal "installed" "rootMember" "soundMember")

/-- A source whose goal is refused, for a reason that the refusal states. -/
def refused (title text : String) (reasons : List String) : IO Unit :=
  match claimOf text with
  | .ok _ => throw (IO.userError s!"{title}: a statement was written")
  | .error why =>
    unless reasons.all (fun reason => why.contains reason) do
      throw (IO.userError s!"{title}: refused for another reason: {why}")

/-- One protocol under three schemes, the second with the roles of prover and verifier
exchanged, and four goals: `a` and `d` of the first scheme, `b` of the second, `c` of the
third. -/
def schemes : String :=
  "module t\nuse zkc::security::{soundness}\nrelation IsSet(b: bool): b\n" ++
  "protocol Pair roles(P, V)(flag: bool @(P, V)):\n    guard @V flag\n    guard @P true\n" ++
  "spec for Pair:\n    proves @V vr: IsSet(flag)\n    proves @P pr: IsSet(flag)\n" ++
  "scheme First = Pair:\n    prover P\n    construction interactive\n" ++
  "scheme Second = Pair:\n    prover V\n    construction interactive\n" ++
  "scheme Third = Pair:\n    prover P\n    construction interactive\n" ++
  "goal a = soundness(First, clause = vr)\ngoal b = soundness(Second, clause = pr)\n" ++
  "goal c = soundness(Third, clause = vr)\ngoal d = soundness(First, clause = vr)\n"

/-- A root over a claim, for the tables of caps: the definitions before the scheme, and the name
of the root. -/
def charged (definitions root : String) : String :=
  "module t\nuse zkc::security::{soundness}\nrelation Holds(claim: bool): claim\n" ++ definitions ++
  s!"scheme Checked = {root}:\n    prover P\n    construction interactive\n" ++
  "goal sound = soundness(Checked)\n"

/-- A root with two charged draws. -/
def twoDraws : String := charged
  ("protocol Two roles(P, V)(claim: bool @(P, V)):\n" ++
    "    x <- draw index<8> from V to P\n    y <- draw index<2> from V to P\n    guard @V claim\n" ++
    "spec for Two:\n    proves @V Holds(claim)\n    charge sites.x <= 3 / 8\n    charge sites.y <= 1 / 2\n")
  "Two"

/-- A callee whose charge is its proof argument over eight, applied twice. -/
def twoCalls (first second : String) : String := charged
  ("protocol Once<spec e: nat> roles(P, V)(claim: bool @(P, V)):\n" ++
    "    z <- draw index<8> from V to P\n" ++
    "spec for Once:\n    charge sites.z <= e / 8\n" ++
    "protocol Caller roles(P, V)(claim: bool @(P, V)):\n" ++
    s!"    Once<spec e = {first}>(claim)\n    Once<spec e = {second}>(claim)\n    guard @V claim\n" ++
    "spec for Caller:\n    proves @V Holds(claim)\n")
  "Caller"

/-- A callee applied once and three times in a kept loop, beside a draw of the caller. -/
def loopedCalls : String := charged
  ("protocol Once roles(P, V)(claim: bool @(P, V)):\n" ++
    "    z <- draw index<8> from V to P\n" ++
    "spec for Once:\n    charge sites.z <= 1 / 8\n" ++
    "protocol Caller roles(P, V)(claim: bool @(P, V)):\n" ++
    "    Once(claim)\n    for i in 0..3:\n        Once(claim)\n" ++
    "    own <- draw index<4> from V to P\n    guard @V claim\n" ++
    "spec for Caller:\n    proves @V Holds(claim)\n    charge sites.own <= 1 / 4\n")
  "Caller"

/-- A stepped loop: the type of the draw depends on the index. -/
def steppedDraws : String := charged
  ("protocol Steps roles(P, V)(claim: bool @(P, V)):\n" ++
    "    for i in 0..3:\n        r <- draw index<i + 2> from V to P\n    guard @V claim\n" ++
    "spec for Steps:\n    proves @V Holds(claim)\n    charge sites.r <= 1 / 2\n")
  "Steps"

/-- A charged draw in each arm of a choice. -/
def chargedArms : String := charged
  ("protocol Arms roles(P, V)(claim: bool @(P, V)):\n" ++
    "    if claim:\n        x <- draw index<8> from V to P\n" ++
    "    else:\n        y <- draw index<4> from V to P\n    guard @V claim\n" ++
    "spec for Arms:\n    proves @V Holds(claim)\n    charge sites.x <= 1 / 8\n    charge sites.y <= 1 / 4\n")
  "Arms"

/-- A callee that the root reaches by three ways: through `A`, which applies it twice in a kept
loop, through `B`, and through `A` again in a kept loop of five. -/
def sharedCallee : String := charged
  ("protocol Once roles(P, V)(claim: bool @(P, V)):\n" ++
    "    z <- draw index<8> from V to P\n" ++
    "spec for Once:\n    charge sites.z <= 1 / 8\n" ++
    "protocol A roles(P, V)(claim: bool @(P, V)):\n    for i in 0..2:\n        Once(claim)\n" ++
    "protocol B roles(P, V)(claim: bool @(P, V)):\n    Once(claim)\n" ++
    "protocol Caller roles(P, V)(claim: bool @(P, V)):\n    A(claim)\n    B(claim)\n" ++
    "    for i in 0..5:\n        A(claim)\n    guard @V claim\n" ++
    "spec for Caller:\n    proves @V Holds(claim)\n")
  "Caller"

/-- A charge on an application. -/
def chargedCall : String := charged
  ("protocol Once roles(P, V)(claim: bool @(P, V)):\n" ++
    "    z <- draw index<8> from V to P\n" ++
    "protocol Caller roles(P, V)(claim: bool @(P, V)):\n" ++
    "    first <- Once(claim)\n    guard @V claim\n" ++
    "spec for Caller:\n    proves @V Holds(claim)\n    charge sites.first <= 1 / 8\n")
  "Caller"

/-- A charge of the caller on a site of its callee. -/
def calleeSite : String := charged
  ("protocol Once roles(P, V)(claim: bool @(P, V)):\n" ++
    "    z <- draw index<8> from V to P\n" ++
    "protocol Caller roles(P, V)(claim: bool @(P, V)):\n" ++
    "    first <- Once(claim)\n    guard @V claim\n" ++
    "spec for Caller:\n    proves @V Holds(claim)\n    charge sites.first.z <= 1 / 8\n")
  "Caller"

/-- A draw under a loop whose count is read at run time, with a charge on it or with none. -/
def runtimeDraws (charge : String) : String := charged
  ("protocol Runs roles(P, V)(claim: bool @(P, V), n: index<4> @(P, V)):\n" ++
    "    for i in 0..n:\n        z <- draw index<8> from V to P\n    guard @V claim\n" ++
    "spec for Runs:\n    proves @V Holds(claim)\n" ++ charge)
  "Runs"

/-- Two charges on one draw. -/
def chargedTwice : String := charged
  ("protocol Two roles(P, V)(claim: bool @(P, V)):\n" ++
    "    z <- draw index<8> from V to P\n    guard @V claim\n" ++
    "spec for Two:\n    proves @V Holds(claim)\n    charge sites.z <= 1 / 8\n    charge sites.z <= 1 / 2\n")
  "Two"

/-- An application under a loop whose count is read at run time, of a callee with the given
contract. -/
def runtimeCalls (contract : String) : String := charged
  ("protocol Once roles(P, V)(claim: bool @(P, V)):\n" ++
    "    z <- draw index<8> from V to P\n" ++ contract ++
    "protocol Caller roles(P, V)(claim: bool @(P, V), n: index<4> @(P, V)):\n" ++
    "    for i in 0..n:\n        Once(claim)\n    guard @V claim\n" ++
    "spec for Caller:\n    proves @V Holds(claim)\n")
  "Caller"

/-- A reduction: the verifier returns its input, and the clause reduces the statement about the
input to the statement about the result. -/
def reduction : String :=
  "module t\nuse zkc::security::{soundness}\nrelation IsSet(b: bool): b\n" ++
  "protocol Flags roles(P, V)(flag: bool @(P, V)) -> echoed: bool @(P, V):\n" ++
  "    bit <- draw bool from V to P\n    return flag\n" ++
  "spec for Flags:\n    reduces @V IsSet(flag) to IsSet(echoed)\n    charge sites.bit <= 1 / 2\n" ++
  "scheme Checked = Flags:\n    prover P\n    construction interactive\n" ++
  "goal sound = soundness(Checked)\n"

/-- A protocol whose verifier decides without a coin: it guards one of two flags. The draw of
the contract's charge is in a loop that does not run. -/
def decided (ports guarded clause : String) : String :=
  "module t\nuse zkc::security::{soundness}\nrelation IsSet(b: bool): b\n" ++
  s!"protocol Flags roles(P, V)({ports}):\n" ++
  s!"    guard @V {guarded}\n    for i in 0..0:\n        z <- draw index<1> from V to P\n" ++
  s!"spec for Flags:\n    {clause}\n    charge sites.z <= 0\n" ++
  "scheme Checked = Flags:\n    prover P\n    construction interactive\n" ++
  "goal sound = soundness(Checked)\n"

/-- The text of the proofs of a module about `decided`: the verifier rejects where the guarded
flag is false, which is where the relation is false of it; the hypotheses are met over the
finite model; and the consumer.

The consumer names no generated proposition and no generated role: the verifier is the second
role of the roster, written as its place. It states, for every admitted program with the
protocol and the relation found by their keys: where the relation returns false of `false`, that
role on the inputs `false` and `true` returns with probability at most zero under the service of
the laws. Its proof is the published theorem `sound_sound` at those inputs. -/
def proofText (guarded : String) : String :=
  let (first, second) := if guarded == "flag" then ("false", "other") else ("flag", "false")
  "noncomputable section\n" ++
  "open Zkc.Formal.Written.StandardModel\n" ++
  "open Zkc.Formal.Written.FiniteModel (data)\n\n" ++
  "theorem sound_installed : soundClaim := by\n" ++
  "  intro F G D _ _ path flag _ other _ premise σ service conforms state\n" ++
  s!"  have declined : {guarded} = false := by\n" ++
  "    have computed : functionResult (t := .bool)\n" ++
  s!"        (fnMeaning (model D) installed soundMember (.cons {guarded} .nil)) = some {guarded} := by\n" ++
  "      kernel_rfl\n" ++
  "    rw [computed] at premise\n    exact Option.some.inj premise\n" ++
  "  subst declined\n" ++
  "  have rejected : roleMeaning (model D) installed rootMember verifierRole path\n" ++
  s!"      (.cons {first} (.cons {second} .nil)) = .halt (.declared .reject ⟨path, ⟨0⟩⟩) := by\n" ++
  "    kernel_rfl\n" ++
  "  have never : Pr{let out ← (simulateQ (handlerOf service) (embed\n" ++
  "      (roleMeaning (model D) installed rootMember verifierRole path\n" ++
  s!"        (.cons {first} (.cons {second} .nil))))).run.run state}[\n" ++
  "      ∃ results, out.1 = some (.inl results)] ≤ soundCaps.total := by\n" ++
  "    rw [prEvent_simulation_returns, rejected]\n    simp [run, Process.interpret]\n" ++
  "  simpa using never\n\n" ++
  "theorem sound_witnessed : soundWitnessed :=\n" ++
  "  ⟨_, _, data, inferInstance, inferInstance, false, trivial, false, trivial,\n" ++
  "    ⟨Unit, serveLaws (model data) (draws data), ⟨()⟩, serveLaws_follows _ _,\n" ++
  "      serveLaws_permitted _ _ (StandardModel.draws_permitted data)⟩, by kernel_rfl⟩\n\n" ++
  "end\n"

def consumer : String :=
  "noncomputable section\n" ++
  "open Zkc.Formal.Written.StandardModel\n" ++
  "open Zkc.Formal.Written.FiniteModel (data)\n\n" ++
  "theorem consumer {a : Admitted V} (admitted : admit stored association = .ok a) :\n" ++
  "    ∃ root : Member a.program.headers.protocols rootHeader,\n" ++
  "      a.program.findProtocol rootKey = some ⟨rootHeader, root⟩ ∧\n" ++
  "      ∃ relation : Member a.program.headers.fns soundHeader,\n" ++
  "        a.program.find soundKey = some (.fn relation) ∧\n" ++
  "        (functionResult (t := .bool)\n" ++
  "            (fnMeaning (model data) a.program relation (.cons false .nil)) = some false →\n" ++
  "          Pr{let out ← (simulateQ (handlerOf (serveLaws (model data) (draws data))) (embed\n" ++
  "              (roleMeaning (model data) a.program root 1 []\n" ++
  "                (.cons false (.cons true .nil))))).run.run ()}[\n" ++
  "            ∃ results, out.1 = some (.inl results)] ≤ 0) := by\n" ++
  "  have free : soundCaps.total = 0 := by\n" ++
  "    rw [CapTable.total, sound_budget]\n    simp [toProbability]\n" ++
  "  obtain ⟨root, found, relation, foundRelation, claim⟩ := sound_sound admitted\n" ++
  "  refine ⟨root, found, relation, foundRelation, fun rejected => ?_⟩\n" ++
  "  rw [← free]\n" ++
  "  simpa using claim data [] false trivial true trivial rejected _ (serveLaws (model data) (draws data))\n" ++
  "    ⟨serveLaws_follows _ _, serveLaws_permitted _ _ (StandardModel.draws_permitted data)⟩ ()\n\n" ++
  "end\n"

/-- The proof module of a source, as the generator assembles it for a text that does not walk:
the package of its claims, what the generator writes around the proofs, the proofs and the
consumer. -/
def proofModule (name text guarded : String) : IO Module := do
  let s ← IO.ofExcept (statementsOf text ["sound"])
  IO.ofExcept (s.module standardModelText name
    { text := proofText guarded, theorems := ["sound_installed", "sound_witnessed"]
      method := .direct }
    (walks := false) (after := { text := consumer, theorems := ["consumer"] }))

def run (work : System.FilePath) : IO Unit := do
  -- The operands: a `spec` port that nothing uses changes neither the input nor the claim, and
  -- another port of the same type changes both.
  let base ← IO.ofExcept (claimOf (flags both "proves @V IsSet(flag)"))
  expect "the operand `flag` is not the first input of the deployed header" (base.1 == #[0])
  expect s!"the claim does not name its inputs as the source does:\n{base.2}"
    (base.2.contains "soundMember (.cons input_flag .nil)) = some false" &&
      base.2.contains "verifierRole path (.cons input_flag (.cons input_other .nil))")
  let inFront ← IO.ofExcept (claimOf (flags ("spec note: bool, " ++ both) "proves @V IsSet(flag)"))
  expect "a spec port in front of the operand changed the operand or the claim" (inFront == base)
  let behind ← IO.ofExcept (claimOf (flags (both ++ ", spec note: bool") "proves @V IsSet(flag)"))
  expect "a spec port behind the operand changed the operand or the claim" (behind == base)
  let other ← IO.ofExcept (claimOf (flags both "proves @V IsSet(other)"))
  expect "the operand `other` is not the second input of the deployed header" (other.1 == #[1])
  expect "another operand of the same type left the claim as it was"
    (other.2 != base.2 && other.2.contains "soundMember (.cons input_other .nil)) = some false")
  let otherInFront ← IO.ofExcept (claimOf (flags ("spec note: bool, " ++ both) "proves @V IsSet(other)"))
  expect "a spec port in front of the other operand changed the operand or the claim" (otherInFront == other)

  -- Which values a statement may be about.
  refused "an operand that is a spec port" (flags ("spec note: bool, " ++ both) "proves @V IsSet(note)")
    ["WK-CLAUSE", "`note` is a specification port"]
  refused "an operand that the verifier holds alone"
    (flags "flag: bool @(P, V), other: bool @V private" "proves @V IsSet(other)")
    ["GL3", "`other` is held by V", "SC4"]
  refused "an operand that the prover holds alone"
    (flags "flag: bool @(P, V), other: bool @P" "proves @V IsSet(other)") ["SX6"]

  -- The deciding role: of the goal's scheme, and one scheme to a package.
  let verifiers (goals : List String) : Except String (Nat × Nat × Nat) := do
    let root ← goalRoot schemes goals.head!
    let claims ← goalClaims root goals
    return (claims.verifier, claims.prover, claims.goals.length)
  for (goal, verifier, prover) in [("a", 1, 0), ("b", 0, 1), ("c", 1, 0), ("d", 1, 0)] do
    expect s!"the verifier and the prover of the goal {goal}, read alone"
      ((verifiers [goal]).toOption == some (verifier, prover, 1))
  expect "two goals of one scheme are not one package" ((verifiers ["a", "d"]).toOption == some (1, 0, 2))
  -- The claim of a goal read with another goal of its scheme is its claim read alone.
  let claimsOf (goals : List String) : Except String (List (String × String)) := do
    let root ← goalRoot schemes goals.head!
    let s : Statements := { claims := ← goalClaims root goals }
    s.claims.goals.mapM fun goal => do
      return (goal.goal, ← s.claimAt standardModelText goal "installed" "rootMember" s!"{goal.goal}Member")
  let together ← IO.ofExcept (claimsOf ["a", "d"])
  expect "the claims of two goals of one scheme are not their claims read alone"
    (together == (← IO.ofExcept (claimsOf ["a"])) ++ (← IO.ofExcept (claimsOf ["d"])))
  for goals in [["a", "b"], ["b", "a"], ["a", "c"], ["c", "a"]] do
    match verifiers goals with
    | .ok _ => throw (IO.userError s!"the goals {goals} of two schemes were read as one package")
    | .error why =>
      expect s!"the goals {goals} were refused for another reason: {why}"
        (why.contains "WK-GOAL" && why.contains "the claims of a package are of one scheme")
  match (goalRoot schemes "a").bind (goalClaims · []) with
  | .ok _ => throw (IO.userError "a package of claims without a goal was read")
  | .error _ => pure ()

  -- The budget: the table of caps of the goal, as uses, and its total.
  let tableOf (text : String) : Option (CapTable × Rat) := do
    let s ← (statementsOf text ["sound"]).toOption
    let [goal] := s.claims.goals | none
    return (goal.caps, goal.total)
  expect "two charged draws of the root are not both in its table"
    (tableOf twoDraws == some (⟨[⟨⟨1⟩, [⟨⟨0⟩, 3, 8, 1⟩, ⟨⟨1⟩, 1, 2, 1⟩], []⟩]⟩, 7 / 8))
  expect "a callee at the proof arguments 3 and 2 is not two uses, each call with its own"
    (tableOf (twoCalls "3" "2") == some (⟨[⟨⟨1⟩, [⟨⟨0⟩, 3, 8, 1⟩], []⟩, ⟨⟨1⟩, [⟨⟨0⟩, 1, 4, 1⟩], []⟩,
      ⟨⟨2⟩, [], [⟨⟨0⟩, 1, 0⟩, ⟨⟨1⟩, 1, 1⟩]⟩]⟩, 5 / 8))
  expect "exchanging the proof arguments does not exchange the caps of the two calls"
    (tableOf (twoCalls "2" "3") == some (⟨[⟨⟨1⟩, [⟨⟨0⟩, 1, 4, 1⟩], []⟩, ⟨⟨1⟩, [⟨⟨0⟩, 3, 8, 1⟩], []⟩,
      ⟨⟨2⟩, [], [⟨⟨0⟩, 1, 0⟩, ⟨⟨1⟩, 1, 1⟩]⟩]⟩, 5 / 8))
  expect "two calls at one proof argument do not share a use"
    (tableOf (twoCalls "3" "3") == some (⟨[⟨⟨1⟩, [⟨⟨0⟩, 3, 8, 1⟩], []⟩,
      ⟨⟨2⟩, [], [⟨⟨0⟩, 1, 0⟩, ⟨⟨1⟩, 1, 0⟩]⟩]⟩, 3 / 4))
  expect "a call in a kept loop has not the count of the loop"
    (tableOf loopedCalls == some (⟨[⟨⟨1⟩, [⟨⟨0⟩, 1, 8, 1⟩], []⟩,
      ⟨⟨2⟩, [⟨⟨3⟩, 1, 4, 1⟩], [⟨⟨0⟩, 1, 0⟩, ⟨⟨1⟩, 3, 0⟩]⟩]⟩, 3 / 4))
  expect "the blocks of a stepped loop do not each have a draw"
    (tableOf steppedDraws == some (⟨[⟨⟨1⟩, [⟨⟨0⟩, 1, 2, 1⟩, ⟨⟨2⟩, 1, 2, 1⟩, ⟨⟨4⟩, 1, 2, 1⟩], []⟩]⟩, 3 / 2))
  -- The arms of a choice are added, though one of them runs: the total is no smaller than what
  -- a run can cost.
  expect "the charged draws of the two arms of a choice are not both in the table"
    (tableOf chargedArms == some (⟨[⟨⟨1⟩, [⟨⟨0⟩, 1, 8, 1⟩, ⟨⟨1⟩, 1, 4, 1⟩], []⟩]⟩, 3 / 8))
  -- A callee reached by three ways is one use, and its draw is counted thirteen times: twice
  -- through `A`, once through `B`, and five times twice through `A` in the loop.
  expect "a callee reached by three ways is not one use with the counts of the ways"
    (tableOf sharedCallee == some (⟨[⟨⟨1⟩, [⟨⟨0⟩, 1, 8, 1⟩], []⟩, ⟨⟨2⟩, [], [⟨⟨0⟩, 2, 0⟩]⟩,
      ⟨⟨3⟩, [], [⟨⟨0⟩, 1, 0⟩]⟩, ⟨⟨4⟩, [], [⟨⟨0⟩, 1, 1⟩, ⟨⟨1⟩, 1, 2⟩, ⟨⟨2⟩, 5, 1⟩]⟩]⟩, 13 / 8))
  -- What has no table yet is refused with the reason, and no claim is read.
  for (title, text, reason) in [
      ("a charge on an application", chargedCall, "`sites.first` is no draw"),
      ("a charge on a site of a callee", calleeSite, "a charge on a site of a callee"),
      ("a charged draw under a loop of a run-time count",
        runtimeDraws "    charge sites.z <= 1 / 8\n", "the draw `z` of `Runs` is under a loop whose count is read at run time"),
      ("two charges on one draw", chargedTwice, "a second charge on `sites.z`"),
      ("an application under a loop of a run-time count",
        runtimeCalls "spec for Once:\n    charge sites.z <= 1 / 8\n",
        "an application in `Caller` is under a loop whose count is read at run time"),
      ("an application of a callee without a charge under a loop of a run-time count",
        runtimeCalls "", "an application in `Caller` is under a loop whose count is read at run time")] do
    match statementsOf text ["sound"] with
    | .ok _ => throw (IO.userError s!"{title} was read into a table")
    | .error why =>
      expect s!"{title} was refused for another reason: {why}"
        (why.contains "WK-CHARGE" && why.contains reason)
  -- A draw without a charge under such a loop is in no table: it is allowed nothing.
  expect "a draw without a charge under a loop of a run-time count is in a table"
    (tableOf (runtimeDraws "") == some (⟨[⟨⟨1⟩, [], []⟩]⟩, 0))

  -- The event: the claims of a reduction are read, and no statement is written for them.
  let reduced ← IO.ofExcept (statementsOf reduction ["sound"])
  let [reducedGoal] := reduced.claims.goals | throw (IO.userError "the reduction has not one goal")
  expect "the clause of the reduction is not read as a reduction" (reducedGoal.clause.kind == .reduces)
  for written in [reduced.claimTexts standardModelText,
      reduced.claimAt standardModelText reducedGoal "installed" "rootMember" "soundMember"] do
    match written with
    | .ok _ => throw (IO.userError "a statement was written for a `reduces` clause")
    | .error why => expect s!"the reduction was refused for another reason: {why}" (why.contains "reduces")

  -- The records of a goal are made by the reader alone: Lean refuses to alter them.
  let closed ← startLakeLean work "Closed"
    ("import Zkc.Frontend.Written.Statement\nopen Zkc.Frontend.Written\n" ++
      "example (claimed : ClaimedGoal) : ClaimedGoal := { claimed with statement := #[1] }\n" ++
      "example (claims : GoalClaims) : GoalClaims := { claims with verifier := 0 }\n" ++
      "example (claimed : ClaimedGoal) : ClaimedGoal := { claimed with caps := ⟨[]⟩ }\n" ++
      "example (claimed : ClaimedGoal) : Array Nat := claimed.statement\n")

  -- Lean: the published theorem at the inputs of the source, by a consumer written apart.
  let fronted := decided ("spec note: bool, " ++ both) "flag" "proves @V IsSet(flag)"
  let aboutOther := decided ("spec note: bool, " ++ both) "other" "proves @V IsSet(other)"
  let module ← proofModule "Operands" fronted "flag"
  let theorems := module.theorems
  let proof ← startLakeLean work "Operands" module.text
  let control ← startLakeLean work "OperandsControl"
    (← proofModule "OperandsControl" aboutOther "other").text
  let (ok, output) ← finishLean closed
  expect s!"the records of a goal were altered outside the reader\n{output}"
    (!ok && output.contains "constructor for `ClaimedGoal` is marked as private" &&
      output.contains "constructor for `GoalClaims` is marked as private" &&
      (output.splitOn "error").length == 4)
  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  let (ok, output) ← finishLean proof
  acceptedOutput "Operands" ok output theorems allowed
  -- The published theorem of the control is about the second input. It is proved; the consumer,
  -- which reads the first, is not, and is refused where it gives the theorem its premise.
  expectUnproved "a clause about the other input" "OperandsControl" theorems control ["consumer"]
  let (_, refusal) ← finishLean control
  expect s!"the consumer of the control was refused for another reason\n{refusal}"
    (refusal.contains "The argument\n  rejected\nhas type" &&
      refusal.contains "(HList.cons true HList.nil)) = some false\nin the application")
  IO.println ("The statement of a goal reads its operands in the deployed header, its deciding role " ++
    "in the goal's scheme and its event in the clause: a spec port that nothing uses leaves the " ++
    "claim as it is, another operand changes it, and a consumer written apart uses the published " ++
    "theorem at the inputs of the source; 2 of 2 controls refused.")

end GoalStatementCheck

#eval show IO Unit from
  IO.FS.withTempDir fun work => GoalStatementCheck.run work
