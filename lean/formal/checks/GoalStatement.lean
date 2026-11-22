import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Written.Package
import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SyntaxHarness
import Zkc.Tests.Frontend.PrintedPackageSupport
import ZkcFormalTests.WrittenSubject

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

Then Lean is run on four more modules. All have a consumer that a reader of the source could write
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
- Two controls are of the text of the proofs, on the first source. Their text proves its claim
  itself (the other method than the judgment with fees). In one, the text takes its claim as a
  hypothesis of the module's scope: every theorem after the text takes that hypothesis, Lean
  proves each and accepts the module, and the judgment (`lake comparator`) refuses it: the
  statement of a published theorem is not the challenge's. In
  the other, the text defines a name of the claim again (the experiment, as a proposition that
  always holds) and proves the claim written anew: the goal is not concluded from it, and Lean
  refuses the module there.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests.WrittenSubject (startModule startRefused refusedOutside startLakeLean finishLean expectUnproved expectPlaces)

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

/-- A stepped loop over `r` beside a draw whose site has the name that the first block of that
loop would get. -/
def clashingSites : String := charged
  ("protocol Clash roles(P, V)(claim: bool @(P, V)):\n" ++
    "    for i in 0..2:\n        r <- draw index<i + 2> from V to P\n" ++
    "    r_0 <- draw index<4> from V to P\n    guard @V claim\n" ++
    "spec for Clash:\n    proves @V Holds(claim)\n    charge sites.r <= 1 / 2\n" ++
    "    charge sites.r_0 <= 1 / 4\n")
  "Clash"

/-- The same with no charge on the stepped loop: the charged draw has its site's name, as it
had when only charged draws were named. -/
def clashingUncharged : String := charged
  ("protocol Clash roles(P, V)(claim: bool @(P, V)):\n" ++
    "    for i in 0..2:\n        r <- draw index<i + 2> from V to P\n" ++
    "    r_0 <- draw index<4> from V to P\n    guard @V claim\n" ++
    "spec for Clash:\n    proves @V Holds(claim)\n" ++
    "    charge sites.r_0 <= 1 / 4\n")
  "Clash"

/-- A site whose name is an identifier of the source and no plain name for a module. -/
def greekSite : String := charged
  ("protocol Greek roles(P, V)(claim: bool @(P, V)):\n" ++
    "    β <- draw index<4> from V to P\n    guard @V claim\n" ++
    "spec for Greek:\n    proves @V Holds(claim)\n    charge sites.β <= 1 / 4\n")
  "Greek"

/-- A charged draw in each arm of a choice. -/
def chargedArms : String := charged
  ("protocol Arms roles(P, V)(claim: bool @(P, V)):\n" ++
    "    if claim:\n        x <- draw index<8> from V to P\n" ++
    "    else:\n        y <- draw index<4> from V to P\n    guard @V claim\n" ++
    "spec for Arms:\n    proves @V Holds(claim)\n    charge sites.x <= 1 / 8\n    charge sites.y <= 1 / 4\n")
  "Arms"

/-- A choice in a kept loop of three whose arms apply two callees, one charged one eighth and
the other one quarter. -/
def loopedArms : String := charged
  ("protocol Once roles(P, V)(claim: bool @(P, V)):\n    z <- draw index<8> from V to P\n" ++
    "spec for Once:\n    charge sites.z <= 1 / 8\n" ++
    "protocol Other roles(P, V)(claim: bool @(P, V)):\n    w <- draw index<4> from V to P\n" ++
    "spec for Other:\n    charge sites.w <= 1 / 4\n" ++
    "protocol Arms roles(P, V)(claim: bool @(P, V)):\n" ++
    "    for i in 0..3:\n        if claim:\n            Once(claim)\n        else:\n            Other(claim)\n" ++
    "    guard @V claim\n" ++
    "spec for Arms:\n    proves @V Holds(claim)\n")
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
  "open ZkcFormal.Written.StandardModel\n" ++
  "open ZkcFormal.Written.FiniteModel (data)\n\n" ++
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
  "open ZkcFormal.Written.StandardModel\n" ++
  "open ZkcFormal.Written.FiniteModel (data)\n\n" ++
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
def proofModule (name text guarded : String)
    (alter : Statements → String → Except String String := fun _ proof => pure proof) :
    IO Module := do
  let s ← IO.ofExcept (statementsOf text ["sound"])
  IO.ofExcept (s.module name
    { text := ← IO.ofExcept (alter s (proofText guarded))
      theorems := ["sound_installed", "sound_witnessed"]
      method := .direct }
    (walks := false) (after := { text := consumer, theorems := ["consumer"] }))

/-- The proof of the claim under another name, so that a control can state `sound_installed`
itself. -/
def established (proof : String) : Except String String := do
  let renamed := proof.replace "theorem sound_installed : soundClaim := by"
    "theorem sound_established : soundClaim := by"
  if renamed == proof then throw "the text does not prove the claim under its name"
  return renamed

/-- A text that proves nothing of its claim: after its last `end` it declares the claim as an
instance variable of the module's scope, with the two linters that would report that switched
off, and takes the claim from the variable. Every theorem that the generator writes after the
text then has the variable as a hypothesis: Lean accepts each and reports no axiom for it, and
none is a theorem of its proposition. -/
def assuming (_ : Statements) (proof : String) : Except String String := do
  return (← established proof) ++
    "\nset_option linter.unusedSectionVars false\nset_option linter.concreteInstances false\n" ++
    "variable [assumed : Fact soundClaim]\n" ++
    "theorem sound_installed : soundClaim := assumed.out\n"

/-- A text that defines again, in its own scope, a name of the library that the claim uses (the
experiment of a bound on returns, as a proposition that holds of everything) and proves the
claim written anew under it. The claim written anew is not the claim that was stated before the
text. -/
def shadowing (s : Statements) (proof : String) : Except String String := do
  let [goal] := s.claims.goals | throw "the statements are not of one goal"
  let anew ← s.claimAt standardModelText goal "installed" "rootMember" "soundMember"
  return (← established proof) ++ "\n" ++
    "def ReturnsWithin {S : Sig} {H A : Type} (_ : Process S H A) (_ : Samplers S)\n" ++
    "    (_ : ∀ op, S.Reply op → Prop) (_ : A → Prop) (_ : ℝ≥0∞) : Prop := True\n\n" ++
    s!"theorem sound_installed :\n  {anew} := by\n" ++
    "  intros\n  trivial\n"

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
    (tableOf twoDraws == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 3, 8, 1⟩, ⟨⟨1⟩, 1, 2, 1⟩] [])]⟩, 7 / 8))
  expect "a callee at the proof arguments 3 and 2 is not two uses, each call with its own"
    (tableOf (twoCalls "3" "2") == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 3, 8, 1⟩] []), (.flat ⟨1⟩ [⟨⟨0⟩, 1, 4, 1⟩] []),
      (.flat ⟨2⟩ [] [⟨⟨0⟩, 1, 0⟩, ⟨⟨1⟩, 1, 1⟩])]⟩, 5 / 8))
  expect "exchanging the proof arguments does not exchange the caps of the two calls"
    (tableOf (twoCalls "2" "3") == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 1, 4, 1⟩] []), (.flat ⟨1⟩ [⟨⟨0⟩, 3, 8, 1⟩] []),
      (.flat ⟨2⟩ [] [⟨⟨0⟩, 1, 0⟩, ⟨⟨1⟩, 1, 1⟩])]⟩, 5 / 8))
  expect "two calls at one proof argument do not share a use"
    (tableOf (twoCalls "3" "3") == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 3, 8, 1⟩] []),
      (.flat ⟨2⟩ [] [⟨⟨0⟩, 1, 0⟩, ⟨⟨1⟩, 1, 0⟩])]⟩, 3 / 4))
  expect "a call in a kept loop has not the count of the loop"
    (tableOf loopedCalls == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 1, 8, 1⟩] []),
      (.ordered ⟨2⟩ [.call ⟨⟨0⟩, 1, 0⟩, .call ⟨⟨1⟩, 3, 0⟩, .draw ⟨⟨3⟩, 1, 4, 1⟩])]⟩, 3 / 4))
  expect "the blocks of a stepped loop do not each have a draw"
    (tableOf steppedDraws == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 1, 2, 1⟩, ⟨⟨2⟩, 1, 2, 1⟩, ⟨⟨4⟩, 1, 2, 1⟩] [])]⟩, 3 / 2))
  -- The names that a module gives the draws of the root, charged or not: the site's, with the place
  -- of the block in a stepped loop; the key where two draws would share a name or the site's
  -- name is no plain identifier.
  let labelsOf (text : String) : Except String (List (String × Nat)) := do
    let s ← statementsOf text ["sound"]
    let [goal] := s.claims.goals | throw "the statements are not of one goal"
    return goal.siteLabels.map fun (_, label, key) => (label, key.number)
  for (title, text, labels) in [
      ("the draws of a stepped loop are not named after its site and their places",
        steppedDraws, [("r_0", 0), ("r_1", 2), ("r_2", 4)]),
      ("two draws that would share a name are not told apart by their keys",
        clashingSites, [("r_0_key0", 0), ("r_1", 2), ("r_0_key4", 4)]),
      ("a charged draw has not its site's name beside a draw without a charge that would share it",
        clashingUncharged, [("r_0_key0", 0), ("r_1", 2), ("r_0", 4)]),
      ("a site whose name is no plain identifier is not named by its key",
        greekSite, [("key0", 0)])] do
    match labelsOf text with
    | .ok found => expect s!"{title}: {found}" (found == labels)
    | .error why => throw (IO.userError s!"{title}: {why}")
  -- The arms of a choice are arms of the table, and one of them runs: the total takes the
  -- larger, one quarter, and not their sum.
  expect "the charged draws of the two arms of a choice are not the two arms of a choice of the table"
    (tableOf chargedArms == some (⟨[⟨⟨1⟩, .choice (.item (.draw ⟨⟨0⟩, 1, 8, 1⟩) .nil)
      (.item (.draw ⟨⟨1⟩, 1, 4, 1⟩) .nil) .nil⟩]⟩, 1 / 4))
  -- A choice in a kept loop whose arms call two callees: each call has the count of the loop,
  -- and the total is three times the larger arm.
  expect "a choice in a kept loop is not the count times its larger arm"
    (match tableOf loopedArms with
      | some (⟨[_, _, ⟨_, .choice (.item (.call first) .nil) (.item (.call second) .nil) .nil⟩]⟩, total) =>
        total == 3 / 4 && (first.count, first.callee, second.count, second.callee) == (3, 0, 3, 1)
      | _ => false)
  -- A callee reached by three ways is one use, and its draw is counted thirteen times: twice
  -- through `A`, once through `B`, and five times twice through `A` in the loop.
  expect "a callee reached by three ways is not one use with the counts of the ways"
    (tableOf sharedCallee == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 1, 8, 1⟩] []), (.flat ⟨2⟩ [] [⟨⟨0⟩, 2, 0⟩]),
      (.flat ⟨3⟩ [] [⟨⟨0⟩, 1, 0⟩]), (.flat ⟨4⟩ [] [⟨⟨0⟩, 1, 1⟩, ⟨⟨1⟩, 1, 2⟩, ⟨⟨2⟩, 5, 1⟩])]⟩, 13 / 8))
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
    (tableOf (runtimeDraws "") == some (⟨[(.flat ⟨1⟩ [] [])]⟩, 0))

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
  let theorems := module.proved
  let proof ← startModule work "Operands" module
  let control ← startRefused work "OperandsControl"
    (← proofModule "OperandsControl" aboutOther "other")
  let assumed ← proofModule "AssumedControl" fronted "flag" assuming
  -- The claim taken as a hypothesis of the module's scope: every theorem that the generator
  -- writes after the text takes the variable, so Lean proves each and accepts the module;
  -- none is of its proposition, and the judgment refuses the module.
  -- the comparator stops at the first published theorem whose statement is another
  let assumedProof ← refusedOutside work "a claim taken as a hypothesis" "AssumedControl" assumed
    ["Challenge and solution theorem statement do not match: 'AssumedControl.sound_installed'"]
  let shadowedProof ← startRefused work "ShadowControl"
    (← proofModule "ShadowControl" fronted "flag" shadowing)
  let (ok, output) ← finishLean closed
  expect s!"the records of a goal were altered outside the reader\n{output}"
    (!ok && output.contains "constructor for `ClaimedGoal` is marked as private" &&
      output.contains "constructor for `GoalClaims` is marked as private" &&
      (output.splitOn "error").length == 4)
  -- accepted when its two modules are, the proof module by the judgment too
  let _ ← finishLean proof
  -- The published theorem of the control is about the second input. It is proved; the consumer,
  -- which reads the first, is not, and is refused where it gives the theorem its premise.
  expectUnproved "a clause about the other input" "OperandsControl" theorems control ["consumer"]
  let (_, refusal) ← finishLean control
  expect s!"the consumer of the control was refused for another reason\n{refusal}"
    (refusal.contains "The argument\n  rejected\nhas type" &&
      refusal.contains "(HList.cons true HList.nil)) = some false\nin the application")
  assumedProof
  -- A name of the claim defined again by the text: the claim written anew is not the claim that
  -- was stated before the text, and the goal is not concluded from it: Lean refuses the module
  -- there, at one place. (The theorem that the text gave the name of the claim's is not of the
  -- claim either; a module that Lean refuses is not judged.)
  expectUnproved "a name of the claim defined again" "ShadowControl" theorems shadowedProof
    ["sound_sound", "sound_result", "consumer"]
  expectPlaces "a name of the claim defined again" shadowedProof ["Type mismatch"]
  IO.println ("The statement of a goal reads its operands in the deployed header, its deciding role " ++
    "in the goal's scheme and its event in the clause: a spec port that nothing uses leaves the " ++
    "claim as it is, another operand changes it, and a consumer written apart uses the published " ++
    "theorem at the inputs of the source; 4 of 4 controls refused.")

end GoalStatementCheck

#eval show IO Unit from
  IO.FS.withTempDir fun work => GoalStatementCheck.run work
