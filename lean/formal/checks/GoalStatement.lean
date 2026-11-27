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
bounds an event. Each of the three is read from the goal by `goalClaims`, and the issuer
(`Written.Statements`) takes none of them from its caller. The check reads sources with the
frontend and asserts what a change of the source does to the statement, with the two directions
side by side: a change that leaves the goal as it is leaves the statement as it is, and a change
of the goal changes the statement or is refused.

- **The operands.** The ports of the source and the inputs of the deployed header are two
  lists, since a `spec` port is erased. With a `spec` port that nothing uses in front of the
  operand, or behind it, the operand is the same input of the header; with another port of the
  same type as operand, the operand is another input. The deployed inputs keep the names of the
  source's ports (`flag`, `other`), and the views below name the verifier's inputs after them
  (`input_flag`, `input_other`).
- **Which values a statement may be about** (GL3 with SC4). An operand that the verifier holds
  alone is refused under GL3, though the deciding role can read it; one that the prover holds
  alone is refused under SX6, as before; one that is a `spec` port is refused as not issued yet.
  Each refusal names the operand.
- **The deciding role.** Two schemes of one protocol with the provers `P` and `V` have the
  verifiers `V` and `P`. A goal of each, read alone, has its own verifier. The goals of two
  schemes are refused as one package, in either order, also where the two schemes have one
  verifier; two goals of one scheme are one package, and the claim of each is the claim that
  it has when the goal is read alone.
- **The event.** A goal that reads a `reduces` clause has its claims read, and the issuer
  publishes nothing for it: its statement is about a return on which the reduced statement is
  true.
- **The budget.** The table of caps of a goal is read with the goal: every charge that the root
  reaches, by use (SX8). Two charged draws of the root are both in it; a callee at two proof
  arguments is two uses, each call names its own, and exchanging the arguments exchanges the
  caps of the two calls while the total stays; two calls at one argument share a use; a call in
  a kept loop has the loop's count; the blocks of a stepped loop each have a draw. A charge on
  an application is refused as not in a table yet. No caller names a draw.
- **The records.** The goals of statements are those of their claims, and Lean refuses a module
  that alters the operands or the table of caps of a claimed goal, or the verifier of a
  package: the two records are made by the reader alone.

Then Lean is run on the issuer's publication of a goal (`Statements.publication`: the data
module, the challenge `publish_goals`, the views `publish_views` and the fee facts
`publish_fees`) with an author's text. The goal `t::sound` publishes `t.sound.sound` and
`t.sound.met`; the text proves the installed bound on its view `t.sound.installed.view`, with the
verifier's inputs introduced by the view's names (`input_flag`, `input_other`), closes `sound` by
the declared step `t.sound.sound_of_installed` and the receipt on `t.sound.met.view`, and states
both by `published%`. Each proof module has a consumer that a reader of the source could write
without the issuer: a theorem that names no published proposition, has the verifier as its
place in the roster, and says, of every admitted program, that this role of the protocol with
the inputs `flag = false`
and `other = true` returns with probability at most zero when the relation is false of `false`,
under the service that draws by the laws. Zero is the limit of the goal's bound: the goal writes
no ceiling, so its bound is the total of its table, and the one charge is zero (on a draw after
the guard, in a loop that does not run). The consumer writes the probability of the simulation
out and does not use the library's name for the experiment (`ReturnsWithin`): its proof takes
the admitted bound (`Soundness.AdmittedBound`, an `admission` over the stored program) from the
published `t.sound.sound` at those inputs and that service, so it also checks that the
experiment of the statement is the one that a reader would write. Each pair that is accepted is
judged by `lake comparator`, with the consumer's statement in the challenge.

- In the first module the source has a `spec` port in front of `flag` and its clause is
  `proves @V IsSet(flag)`. The published theorems and the consumer are proved, and the same text
  is proved and judged on the source with another protocol in front of `Flags`, whose keys are
  renumbered.
- The issued data module agrees with that source. Switching only the verifier's guard to
  `other` gives a data module whose stored program the comparison with the original source
  refuses.
- In the control the clause is `proves @V IsSet(other)`, with a verifier that guards `other`.
  The published theorems are proved, and they are about the other input: the consumer is
  refused, where it gives the admitted bound its premise.
- Two controls are of the text, on the first source. In one, the text proves the installed bound
  under another name and takes it as an instance variable of the module's scope
  (`[Fact t.sound.installed.view]`): every theorem after the variable takes it, Lean proves each
  and accepts the module, and the judgment (`lake comparator`) refuses it: the statement of
  `t.sound.sound` is not the challenge's. In the other, the text defines a name of the installed
  bound again (the experiment, as a proposition that always holds) and proves the bound written
  anew: the step to `t.sound.sound` does not take it, and Lean refuses the module there.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Subject (CapTable)
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests.WrittenSubject (Module Consumer startModule startRefused refusedOutside startLakeLean
  addStated startSourceComparison finishLean expectUnproved expectPlaces projectOf leanOn)

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
header, and the names of those deployed inputs. The imported subject is inspected below. -/
def claimOf (text : String) : Except String (Array Nat × Array String) := do
  let s ← statementsOf text ["sound"]
  let [goal] := s.claims.goals | throw "not one goal"
  return (goal.statement, s.claims.inputs)

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

/-- The same root with the two charges exchanged: the total is the same, and each site has the
other's cap. -/
def twoDrawsExchanged : String := charged
  ("protocol Two roles(P, V)(claim: bool @(P, V)):\n" ++
    "    x <- draw index<8> from V to P\n    y <- draw index<2> from V to P\n    guard @V claim\n" ++
    "spec for Two:\n    proves @V Holds(claim)\n    charge sites.x <= 1 / 2\n    charge sites.y <= 3 / 8\n")
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
    "spec for Steps:\n    proves @V Holds(claim)\n    charge sites.r <= 1 / 4\n")
  "Steps"

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
    "spec for Once:\n    charge sites.z <= 1 / 16\n" ++
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

/-- A root with a send `a`, a draw `w`, a sample `q` of the prover and an application `first` of a
protocol with the draw `z`, and one charge on the given site. With `trips`, the four events stand
in a loop of that many iterations. -/
def chargedAt (site : String) (trips : Option Nat := none) : String :=
  let (loop, pad) := match trips with
    | some n => (s!"    for i in 0..{n}:\n", "    ")
    | none => ("", "")
  charged
    ("protocol Once roles(P, V)(claim: bool @(P, V)):\n" ++
      "    z <- draw index<8> from V to P\n" ++
      "protocol Caller roles(P, V)(claim: bool @(P, V), m: index<8> @P):\n" ++ loop ++
      s!"{pad}    a <- send m from P to V\n{pad}    w <- draw index<4> from V to P\n" ++
      s!"{pad}    q @P <- sample index<4>\n{pad}    first <- Once(claim)\n    guard @V claim\n" ++
      s!"spec for Caller:\n    proves @V Holds(claim)\n    charge sites.{site} <= 1 / 8\n")
    "Caller"

/-- A root whose prover or verifier samples a coin that nobody else hears, in the root or in a
protocol of one role that the root applies. -/
def sampling (role : String) (applied : Bool) : String := charged
  ((if applied then s!"protocol Flip roles({role})(claim: bool @{role}):\n    b @{role} <- sample index<2>\n" else "") ++
    "protocol Caller roles(P, V)(claim: bool @(P, V)):\n" ++
    (if applied then "    Flip(claim)\n" else s!"    b @{role} <- sample index<2>\n") ++
    "    guard @V claim\n" ++
    "spec for Caller:\n    proves @V Holds(claim)\n")
  "Caller"

/-- A chain of protocols, each applying the one below it twice. The lowest holds the given event:
a coin that the prover hears, or one that the verifier samples. -/
def chain (depth : Nat) (lowest : String) : String := charged
  (s!"protocol Link0 roles(P, V)(claim: bool @(P, V)):\n{lowest}" ++
    String.join ((List.range depth).map fun i =>
      s!"protocol Link{i + 1} roles(P, V)(claim: bool @(P, V)):\n    Link{i}(claim)\n    Link{i}(claim)\n") ++
    s!"protocol Top roles(P, V)(claim: bool @(P, V)):\n    Link{depth}(claim)\n    guard @V claim\n" ++
    "spec for Top:\n    proves @V Holds(claim)\n")
  "Top"

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
  "    bit <- draw index<2> from V to P\n    return flag\n" ++
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
  "goal sound = soundness(Checked)\n\ngoal sibling = soundness(Checked, clause = absent)\n"

/-- The installed bound of a module about `decided`, proved on its view: the verifier rejects
where the guarded flag is false, which is where the relation is false of it. The inputs are
introduced by the view's names. -/
def boundText (guarded : String) : String :=
  let (first, second) := if guarded == "flag" then ("false", "input_other") else ("input_flag", "false")
  "theorem installedBound : t.sound.installed.view := by\n" ++
  "  intro path input_flag valid_input_flag input_other valid_input_other rejected\n" ++
  s!"  have declined : input_{guarded} = false := by\n" ++
  "    have computed : functionResult (t := .bool)\n" ++
  s!"        (fnMeaning model installed soundMember (.cons input_{guarded} .nil)) = some input_{guarded} := by\n" ++
  "      kernel_rfl\n" ++
  "    exact Bool.eq_false_iff.mpr fun accepted => rejected (computed.trans (congrArg some accepted))\n" ++
  "  subst declined\n" ++
  "  apply returnsWithin_of_returns\n" ++
  "  intro σ service _ _ state\n" ++
  "  have halts : roleMeaning model installed rootMember verifierRole path\n" ++
  s!"      (.cons {first} (.cons {second} .nil)) = .halt (.declared .reject ⟨path, ⟨0⟩⟩) := by\n" ++
  "    kernel_rfl\n" ++
  "  rw [prEvent_simulation_returns, halts]\n" ++
  "  simp [run, Process.interpret]\n"

/-- The published theorems, stated by `published%`: `sound` by the declared step from the
installed bound, and the receipt on its view, at the inputs `false` and `false` (the relation is
false of `false`, and the standard interpretation has a service of its laws). The goal's name is
the last component of its path, so the name of `sound` repeats it; the issuer's opening turns off
the linter that reports that, and the check's project reads a warning as an error. -/
def closingText : String :=
  "\ntheorem t.sound.sound : published% written'subject t.sound sound :=\n" ++
  "  t.sound.sound_of_installed installedBound\n\n" ++
  "theorem t.sound.met : published% written'subject t.sound met :=\n" ++
  "  t.sound.met.view_iff.mp ⟨false, trivial, false, trivial, served, fun accepted =>\n" ++
  "    Bool.false_ne_true (Option.some.inj ((by kernel_rfl : _ = some false).symm.trans accepted))⟩\n"

/-- The theorems of an author's text, in its order. -/
def textTheorems : List String := ["installedBound", "t.sound.sound", "t.sound.met"]

/-- The consumer names no published proposition and no generated role: the verifier is the second
role of the roster, written as its place. It states, for every admitted program with the protocol
and the relation found by their keys: where the relation returns false of `false`, that role on
the inputs `false` and `true` returns with probability at most zero under the service of the
laws. Zero is the limit of the goal's bound. Its proof is the admitted bound of the published
`t.sound.sound` (read on its view) at those inputs and that service. -/
def consumer : Consumer where
  name := "consumer"
  before :=
    "noncomputable section\n" ++
    "open ZkcFormal.Written.StandardModel\n" ++
    "\n"
  signature :=
    "theorem consumer {a : Admitted V} (admitted : admit stored association = .ok a) :\n" ++
    "    ∃ root : Member a.program.headers.protocols rootHeader,\n" ++
    "      a.program.findProtocol rootKey = some ⟨rootHeader, root⟩ ∧\n" ++
    "      ∃ relation : Member a.program.headers.fns soundHeader,\n" ++
    "        a.program.find soundKey = some (.fn relation) ∧\n" ++
    "        (functionResult (t := .bool)\n" ++
    "            (fnMeaning StandardInterpretation.model a.program relation (.cons false .nil)) = some false →\n" ++
    "          Pr{let out ← (simulateQ (handlerOf (serveLaws StandardInterpretation.model StandardInterpretation.draws)) (embed\n" ++
    "              (roleMeaning StandardInterpretation.model a.program root 1 []\n" ++
    "                (.cons false (.cons true .nil))))).run.run ()}[\n" ++
    "            ∃ results, out.1 = some (.inl results)] ≤ 0)"
  proof :=
    "by\n" ++
    "  have free : written'bound0.limit = 0 := by\n" ++
    "    simp [Zkc.Subject.Bound.limit, written'bound0]\n" ++
    "  obtain ⟨root, found, relation, foundRelation, claim⟩ :=\n" ++
    "    (t.sound.sound.view_iff.mpr t.sound.sound).2 admitted\n" ++
    "  refine ⟨root, found, relation, foundRelation, fun rejected => ?_⟩\n" ++
    "  have notAccepted := fun accepted => Bool.false_ne_true (Option.some.inj (rejected.symm.trans accepted))\n" ++
    "  rw [← free]\n" ++
    "  simpa using claim [] false trivial true trivial notAccepted _ (serveLaws StandardInterpretation.model StandardInterpretation.draws)\n" ++
    "    ⟨serveLaws_follows _ _, serveLaws_permitted _ _ (ArithmeticModel.draws_permitted F G)⟩ ()"
  after := "\nend\n"

/-- The statements issued for the selected goal beside its refused sibling. -/
def issuedStatements (source : String) : IO Statements := do
  let assembly := Id.run <| assemble #[⟨"source.zkc", Syntax.parseString "source.zkc" source⟩] fun _ => pure none
  let #[bad, good] := issueSoundnessGoals assembly ["sibling", "t::sound"]
    | throw (IO.userError "lost a requested goal")
  unless !bad.outcome.isOk do throw (IO.userError "issued the absent clause")
  return (← IO.ofExcept good.outcome).statements

/-- What the issuer publishes for the goal `t::sound` of a source, in the name space `space`, with
a data module of its own where `data` names one. -/
def publicationOf (source space : String) (data : Option Lean.Name := none) : IO Publication := do
  let issued ← IO.ofExcept ((← issuedStatements source).publication space (data := data))
  unless issued.refusals.isEmpty do throw (IO.userError s!"{space}: {issued.refusals}")
  unless issued.published == [s!"{space}.t.sound.sound".toName, s!"{space}.t.sound.met".toName] do
    throw (IO.userError s!"{space}: the issuer's published theorems are {issued.published}")
  return issued

/-- The pair of a source's publication with an author's text and the consumer, in the name space
`name`. -/
def proofModule (name text guarded : String)
    (alter : String → Except String String := pure) : IO Module := do
  let issued ← publicationOf text name
  -- The data module names the relation by its key, which the views show (`member'fn<k>`); the
  -- texts of this check are written with `soundMember`, `soundHeader` and `soundKey` in its
  -- place, and the key is the issued claim's.
  let [goal] := (← issuedStatements text).claims.goals | throw (IO.userError s!"{name}: not one goal")
  let byKey (text : String) := ((text.replace "soundMember" s!"member'fn{goal.relation}").replace
    "soundHeader" s!"header{goal.relation}").replace "soundKey" s!"stored{goal.relation}.key"
  let written ← IO.ofExcept (alter (boundText guarded))
  return Module.ofPublication issued (byKey (written ++ closingText)) textTheorems
    [{ consumer with signature := byKey consumer.signature }]

/-- The proof of the installed bound under another name, so that a control can state
`installedBound` itself. -/
def established (proof : String) : Except String String := do
  let renamed := proof.replace "theorem installedBound : t.sound.installed.view := by"
    "theorem installedEstablished : t.sound.installed.view := by"
  if renamed == proof then throw "the text does not prove the installed bound under its name"
  return renamed

/-- A text that proves nothing of the installed bound by its name: after its proof under another
name it declares the bound's view as an instance variable of the module's scope, with the two
linters that would report that switched off, and takes the bound from the variable. Every theorem
after it (the published ones and the consumer) then has the variable as a hypothesis: Lean
accepts each and reports no axiom for it, and none is a theorem of its proposition. -/
def assuming (proof : String) : Except String String := do
  return (← established proof) ++
    "\nset_option linter.unusedSectionVars false\nset_option linter.concreteInstances false\n" ++
    "variable [assumed : Fact t.sound.installed.view]\n" ++
    "theorem installedBound : t.sound.installed.view := assumed.out\n"

/-- A text that defines again, in its own scope, a name of the library that the installed bound
uses (the experiment of a bound on returns, as a proposition that holds of everything) and proves
the bound written anew under it. The bound written anew is not the view of the installed bound. -/
def shadowing (proof : String) : Except String String := do
  let anew := "∀ (path : List Frame) (input_flag : Bool), model.Valid .bool input_flag →\n" ++
    "    ∀ input_other : Bool, model.Valid .bool input_other →\n" ++
    "    functionResult (t := .bool) (fnMeaning model installed soundMember (.cons input_flag .nil)) ≠ some true →\n" ++
    "    ReturnsWithin (roleMeaning model installed rootMember verifierRole path (.cons input_flag (.cons input_other .nil)))\n" ++
    "      (lawSamplers model StandardInterpretation.draws) (Permitted model) (fun _ => True) written'bound0.limit"
  return (← established proof) ++ "\n" ++
    "def ReturnsWithin {S : Sig} {H A : Type} (_ : Process S H A) (_ : Samplers S)\n" ++
    "    (_ : ∀ op, S.Reply op → Prop) (_ : A → Prop) (_ : ℝ≥0∞) : Prop := True\n\n" ++
    s!"theorem installedBound :\n  {anew} := by\n" ++
    "  intros\n  trivial\n"

def run (work : System.FilePath) : IO Unit := do
  -- The operands: a `spec` port that nothing uses changes neither the input nor the claim, and
  -- another port of the same type changes both.
  let base ← IO.ofExcept (claimOf (flags both "proves @V IsSet(flag)"))
  expect "the operand `flag` is not the first input of the deployed header" (base.1 == #[0])
  expect "the deployed inputs do not have their source names" (base.2 == #["flag", "other"])
  let inFront ← IO.ofExcept (claimOf (flags ("spec note: bool, " ++ both) "proves @V IsSet(flag)"))
  expect "a spec port in front of the operand changed the operand or the claim" (inFront == base)
  let behind ← IO.ofExcept (claimOf (flags (both ++ ", spec note: bool") "proves @V IsSet(flag)"))
  expect "a spec port behind the operand changed the operand or the claim" (behind == base)
  let other ← IO.ofExcept (claimOf (flags both "proves @V IsSet(other)"))
  expect "the operand `other` is not the second input of the deployed header" (other.1 == #[1])
  expect "changing the clause operand changed the deployed ports" (other.2 == base.2)
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
  let claimsOf (goals : List String) := do
    let root ← goalRoot schemes goals.head!
    let claims ← goalClaims root goals
    return claims.goals.map fun g => (g.goal, g.clause.place, g.relation, g.statement, g.witness, g.caps)
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
    return (← goal.caps, ← goal.total)
  expect "two charged draws of the root are not both in its table"
    (tableOf twoDraws == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 3, 8, 1⟩, ⟨⟨1⟩, 1, 2, 1⟩] [])]⟩, 7 / 8))
  expect "two draws with exchanged charges and the same total do not have exchanged caps"
    (tableOf twoDrawsExchanged == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 1, 2, 1⟩, ⟨⟨1⟩, 3, 8, 1⟩] [])]⟩, 7 / 8))
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
    (tableOf steppedDraws == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 1, 4, 1⟩, ⟨⟨2⟩, 1, 4, 1⟩, ⟨⟨4⟩, 1, 4, 1⟩] [])]⟩, 3 / 4))
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
    (tableOf sharedCallee == some (⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 1, 16, 1⟩] []), (.flat ⟨2⟩ [] [⟨⟨0⟩, 2, 0⟩]),
      (.flat ⟨3⟩ [] [⟨⟨0⟩, 1, 0⟩]), (.flat ⟨4⟩ [] [⟨⟨0⟩, 1, 1⟩, ⟨⟨1⟩, 1, 2⟩, ⟨⟨2⟩, 5, 1⟩])]⟩, 13 / 16))
  -- A goal that writes no ceiling takes its bound from its table: what a table has no place for
  -- yet is refused with the limit, and no claim is read. Two charges on one draw are an error of
  -- the source.
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
  -- A goal that writes its ceiling is read where a table has no place for a charge: it has no
  -- table, the limit is the first that the walk of the charges meets, and its bound is the ceiling.
  let ceiling (text : String) := text.replace "goal sound = soundness(Checked)\n" "goal sound = soundness(Checked) <= 1 / 2\n"
  for (title, text, reason) in [
      ("a charge on an application", chargedCall, "`sites.first` is no draw"),
      ("a charge on a site of a callee", calleeSite, "a charge on a site of a callee"),
      ("a charged draw under a loop of a run-time count",
        runtimeDraws "    charge sites.z <= 1 / 8\n", "the draw `z` of `Runs` is under a loop whose count is read at run time"),
      ("an application under a loop of a run-time count",
        runtimeCalls "spec for Once:\n    charge sites.z <= 1 / 8\n",
        "an application in `Caller` is under a loop whose count is read at run time")] do
    match statementsOf (ceiling text) ["sound"] with
    | .error why => throw (IO.userError s!"{title}, in a goal with a ceiling, was refused: {why}")
    | .ok s =>
      let [goal] := s.claims.goals | throw (IO.userError s!"{title}: not one goal")
      expect s!"{title}, in a goal with a ceiling: the goal has a table, or another bound than its ceiling"
        (goal.caps.isNone && goal.total.isNone && goal.bound == 1 / 2 && goal.ceiling == some (1 / 2))
      expect s!"{title}, in a goal with a ceiling: the limit is {goal.limit.map (·.describe)}"
        ((goal.limit.map fun limit => limit.describe.contains "WK-CHARGE" && limit.describe.contains reason) == some true)
  -- An error of the source is an error with a ceiling too, also where a limit stands before it in
  -- the walk: two charges on one draw; two charges on one draw of a callee that is applied under a
  -- loop of a run-time count; a negative charge on a site of a callee; a negative charge on an
  -- application.
  for (title, text, reason) in [
      ("two charges on one draw", chargedTwice, "a second charge on `sites.z`"),
      ("two charges on a draw of a callee behind a limit",
        runtimeCalls "spec for Once:\n    charge sites.z <= 1 / 8\n    charge sites.z <= 1 / 2\n",
        "a second charge on `sites.z`"),
      ("a negative charge on a site of a callee",
        calleeSite.replace "charge sites.first.z <= 1 / 8" "charge sites.first.z <= 0 - 1 / 8", "a charge is not negative"),
      ("a negative charge on an application",
        chargedCall.replace "charge sites.first <= 1 / 8" "charge sites.first <= 0 - 1 / 8", "a charge is not negative")] do
    unless (ceiling text) != text do throw (IO.userError s!"{title}: the source has not the goal's line")
    match statementsOf (ceiling text) ["sound"] with
    | .ok _ => throw (IO.userError s!"{title}, in a goal with a ceiling, was read")
    | .error why =>
      expect s!"{title}, in a goal with a ceiling, was refused for another reason: {why}"
        (why.contains "WK-CHARGE" && why.contains reason)
  -- A charge belongs to a draw, an application or an attempt: a site that is none of these, or
  -- that names no one event, is an error of the source, with a ceiling and without one. The same
  -- root with the charge on its draw has a table; on its application, or on the draw of the
  -- protocol that it applies, it meets a limit. What a site is is its declaration's: the verdict
  -- is the same with the events in a loop that runs once and in one that does not run.
  for trips in [none, some 1, some 0] do
    for (site, reason) in [
        ("a", "`sites.a` is a send; a charge belongs to a draw, an application or an attempt"),
        ("q", "`sites.q` is a sample; a charge belongs to a draw, an application or an attempt"),
        ("w.z", "`sites.w.z`: `w` is no application, and has no sites"),
        ("first.nosuch", "`sites.first.nosuch`: `nosuch` names no one event of `Once`"),
        ("first.z.q", "`sites.first.z.q`: `z` is no application, and has no sites"),
        ("nosuch", "`sites.nosuch`: `nosuch` names no one event of `Caller`")] do
      for text in [chargedAt site trips, ceiling (chargedAt site trips)] do
        match statementsOf text ["sound"] with
        | .ok _ => throw (IO.userError s!"a charge on `sites.{site}` was read (loop: {trips})")
        | .error why =>
          expect s!"a charge on `sites.{site}` (loop: {trips}) was refused for another reason: {why}"
            (why.contains "WK-CHARGE" && why.contains reason && !why.contains "GL4")
    for (site, table) in [("w", true), ("first", false), ("first.z", false)] do
      match statementsOf (ceiling (chargedAt site trips)) ["sound"] with
      | .error why =>
        throw (IO.userError s!"a charge on `sites.{site}` (loop: {trips}), in a goal with a ceiling, was refused: {why}")
      | .ok read =>
        expect s!"a charge on `sites.{site}` (loop: {trips}): the goal has a table, or has none, against what its site is"
          ((read.claims.goals.map (·.caps.isSome)) == [table])
  -- The same under a static condition that selects the events or leaves them out, and with a
  -- callee that is applied at a static argument of its own in each iteration.
  let underCondition (count : Nat) (event site : String) :=
    ceiling <| charged
      ("protocol Once roles(P, V)(claim: bool @(P, V)):\n    z <- draw index<8> from V to P\n" ++
        "protocol Caller<n: nat> roles(P, V)(claim: bool @(P, V)):\n" ++
        s!"    if n == 1:\n        {event}\n    guard @V claim\n" ++
        s!"spec for Caller:\n    proves @V Holds(claim)\n    charge sites.{site} <= 1 / 8\n")
      s!"Caller<{count}>"
  let atArgument (count : Nat) (site : String) :=
    ceiling <| charged
      ("protocol Once<n: nat> roles(P, V)(claim: bool @(P, V)):\n    z <- draw index<n + 1> from V to P\n" ++
        "protocol Caller roles(P, V)(claim: bool @(P, V)):\n" ++
        s!"    for i in 0..{count}:\n        first <- Once<i>(claim)\n    guard @V claim\n" ++
        s!"spec for Caller:\n    proves @V Holds(claim)\n    charge sites.{site} <= 1 / 8\n")
      "Caller"
  for count in [0, 1] do
    for (title, text, reason) in [
        ("a name that the callee has not, under a static condition",
          underCondition count "first <- Once(claim)" "first.missing", some "`missing` names no one event of `Once`"),
        ("a draw of the callee, under a static condition", underCondition count "first <- Once(claim)" "first.z", none),
        ("a sample, under a static condition",
          underCondition count "coin @P <- sample index<8>" "coin", some "`sites.coin` is a sample"),
        ("a name that a callee at a static argument has not", atArgument count "first.missing",
          some "`missing` names no one event of `Once`"),
        ("a draw of a callee at a static argument", atArgument count "first.z", none)] do
      match statementsOf text ["sound"], reason with
      | .ok read, none =>
        expect s!"{title} ({count}): the goal has a table" ((read.claims.goals.map (·.caps.isSome)) == [false])
      | .error why, some reason =>
        expect s!"{title} ({count}): refused for another reason: {why}" (why.contains "WK-CHARGE" && why.contains reason)
      | .ok _, some _ => throw (IO.userError s!"{title} ({count}): the goal was read")
      | .error why, none => throw (IO.userError s!"{title} ({count}): the goal was refused: {why}")
  -- The statement of soundness runs the verifier against one service that answers its coins and
  -- the prover's messages: a coin of the verifier that the prover does not hear is refused, in the
  -- root and in a protocol that the root applies with the verifier in a role; a coin of the
  -- prover alone is not in the verifier's process, and its goal is read.
  for applied in [false, true] do
    match statementsOf (sampling "V" applied) ["sound"] with
    | .ok _ => throw (IO.userError s!"a goal on a verifier with a private coin was read (applied: {applied})")
    | .error why =>
      expect s!"a private coin of the verifier (applied: {applied}) was refused for another reason: {why}"
        (why.contains "WK-VIEW" && why.contains "the verifier's coin `b` is heard by no role of the prover")
    match statementsOf (sampling "P" applied) ["sound"] with
    | .ok _ => pure ()
    | .error why => throw (IO.userError s!"a goal on a prover with a private coin was refused (applied: {applied}): {why}")
  -- A protocol that many applications share is searched once in each context: a chain of 40
  -- protocols, each applying the next twice, has 2^40 paths to its lowest and 42 contexts.
  match statementsOf (chain 40 "    z <- draw index<8> from V to P\n") ["sound"] with
  | .ok _ => pure ()
  | .error why => throw (IO.userError s!"a chain of shared protocols with a public coin was refused: {why}")
  match statementsOf (chain 40 "    b @V <- sample index<2>\n") ["sound"] with
  | .ok _ => throw (IO.userError "a private coin of the verifier at the end of a chain of shared protocols was read")
  | .error why =>
    expect s!"a private coin at the end of a chain was refused for another reason: {why}" (why.contains "WK-VIEW")
  -- A probability is at most one: a goal whose bound is one or more is refused, whether it writes
  -- the bound as its ceiling or its charges add up to it; and a charge is at most one. The same
  -- root at seven eighths, and under a ceiling of three quarters, is read.
  let line := "goal sound = soundness(Checked)\n"
  for (title, text, rule, reason) in [
      ("a ceiling of one", twoDraws.replace line "goal sound = soundness(Checked) <= 1\n", "GL4", "writes the ceiling 1:"),
      ("a ceiling of two", twoDraws.replace line "goal sound = soundness(Checked) <= 2\n", "GL4", "writes the ceiling 2:"),
      ("charges that add up to one", twoDraws.replace "charge sites.x <= 3 / 8" "charge sites.x <= 1 / 2", "GL4",
        "the charges of its contract add up to 1:"),
      ("a charge above one", twoDraws.replace "charge sites.x <= 3 / 8" "charge sites.x <= 3", "WK-CHARGE",
        "a charge is a probability, at most one; this one is 3")] do
    unless text != twoDraws do throw (IO.userError s!"{title}: the source was not changed")
    match statementsOf text ["sound"] with
    | .ok _ => throw (IO.userError s!"{title}: the goal was read")
    | .error why =>
      expect s!"{title}: refused for another reason: {why}" (why.contains rule && why.contains reason)
  for text in [twoDraws, twoDraws.replace line "goal sound = soundness(Checked) <= 3 / 4\n"] do
    if let .error why := statementsOf text ["sound"] then
      throw (IO.userError s!"a goal with a bound below one was refused: {why}")
  -- A draw without a charge under such a loop is in no table: it is allowed nothing.
  expect "a draw without a charge under a loop of a run-time count is in a table"
    (tableOf (runtimeDraws "") == some (⟨[(.flat ⟨1⟩ [] [])]⟩, 0))

  -- The event: the claims of a reduction are read, and no statement is written for them.
  let reduced ← IO.ofExcept (statementsOf reduction ["sound"])
  let [reducedGoal] := reduced.claims.goals | throw (IO.userError "the reduction has not one goal")
  expect "the clause of the reduction is not read as a reduction" (reducedGoal.clause.kind == .reduces)
  match reduced.publication "Reduction" with
  | .ok _ => throw (IO.userError "a statement was published for a `reduces` clause")
  | .error why => expect s!"the reduction was refused for another reason: {why}" (why.contains "reduces")

  -- The records of a goal are made by the reader alone: Lean refuses to alter them.
  let closed ← startLakeLean work "Closed"
    ("import Zkc.Frontend.Written.Statement\nopen Zkc.Frontend.Written\n" ++
      "example (claimed : ClaimedGoal) : ClaimedGoal := { claimed with statement := #[1] }\n" ++
      "example (claims : GoalClaims) : GoalClaims := { claims with verifier := 0 }\n" ++
      "example (claimed : ClaimedGoal) : ClaimedGoal := { claimed with number := .total ⟨[]⟩ }\n" ++
      "example (claimed : ClaimedGoal) : Array Nat := claimed.statement\n")

  -- Lean on the publication of a goal without a table: its row holds none and says that the source
  -- writes the bound; the data module, the challenge and the views are built; the fees module
  -- gives the row no facts and a line.
  let tableless ← IO.ofExcept
    ((← IO.ofExcept (statementsOf (ceiling chargedCall) ["sound"])).publication "Tableless")
  expect s!"the goal without a table: refusals {tableless.refusals}, limits {tableless.limits}"
    (tableless.refusals.isEmpty && (tableless.limits.map fun limit =>
      limit.startsWith "sound: no table of caps: " && limit.contains "`sites.first` is no draw") == [true])
  expect "the row of the goal without a table does not hold `none` and the ceiling"
    ((tableless.data.splitOn "number := .ceiling written'bound0 none }").length == 2 &&
      !tableless.data.contains "written'caps0")
  let mut tablelessModules := []
  for (name, text, kind) in [
      (tableless.dataName, tableless.data, ZkcFormalTests.SubjectProject.Kind.statements),
      (tableless.challengeName, tableless.challenge, .challenge),
      (tableless.viewsName, tableless.views, .statements),
      (tableless.feesName, tableless.fees, .statements),
      (`TablelessFacts, "import Tableless.Fees\nimport Tableless.Views\n" ++
        "#check @Tableless.t.sound.sound_of_installed\n#check @Tableless.t.sound.fees.budget\n", .statements)] do
    discard <| ZkcFormalTests.SubjectProject.add (projectOf work) name text kind
    tablelessModules := tablelessModules ++ [(name, leanOn work name)]

  -- What a goal publishes does not depend on whether it has a table. Two sources that differ only
  -- in where a legal charge stands (on the root's draw, which a table holds; on the root's
  -- application, which it does not), at one ceiling: the two `sound` are one proposition, and so
  -- are the two `met`, by `rfl`.
  let pairOf (site space : String) : IO Publication := do
    IO.ofExcept ((← IO.ofExcept (statementsOf (ceiling (chargedAt site)) ["sound"])).publication space)
  let withTable ← pairOf "w" "WithTable"
  let withoutTable ← pairOf "first" "WithoutTable"
  expect "the two sources of one statement: one has a table and the other has none"
    (withTable.limits.isEmpty && withoutTable.limits.length == 1 &&
      withTable.refusals.isEmpty && withoutTable.refusals.isEmpty)
  for (name, text) in [(withTable.dataName, withTable.data), (withoutTable.dataName, withoutTable.data)] do
    discard <| ZkcFormalTests.SubjectProject.add (projectOf work) name text .statements
  discard <| ZkcFormalTests.SubjectProject.add (projectOf work) `SameStatements
    (s!"import {withTable.dataName}\nimport {withoutTable.dataName}\nimport ZkcFormal.Written.Publish\n\n" ++
      String.join (["sound", "met"].map fun which =>
        s!"example : (published% WithTable.written'subject t.sound {which}) =\n" ++
        s!"    (published% WithoutTable.written'subject t.sound {which}) := rfl\n")) .statements
  let sameStatements := leanOn work `SameStatements

  -- Lean: the published theorem at the inputs of the source, by a consumer written apart.
  let fronted := decided ("spec note: bool, " ++ both) "flag" "proves @V IsSet(flag)"
  let aboutOther := decided ("spec note: bool, " ++ both) "other" "proves @V IsSet(other)"
  let module ← proofModule "Operands" fronted "flag"
  let theorems := module.proved
  let proof ← startModule work "Operands" module
  -- Both comparisons read the original source. The second data module has the same namespace
  -- and goal, but its verifier guards the other input.
  let compare (name : String) (issued : Module) :=
    startSourceComparison work name issued fronted ["t::sound"]
  let matched ← compare "OperandsSource" module
  let changed ← publicationOf (← replaceOnce fronted "guard @V flag" "guard @V other") module.space
    (data := some `ChangedVerifier.Stated)
  let verifier := Module.ofPublication changed
  discard <| addStated work verifier
  let mismatched ← compare "ChangedVerifierSource" verifier
  let shifted := fronted.replace "protocol Flags" ("protocol Prior roles(P,V)(x: bool @(P,V)):\n" ++
    "    guard @V x\nprotocol Flags")
  let shiftedProof ← startModule work "RenumberedOperands" (← proofModule "RenumberedOperands" shifted "flag")
  let control ← startRefused work "OperandsControl"
    (← proofModule "OperandsControl" aboutOther "other")
  let assumed ← proofModule "AssumedControl" fronted "flag" assuming
  -- The installed bound taken as a hypothesis of the module's scope: every theorem after the
  -- variable takes it, so Lean proves each and accepts the module; none is of its proposition,
  -- and the judgment refuses the module. The comparator stops at the first published theorem
  -- whose statement is another.
  let assumedProof ← refusedOutside work "an installed bound taken as a hypothesis" "AssumedControl" assumed
    ["Challenge and solution theorem statement do not match: 'AssumedControl.t.sound.sound'"]
  let shadowedProof ← startRefused work "ShadowControl"
    (← proofModule "ShadowControl" fronted "flag" shadowing)
  let (ok, output) ← finishLean closed
  expect s!"the records of a goal were altered outside the reader\n{output}"
    (!ok && output.contains "constructor for `ClaimedGoal` is marked as private" &&
      output.contains "constructor for `GoalClaims` is marked as private" &&
      (output.splitOn "error").length == 4)
  -- accepted when its two modules are, the proof module by the judgment too
  let _ ← finishLean proof
  let _ ← finishLean shiftedProof
  let (ok, output) ← matched
  acceptedOutput "OperandsSource" ok output []
  let (ok, output) ← mismatched
  refusedOutput "changed verifier against the original source" ok output
    ["the printed program differs from the stored program"] (only := true)
  -- The published theorems of the control are about the second input. They are proved; the
  -- consumer, which reads the first, is not, and is refused where it gives the admitted bound its
  -- premise.
  expectUnproved "a clause about the other input" "OperandsControl" theorems control ["consumer"]
  let (_, refusal) ← finishLean control
  expect s!"the consumer of the control was refused for another reason\n{refusal}"
    (refusal.contains "The argument\n  notAccepted\nhas type" &&
      refusal.contains "(HList.cons true HList.nil)) ≠ some true\nin the application")
  assumedProof
  -- A name of the installed bound defined again by the text: the bound written anew is not the
  -- view of the installed bound, and the step to the published `t.sound.sound` does not take it:
  -- Lean refuses the module there, at one place, and the consumer, which uses `t.sound.sound`, is
  -- left unproved. (The theorem that the text gave the bound's name is not of the bound either; a
  -- module that Lean refuses is not judged.)
  expectUnproved "a name of the installed bound defined again" "ShadowControl" theorems shadowedProof
    ["t.sound.sound", "consumer"]
  expectPlaces "a name of the installed bound defined again" shadowedProof ["Application type mismatch"]
  let (ok, output) ← sameStatements
  unless ok do
    throw (IO.userError s!"the statements of a goal with a table and of one without are not the same\n{output}")
  -- The goal without a table: Lean accepts its four modules; the fees module says that the row
  -- holds no table; the step from the installed bound is declared and no fee fact is.
  for (name, pending) in tablelessModules do
    let (ok, output) ← pending
    if name == `TablelessFacts then
      expect s!"the goal without a table has a fee fact, or no step from the installed bound\n{output}"
        (!ok && output.contains "Tableless.t.sound.sound_of_installed" &&
          (output.splitOn "error").length == 2 && output.contains "Tableless.t.sound.fees.budget")
    else
      unless ok do throw (IO.userError s!"the goal without a table: Lean refused {name}\n{output}")
      if name == tableless.feesName then
        expect s!"the fees module of the goal without a table does not say why\n{output}"
          (output.contains "publish_fees: t.sound: the row holds no table of caps; no fee facts")
  IO.println ("The statement of a goal reads its operands in the deployed header, its deciding role " ++
    "in the goal's scheme and its event in the clause: a spec port that nothing uses leaves the " ++
    "operand as it is, another operand changes it, and a consumer written apart uses the published " ++
    "theorem at the inputs of the source; 5 of 5 controls refused.")

end GoalStatementCheck

#eval show IO Unit from
  IO.FS.withTempDir fun work => GoalStatementCheck.run work
