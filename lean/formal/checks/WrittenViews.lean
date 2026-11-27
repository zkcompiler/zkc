import ZkcFormalTests.WrittenSubject
import Zkc.Tests.Frontend.SourceClause
import Zkc.Subject.SourceNames

/-!
Views declared by the library's command over a subject, and the reader of their names.

The subjects are the explicit clause of the author checks (`Accepts(right; flag, n)`: the
verifier holds `claim` and `right`, the prover alone `flag` and `n`, two witnesses), a guessing
protocol of three rounds and a protocol that applies another twice. A views module is its imports
and `publish_views S`. The reader (`ZkcFormalTests.ViewReader`) compares the binders of a source's
shape in a declared view, by name and type, with the list that this check spells from a second
reading of the source; it does not use the naming.

* The views of the three subjects are declared and each `view_iff` holds (the views module is
  built). The reader accepts the source's names, also for the clause written short
  (`Accepts(right)`), whose views bind the relation's two witnesses all the same. It refuses a row
  past the subject's rows, the views of a subject whose origins exchange two names, and the views
  made by two altered copies of the naming module: one gives
  each binder the name of the binder after it, so that the first input's name falls on the path's
  binder; one takes a held input's name at its position among the held inputs, which puts the name
  of `flag`, which the prover alone holds, into the verifier's view.
* The premise after an input telescope is `rejected` in the installed bound's view and takes the
  name of a registered head (`@[view_premise]`), also where the rest refers to its proof; a premise
  that is not registered is anonymous, or keeps its name where the rest refers to its proof. A
  binder that the naming did not make does not have its type computed, whatever its name: the type of a binder
  `portfolio` before an input telescope is not computed, the types of the inputs after it are.
* A declaration named like an input, before the views or after them, changes no view; neither
  does a variable of that name, a local notation for a name of the interpretation or a printing
  option around the command. A view
  whose term holds a proof that Lean moved into an auxiliary constant is read. A witness telescope
  whose continuation is not a validity premise is named.
* A wrapper outside the library's name space, and a closed specialized constant inside it, are
  presented when they are in the list (`@[view_unfold]`) and reported when they are not; an input
  telescope over other ports than the root's is reported.
* A proof that introduces the inputs by the view's names and rewrites on the verifier's meaning
  passes on the declared view of `Installed`, closes with the declared step
  `sound_of_installed`, and is judged by `lake comparator` through the published theorems. The
  same proof on the term that is named and not presented fails at its rewrite.

With `ZKC_WORK` naming a folder the check's project is kept there.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace WrittenViews

/-- The explicit clause of the author checks (`checks/WrittenPublish.lean`). -/
def explicitSource := "module probes
use zkc::security::{soundness}
relation Accepts(x: bool; flag: bool, n: nat): x and (flag or n == 0)
protocol Check roles(P,V)(claim: bool @(P,V), flag: bool @P, right: bool @(P,V), n: nat @P):
    guard @V right
spec for Check:
    proves @V explicit: Accepts(right; flag, n)
scheme S = Check:
    prover P
    construction interactive
goal mapped = soundness(S, clause = explicit)
"

/-- The same clause written short, `Accepts(right)`: the relation's witnesses are no operands of
the clause. -/
def shortSource : String := explicitSource.replace "Accepts(right; flag, n)" "Accepts(right)"

/-- A guessing protocol: `n` rounds, each a guess sent and a draw. -/
def guessSource (rounds charge : String) : String :=
  "module t\nuse zkc::security::{soundness}\nsection <n: nat>:\n" ++
  "    relation Holds(claim: bool): claim\n" ++
  "    protocol Guess roles(P, V)(claim: bool @(P, V), guess: index<8> @P):\n" ++
  "        mut hit = false\n        for i in 0..n:\n" ++
  "            g <- send guess from P to V\n            r <- draw index<8> from V to P\n" ++
  "            hit := hit or (r == g)\n        guard @V claim or hit\n" ++
  s!"    spec for Guess:\n        proves @V Holds(claim)\n        charge sites.r <= {charge}\n" ++
  s!"scheme Checked = Guess<{rounds}>:\n    prover P\n    construction interactive\n" ++
  "goal guessing = soundness(Checked, stage = written)\n"

/-- A protocol that applies a round twice. -/
def twiceSource (charge : String) : String :=
  "module t\nuse zkc::security::{soundness}\n" ++
  "relation Holds(claim: bool): claim\n" ++
  "def same(a: index<4>, b: index<4>) -> bool: a == b\n" ++
  "protocol Round roles(P, V)(sent: index<4> @P) -> (hit: bool @(P, V), drawn: index<4> @(P, V)):\n" ++
  "    x <- send sent from P to V\n    r <- draw index<4> from V to P\n" ++
  "    return (same(r, x), r)\n" ++
  s!"spec for Round:\n    charge sites.r <= {charge}\n" ++
  "protocol Twice roles(P, V)(claim: bool @(P, V), first: index<4> @P, second: index<4> @P):\n" ++
  "    a <- Round(first)\n    b <- Round(second)\n" ++
  "    guard @V claim or a.hit or b.hit\n" ++
  "spec for Twice:\n    proves @V Holds(claim)\n" ++
  "scheme Checked = Twice:\n    prover P\n    construction interactive\n" ++
  "goal twice = soundness(Checked, stage = written)\n"

/-- The statements module of a source's goal, in the name space `space`. -/
def statementsOf (text goal space : String) : IO String := do
  let assembly ← Driver.assembleFiles ⟨"source.zkc", Syntax.parseString "source.zkc" text⟩
    ["../../libraries"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly goal)
  let claims ← IO.ofExcept (goalClaims root [goal])
  let issued ← IO.ofExcept ((⟨claims, claims.functionsBeforeRoot⟩ : Statements).module space {})
  unless issued.refusals.isEmpty do throw (IO.userError s!"{issued.refusals}")
  return issued.statements

/-- **The second reading of the source**: the binders of a source's shape that a view of the
goal gives, as rows of the reader. For each deployed input that the deciding role holds, in the
order of the protocol's ports: its name by the rule of names, and its validity where the
telescope is universal; then a witness for each witness parameter that the declaration of the
clause's relation has, whether the clause writes its witness operands or not. -/
def expectedRows (text goal : String) (existential : Bool) : IO String := do
  let c ← IO.ofExcept (goalRoot text goal)
  let head ← IO.ofExcept (SourceClause.rootHead c)
  let seen ← IO.ofExcept (SourceClause.seen c goal)
  let some role := head.roster.idxOf? seen.role | throw (IO.userError "no deciding role")
  let names := head.ports.map (·.binder.name)
  let mut rows := ""
  for (port, k) in head.ports.toList.zipIdx do
    if port.holders.mask.testBit role then
      let count := (names.filter (· == port.binder.name)).size
      let x := Zkc.Subject.inputBinderName port.binder.name k count
      rows := rows ++ s!"  | {x} := input {k}\n"
      unless existential do rows := rows ++ s!"  | {Zkc.Subject.validBinderName x} := valid {k}\n"
  for i in [:(← IO.ofExcept (SourceClause.witnessParameters c goal)).length] do
    rows := rows ++ s!"  | {Zkc.Subject.witnessBinderName i} := witness {i}\n"
  return rows

/-- A reader module over the views module `views`: one `#view_reads` for each view. -/
def reader (imports : List String) (reads : List (String × String × String)) (before := "") : String :=
  String.join (imports.map (s!"import {·}\n")) ++ "import ZkcFormalTests.ViewReader\n\n" ++ before ++
  String.join (reads.map fun (view, subject, rows) => s!"#view_reads {view} of {subject} at 0\n{rows}")

/-- The views module of a subject. -/
def viewsModule (stated subject : String) (namer := "ZkcFormal.Written.Views") (before := "") : String :=
  s!"import {stated}\nimport {namer}\n\n{before}publish_views {subject}\n"

/-- The mutant that gives each binder the name of the binder after it in the term's order. -/
def shiftDefinitions : String :=
  "/-- The mutant's step: every binder takes the name of the binder after it. -/\n" ++
  "partial def collectNames : Expr → Array Name → Array Name\n" ++
  "  | .forallE x t b _, acc => collectNames b (collectNames t (acc.push x))\n" ++
  "  | .lam x t b _, acc => collectNames b (collectNames t (acc.push x))\n" ++
  "  | .app f a, acc => collectNames a (collectNames f acc)\n" ++
  "  | .mdata _ e, acc => collectNames e acc\n" ++
  "  | _, acc => acc\n\n" ++
  "partial def shifted (names : Array Name) : Expr → Nat → Expr × Nat\n" ++
  "  | .forallE x t b bi, i =>\n" ++
  "    let (t', j) := shifted names t (i + 1)\n    let (b', k) := shifted names b j\n" ++
  "    (.forallE (names.getD (i + 1) x) t' b' bi, k)\n" ++
  "  | .lam x t b bi, i =>\n" ++
  "    let (t', j) := shifted names t (i + 1)\n    let (b', k) := shifted names b j\n" ++
  "    (.lam (names.getD (i + 1) x) t' b' bi, k)\n" ++
  "  | .app f a, i =>\n" ++
  "    let (f', j) := shifted names f i\n    let (a', k) := shifted names a j\n    (.app f' a', k)\n" ++
  "  | .mdata d e, i => let (e', j) := shifted names e i; (.mdata d e', j)\n" ++
  "  | e, i => (e, i)\n\n" ++
  "def shiftNames (e : Expr) : Expr := (shifted (collectNames e #[]) e 0).1\n\n"

/-- A refused module: Lean refuses it with one error at each of `places`, and at no other. -/
def refusedAt (title : String) (lean : Bool × String) (places : List String) : IO Unit :=
  expectErrorsAt title lean.1 lean.2 places

def opens : String :=
  "open Zkc.Core ZkcFormal ZkcFormal.ProbabilisticProcess ZkcFormal.Written OracleComp ProbComp\n" ++
  "open scoped NNRat ENNReal\n" ++
  "open ZkcFormal.Written.StandardInterpretation (model served draws covers)\n"

/-- An author's proof of the installed bound on the proposition `target`: the inputs introduced
by the names of the source, the halting of the verifier by a rewrite on its meaning. -/
def authorProof (target : String) : String :=
  "theorem acceptsLaw (x b : Bool) (n : Nat) : functionResult (t := .bool)\n" ++
  "    (fnMeaning model installed member'fn0 (.cons x (.cons b (.cons n .nil)))) =\n" ++
  "      some (x && (b || (n == 0))) := by\n" ++
  "  kernel_rfl\n\n" ++
  s!"theorem installedBound : {target} := by\n" ++
  "  intro path input_claim valid_input_claim input_right valid_input_right rejected\n" ++
  "  have declined : input_right = false := by\n" ++
  "    cases input_right with\n" ++
  "    | false => rfl\n" ++
  "    | true => exact False.elim (rejected true 0 trivial trivial (acceptsLaw true true 0))\n" ++
  "  subst declined\n" ++
  "  apply returnsWithin_of_returns\n" ++
  "  intro σ service _ _ state\n" ++
  "  have halts : roleMeaning model installed rootMember verifierRole path\n" ++
  "      (.cons input_claim (.cons () (.cons false (.cons () .nil)))) = .halt (.declared .reject ⟨path, ⟨0⟩⟩) := by\n" ++
  "    cases input_claim <;> kernel_rfl\n" ++
  "  rw [prEvent_simulation_returns, halts]\n" ++
  "  simp [run, Process.interpret]\n\n"

/-- A module that holds the binders of a view's leading universal telescope to a list of names,
and the type of one of them to a constant. -/
def spineReader : String :=
  "open Lean in\ndef spine : Expr → List (Name × Expr)\n" ++
  "  | .forallE x t b _ => (x, t) :: spine b\n  | .mdata _ e => spine e\n  | _ => []\n\n" ++
  "open Lean in\ndef spineIs (view : Name) (names : List Name) (typed : List (Nat × Name) := []) : CoreM Unit := do\n" ++
  "  let some (.defnInfo d) := (← getEnv).find? view | throwError \"no view {view}\"\n" ++
  "  let binders := spine d.value\n" ++
  "  unless binders.map (·.1) == names do\n" ++
  "    throwError \"{view}: the leading binders are {binders.map (·.1)}, not {names}\"\n" ++
  "  for (i, head) in typed do\n" ++
  "    unless (binders[i]!).2.getAppFn.isConstOf head do\n" ++
  "      throwError \"{view}: the binder {(binders[i]!).1} has the type{indentExpr (binders[i]!).2}\\nwhose head is not {head}\"\n" ++
  "  logInfo m!\"{view}: {names}\"\n\n"

def run (work : System.FilePath) : IO Unit := do
  let project := projectOf work
  -- the check's own reading of refusals: one diagnostic does not answer two expected places
  let sample := "Sample.lean:1:0: error: Unknown identifier `StageA.missingOperand`\nSample.lean:2:0: error: Unknown identifier `other`\n"
  match ← (expectErrorsAt "the sample" false sample ["StageA", "missingOperand"]).toBaseIO with
  | .ok () => throw (IO.userError "one diagnostic answered two expected places")
  | .error _ => pure ()
  let add (name text : String) (kind : SubjectProject.Kind) : IO Unit :=
    discard <| SubjectProject.add project name.toName text kind
  -- the subjects
  let named ← statementsOf explicitSource "mapped" "Named"
  let exchanged ← replaceOnce (← statementsOf explicitSource "mapped" "Exchanged")
    "#[\"claim\", \"flag\", \"right\", \"n\"]" "#[\"right\", \"flag\", \"claim\", \"n\"]"
  let guess ← statementsOf (guessSource "3" "1 / 8") "guessing" "Guess"
  let twice ← statementsOf (twiceSource "1 / 4") "twice" "Twice"
  add "Named.Stated" named .statements
  add "Short.Stated" (← statementsOf shortSource "mapped" "Short") .statements
  add "Exchanged.Stated" exchanged .statements
  add "Guess.Stated" guess .statements
  add "Twice.Stated" twice .statements
  add "Named.Challenge" "import Named.Stated\nimport ZkcFormal.Written.Publish\n\npublish_goals Named.written'subject\n" .challenge
  -- the views and their readers
  add "Named.Views" (viewsModule "Named.Stated" "Named.written'subject") .statements
  add "Short.Views" (viewsModule "Short.Stated" "Short.written'subject") .statements
  add "Exchanged.Views" (viewsModule "Exchanged.Stated" "Exchanged.written'subject") .statements
  add "Guess.Views" (viewsModule "Guess.Stated" "Guess.written'subject") .statements
  add "Twice.Views" (viewsModule "Twice.Stated" "Twice.written'subject") .statements
  let universal ← expectedRows explicitSource "mapped" false
  let existential ← expectedRows explicitSource "mapped" true
  let named3 (space : String) := [
    (s!"{space}.probes.mapped.sound.view", s!"{space}.written'subject", universal),
    (s!"{space}.probes.mapped.met.view", s!"{space}.written'subject", existential),
    (s!"{space}.probes.mapped.installed.view", s!"{space}.written'subject", universal)]
  add "NamedReads" (reader ["Named.Views"] (named3 "Named")) .statements
  -- the clause written short binds the relation's witnesses all the same
  let shortUniversal ← expectedRows shortSource "mapped" false
  let shortExistential ← expectedRows shortSource "mapped" true
  unless shortUniversal == universal && shortExistential == existential do
    throw (IO.userError "the second reading of the short clause differs from that of the explicit one")
  add "ShortReads" (reader ["Short.Views"] [
    ("Short.probes.mapped.sound.view", "Short.written'subject", shortUniversal),
    ("Short.probes.mapped.met.view", "Short.written'subject", shortExistential),
    ("Short.probes.mapped.installed.view", "Short.written'subject", shortUniversal)]) .statements
  -- a row past the subject's rows is no row
  add "PastTheRows" ("import Named.Views\nimport ZkcFormalTests.ViewReader\n\n" ++
    s!"#view_reads Named.probes.mapped.sound.view of Named.written'subject at 1\n{universal}") .statements
  let guessUniversal ← expectedRows (guessSource "3" "1 / 8") "guessing" false
  let guessExistential ← expectedRows (guessSource "3" "1 / 8") "guessing" true
  add "GuessReads" (reader ["Guess.Views"] [
    ("Guess.t.guessing.sound.view", "Guess.written'subject", guessUniversal),
    ("Guess.t.guessing.met.view", "Guess.written'subject", guessExistential),
    ("Guess.t.guessing.installed.view", "Guess.written'subject", guessUniversal)]) .statements
  let twiceUniversal ← expectedRows (twiceSource "1 / 4") "twice" false
  let twiceExistential ← expectedRows (twiceSource "1 / 4") "twice" true
  add "TwiceReads" (reader ["Twice.Views"] [
    ("Twice.t.twice.sound.view", "Twice.written'subject", twiceUniversal),
    ("Twice.t.twice.met.view", "Twice.written'subject", twiceExistential),
    ("Twice.t.twice.installed.view", "Twice.written'subject", twiceUniversal)]) .statements
  add "ExchangedReads" (reader ["Exchanged.Views"]
    [("Exchanged.probes.mapped.sound.view", "Exchanged.written'subject", universal)]) .statements
  -- the two altered copies of the naming module
  let namer ← IO.FS.readFile "ZkcFormal/Written/Views.lean"
  let shift ← replaceOnce namer "  let named ← name n e\n" "  let named := shiftNames (← name n e)\n"
  let shift ← replaceOnce shift "/-! ## Views -/\n" ("/-! ## Views -/\n\n" ++ shiftDefinitions)
  let held ← replaceOnce namer "  held.map fun k => (named[k]!, k)\n" "  held.zipIdx.map fun (k, i) => (named[i]!, k)\n"
  add "MutantShift" shift .statements
  add "MutantHeld" held .statements
  add "Shifted.Views" (viewsModule "Named.Stated" "Named.written'subject" (namer := "MutantShift")) .statements
  add "Held.Views" (viewsModule "Named.Stated" "Named.written'subject" (namer := "MutantHeld")) .statements
  add "ShiftedReads" (reader ["Shifted.Views"]
    [("Named.probes.mapped.installed.view", "Named.written'subject", universal)]) .statements
  add "HeldReads" (reader ["Held.Views"]
    [("Named.probes.mapped.installed.view", "Named.written'subject", universal)]) .statements
  add "PrintViews" ("import Named.Views\nimport Guess.Views\nimport Twice.Views\n\n" ++
    "set_option pp.proofs false\n" ++
    String.join (["Named.probes.mapped", "Guess.t.guessing", "Twice.t.twice"].flatMap fun p =>
      ["sound", "met", "installed"].map fun t => s!"#print {p}.{t}.view\n")) .statements
  -- a declaration named like an input, before the views and after them
  add "Before.Views" (viewsModule "Named.Stated" "Named.written'subject"
    (before := "def input_claim : Nat := 0\ndef valid_input_right : Nat := 0\ndef Named.input_right : Nat := 0\n\n")) .statements
  add "BeforeReads" (reader ["Before.Views"] (named3 "Named")) .statements
  -- the stored terms themselves, printed in full, are the same with and without the declarations
  let printAll (views : String) : String :=
    s!"import {views}\n\nset_option pp.all true\n" ++
      String.join (["sound", "met", "installed"].map fun t => s!"#print Named.probes.mapped.{t}.view\n")
  add "PrintNamed" (printAll "Named.Views") .statements
  add "PrintBefore" (printAll "Before.Views") .statements
  -- the command inside a name space and a section, with a variable named like an input, local
  -- notations for the interpretation's names and a printing option around it
  add "Ambient.Views" (viewsModule "Named.Stated" "Named.written'subject"
    (before := "namespace Customer\nsection\nvariable (input_claim : Nat)\nlocal notation \"model\" => Unit\n" ++
      "local notation \"draws\" => False\nset_option pp.universes true in\n")) .statements
  add "PrintAmbient" (printAll "Ambient.Views") .statements
  add "AfterReads" (reader ["Named.Views"] (named3 "Named")
    (before := "def input_claim : Nat := 0\ndef valid_input_right : Nat := 0\ndef Named.input_right : Nat := 0\n\n")) .statements
  -- a proof in an auxiliary constant; a witness telescope with another continuation
  let witnessRows := "  | witness0 := witness 0\n  | witness1 := witness 1\n"
  add "Lemmas" ("import Named.Stated\nimport ZkcFormalTests.ViewEntry\nimport ZkcFormalTests.ViewReader\n\n" ++ opens ++
    "declare_view Named.written'subject Named.literal :\n" ++
    "  Soundness.Installed model Named.written'application0 draws (⟨0, 1, Nat.zero_lt_succ 0⟩ : Zkc.Subject.Bound).limit\n" ++
    "open Lean in\n#eval show MetaM Unit from do\n" ++
    "  let some (.defnInfo d) := (← getEnv).find? `Named.literal.view | throwError \"no view\"\n" ++
    "  let aux := d.value.getUsedConstants.filter fun c => c.toString.endsWith \"_proof_1\"\n" ++
    "  if aux.isEmpty then throwError \"the view holds no auxiliary proof\"\n" ++
    "  logInfo m!\"the view holds the auxiliary proof {aux}\"\n" ++
    s!"#view_reads Named.literal.view of Named.written'subject at 0\n{universal}" ++
    "declare_view Named.written'subject Named.constant :\n" ++
    "  Goal.Internal.witnesses model\n" ++
    "    (Named.written'application0.relation.header.ins.drop Named.written'application0.arity) fun _ => True\n" ++
    s!"#view_reads Named.constant.view of Named.written'subject at 0\n{witnessRows}" ++
    "#print Named.constant.view\n") .statements
  -- the premise after an input telescope, by its head; a binder that the naming did not make
  let ports := "Goal.Internal.inputs model 1 false Named.written'root.entry.header.ins"
  let inputs := "[`input_claim, `valid_input_claim, `input_right, `valid_input_right"
  add "Premises" ("import Named.Views\nimport ZkcFormalTests.ViewEntry\n\n" ++ spineReader ++ opens ++
    "def Customer.Ready : Prop := True\ndef Customer.Idle : Prop := True\n" ++
    "opaque Customer.Later (h : Customer.Ready) : Prop\nopaque Customer.Other (h : Customer.Idle) : Prop\n" ++
    "attribute [view_premise] Customer.Ready\n" ++
    s!"declare_view Named.written'subject Named.ordinary : {ports} fun _ => Customer.Ready → True\n" ++
    s!"declare_view Named.written'subject Named.dependent :\n  {ports} fun _ => ∀ original : Customer.Ready, Customer.Later original\n" ++
    s!"declare_view Named.written'subject Named.unregistered : {ports} fun _ => Customer.Idle → True\n" ++
    s!"declare_view Named.written'subject Named.unregisteredDependent :\n  {ports} fun _ => ∀ original : Customer.Idle, Customer.Other original\n" ++
    s!"#eval spineIs `Named.probes.mapped.installed.view (`path :: {inputs}, `rejected])\n" ++
    s!"#eval spineIs `Named.ordinary.view ({inputs}, `ready])\n" ++
    s!"#eval spineIs `Named.dependent.view ({inputs}, `ready])\n" ++
    s!"#eval spineIs `Named.unregistered.view ({inputs}, .anonymous])\n" ++
    s!"#eval spineIs `Named.unregisteredDependent.view ({inputs}, `original])\n") .statements
  add "OtherBinders" ("import Named.Stated\nimport ZkcFormalTests.ViewEntry\n\n" ++ spineReader ++ opens ++
    s!"declare_view Named.written'subject Named.neutral :\n  ∀ item : model.Val .bool, {ports} fun _ => item = true\n" ++
    s!"declare_view Named.written'subject Named.spelled :\n  ∀ portfolio : model.Val .bool, {ports} fun _ => portfolio = true\n" ++
    s!"#eval spineIs `Named.neutral.view (`item :: {inputs}])\n    [(0, ``Zkc.Core.Model.Val), (1, ``Bool), (3, ``Bool)]\n" ++
    s!"#eval spineIs `Named.spelled.view (`portfolio :: {inputs}])\n    [(0, ``Zkc.Core.Model.Val), (1, ``Bool), (3, ``Bool)]\n") .statements
  -- wrappers in the list and not; a telescope over other ports
  let lemmaHead := "import Named.Stated\nimport ZkcFormalTests.ViewEntry\nimport ZkcFormalTests.ViewReader\n\n" ++ opens
  add "Listed" (lemmaHead ++
    "@[view_unfold] def Customer.bound (b : ℝ≥0∞) : Prop := Soundness.Installed model Named.written'application0 draws b\n" ++
    "@[view_unfold] def ZkcFormal.Analysis.closed : Prop :=\n" ++
    "  Soundness.Installed model Named.written'application0 draws Named.written'bound0.limit\n" ++
    "declare_view Named.written'subject Named.wrapper : Customer.bound Named.written'bound0.limit\n" ++
    s!"#view_reads Named.wrapper.view of Named.written'subject at 0\n{universal}" ++
    "declare_view Named.written'subject Named.closed : ZkcFormal.Analysis.closed\n" ++
    s!"#view_reads Named.closed.view of Named.written'subject at 0\n{universal}") .statements
  add "UnlistedWrapper" (lemmaHead ++
    "def Customer.bound (b : ℝ≥0∞) : Prop := Soundness.Installed model Named.written'application0 draws b\n" ++
    "#check view% Named.written'subject (Customer.bound Named.written'bound0.limit)\n") .statements
  add "UnlistedClosed" (lemmaHead ++
    "def ZkcFormal.Analysis.closed : Prop :=\n" ++
    "  Soundness.Installed model Named.written'application0 draws Named.written'bound0.limit\n" ++
    "#check view% Named.written'subject ZkcFormal.Analysis.closed\n") .statements
  add "OtherPorts" (lemmaHead ++
    "#check view% Named.written'subject\n" ++
    "  (Goal.Internal.inputs model 1 false [⟨Zkc.Core.Ty.bool, [0, 1]⟩] fun _ => True)\n") .statements
  -- the proof by rewriting on the declared view, judged; and on the named term not presented
  let proofHead := "import Named.Views\nimport ZkcFormal.Written.Publish\n\n" ++ opens ++ "namespace Named\n\n"
  add "Named.Proof" (proofHead ++ authorProof "probes.mapped.installed.view" ++
    "theorem probes.mapped.sound : published% written'subject probes.mapped sound :=\n" ++
    "  probes.mapped.sound_of_installed installedBound\n\n" ++
    "theorem probes.mapped.met : published% written'subject probes.mapped met :=\n" ++
    "  probes.mapped.met.view_iff.mp ⟨true, trivial, false, trivial, served, fun b n _ _ accepted => by\n" ++
    "    have := (acceptsLaw false b n).symm.trans accepted\n" ++
    "    simp at this⟩\n\nend Named\n") .module
  add "NotPresented" ("import Named.Stated\nimport ZkcFormalTests.ViewEntry\n\n" ++ opens ++ "namespace Named\n\n" ++
    "def namedOnly : Prop :=\n" ++
    "  named_view% written'subject (Soundness.Installed model written'application0 draws written'bound0.limit)\n\n" ++
    authorProof "namedOnly" ++ "end Named\n") .module
  SubjectProject.expect project "Named" [(`Named.Challenge, `Named.Proof)]
    [`Named.probes.mapped.sound, `Named.probes.mapped.met] WrittenSubject.allowed
  -- what Lean and the judgment say
  let result (name : String) := SubjectProject.result project name.toName
  for name in ["PrintViews", "Named.Views", "Guess.Views", "Twice.Views", "Exchanged.Views", "NamedReads", "GuessReads",
      "TwiceReads", "Short.Views", "ShortReads", "Shifted.Views", "Held.Views", "Before.Views", "BeforeReads",
      "AfterReads", "Lemmas", "Premises", "OtherBinders", "Listed"] do
    let (ok, output) ← result name
    unless ok do throw (IO.userError s!"{name}: Lean refused the module\n{output}")
    IO.println s!"{name}: accepted\n{output}"
  let printed (name : String) : IO String := do
    let (ok, output) ← result name
    unless ok do throw (IO.userError s!"{name}: Lean refused the module\n{output}")
    -- what Lean printed, without the positions, which name the module
    return "\n".intercalate ((output.splitOn "\n").map fun line =>
      match line.splitOn ": info: " with
      | [_, rest] => rest
      | _ => line)
  unless (← printed "PrintNamed") == (← printed "PrintBefore") do
    throw (IO.userError "a declaration named like an input before the views changed a view's term")
  unless (← printed "PrintNamed") == (← printed "PrintAmbient") do
    throw (IO.userError "the scope around the command changed a view's term")
  IO.println ("PrintNamed = PrintBefore = PrintAmbient: the three views' terms (pp.all) are the same with the " ++
    "declarations before the views, and with a variable, local notations and an option around the command")
  refusedAt "a subject whose origins exchange two names" (← result "ExchangedReads")
    ["Exchanged.probes.mapped.sound.view: at the source's binder 0 the view binds `input_right` where the source gives `input_claim`"]
  refusedAt "the namer that shifts each name onto the binder before" (← result "ShiftedReads")
    ["Named.probes.mapped.installed.view: the binder `input_claim` has the type"]
  refusedAt "the namer that takes a held input's name at its position among the held" (← result "HeldReads")
    ["Named.probes.mapped.installed.view: at the source's binder 2 the view binds `input_flag` where the source gives `input_right`"]
  refusedAt "a row past the subject's rows" (← result "PastTheRows") ["publish: no row 1 in a table of 1"]
  refusedAt "a wrapper outside the list" (← result "UnlistedWrapper") ["views: no input or witness telescope is reached"]
  refusedAt "a closed constant outside the list" (← result "UnlistedClosed") ["views: no input or witness telescope is reached"]
  refusedAt "a telescope over other ports" (← result "OtherPorts")
    ["views: an input telescope over ports that are not the deployed inputs of the subject's root"]
  let (ok, output) ← result "Named.Proof"
  unless ok do throw (IO.userError s!"the proof on the declared view: Lean refused it\n{output}")
  refusedAt "the proof on the named term, not presented" (← result "NotPresented") ["error: Tactic `rewrite` failed"]
  let (verdict, said) ← SubjectProject.judge project "Named"
  unless verdict == .accepted do
    throw (IO.userError s!"the proof through the declared views was not accepted\n{said}")
  for name in ["PastTheRows", "ExchangedReads", "ShiftedReads", "HeldReads", "UnlistedWrapper", "UnlistedClosed", "OtherPorts", "NotPresented"] do
    IO.println s!"{name}: refused\n{(← result name).2}"
  IO.println ("Views by the library's command: the views of the three subjects and of the short clause are " ++
    "declared and read by name and type; a row past the rows, exchanged origins and two altered namers are " ++
    "refused; premises are named by their registered heads and other binders keep their types; the proof " ++
    "through the views and the declared step is accepted by lake comparator.")

end WrittenViews

#eval show IO Unit from do
  match ← IO.getEnv "ZKC_WORK" with
  | some work => WrittenViews.run work
  | none => IO.FS.withTempDir WrittenViews.run
