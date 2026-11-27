import ZkcFormalTests.WrittenSubject

/-!
The library states what a goal publishes, from the goal's row.

A subject's goal rows say the path of each goal's declaration and its property. The challenge of
a subject is then three lines for every subject: the module of the statements, the library's
module `ZkcFormal.Written.Publish`, and `publish_goals <space>.written'subject`, which declares
the theorems `<space>.<path>.sound` and `.met` from the rows, without a proof. An author states
a published theorem as `published% written'subject <path> sound`, the same statement, and
proves it.

The subject is the explicit clause of the author checks (`Accepts(right; flag, n)`, two shared
inputs of one type and a witness).

* A reader of the built challenge finds exactly the two theorems, each with the statement that
  this check spells itself from the short application's and the bound's constants. It refuses a
  spelling with the installed bound where the result stands, and a spelling with the bound's
  number where its constant stands.
* The control of a challenge by the subject's rows (`#challenge_theorems`, which the harness runs
  on every pair that it starts, `startModule`) accepts the issuer's challenge with the two names that
  are judged, and refuses a judgment that is given one name less, a challenge with one theorem
  more, and a challenge whose `sound` is at a number and not at the row's bound.
* A row that writes its ceiling and holds an optional table that cannot be opened is published:
  the challenge and the statement as a term read the bound alone; the fee facts, which ask for
  the table, refuse it.
* The proof module is judged by `lake comparator` against the challenge and is accepted. It
  also states the result through a macro and through a notation of its own, each of which gives
  the same statement.
* The same proof module is refused against the challenge of the source that writes the ceiling
  `1 / 2`, at the bound's constant.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace WrittenPublish

def source := "module probes
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

def statements (text : String) : IO Statements := do
  let assembly ← Driver.assembleFiles ⟨"source.zkc", Syntax.parseString "source.zkc" text⟩
    ["../../libraries"]
  let root ← IO.ofExcept (admitSoundnessGoal assembly "mapped")
  let claims ← IO.ofExcept (goalClaims root ["mapped"])
  return ⟨claims⟩

/-- The challenge: the same three lines for every subject. -/
def challenge (stated space : String) : String :=
  s!"import {stated}\nimport ZkcFormal.Written.Publish\n\npublish_goals {space}.written'subject\n"

private def opens : String :=
  "open Zkc.Core ZkcFormal ZkcFormal.ProbabilisticProcess ZkcFormal.Written OracleComp ProbComp\n" ++
  "open scoped NNRat ENNReal\n" ++
  "open ZkcFormal.Written.StandardInterpretation (model served draws covers)\n"

/-- The author's proof module: the installed bound with its binders in their order, the receipt
by the library's step, each published theorem stated as `published%`. -/
def proof (stated space : String) : String :=
  s!"import {stated}\nimport ZkcFormal.Written.Publish\n\n" ++ opens ++ s!"namespace {space}\n\n" ++
  "theorem acceptsLaw (x b : Bool) (n : Nat) : functionResult (t := .bool)\n" ++
  "    (fnMeaning model installed member'fn0 (.cons x (.cons b (.cons n .nil)))) =\n" ++
  "      some (x && (b || (n == 0))) := by\n" ++
  "  kernel_rfl\n\n" ++
  "theorem installedBound : Soundness.Installed model written'application0 draws written'bound0.limit := by\n" ++
  "  intro path claim _ right _ rejected\n" ++
  "  have declined : right = false := by\n" ++
  "    cases right with\n" ++
  "    | false => rfl\n" ++
  "    | true => exact False.elim (rejected true 0 trivial trivial (acceptsLaw true true 0))\n" ++
  "  subst declined\n" ++
  "  apply returnsWithin_of_returns\n" ++
  "  intro σ service _ _ state\n" ++
  "  have halts : roleMeaning model installed rootMember verifierRole path\n" ++
  "      (.cons claim (.cons () (.cons false (.cons () .nil)))) = .halt (.declared .reject ⟨path, ⟨0⟩⟩) := by\n" ++
  "    cases claim <;> kernel_rfl\n" ++
  "  rw [prEvent_simulation_returns]\n" ++
  "  erw [halts]\n" ++
  "  simp [run, Process.interpret]\n\n" ++
  "-- An author's abbreviation: a macro supplies the path and the theorem's name.\n" ++
  "macro \"mapped_result%\" : term => `(published% written'subject probes.mapped sound)\n" ++
  "example : mapped_result% = published% written'subject probes.mapped sound := rfl\n" ++
  "local notation \"MappedResult\" => (published% written'subject probes.mapped sound)\n" ++
  "example : MappedResult = published% written'subject probes.mapped sound := rfl\n\n" ++
  "theorem probes.mapped.sound : published% written'subject probes.mapped sound :=\n" ++
  "  Soundness.result_of_installed model written'application0 draws (by decide +kernel) installedBound\n\n" ++
  "theorem probes.mapped.met : published% written'subject probes.mapped met :=\n" ++
  "  Soundness.witnessed_of model written'application0 draws served true trivial false trivial\n" ++
  "    (fun b n _ _ accepted => by\n" ++
  "      have := (acceptsLaw false b n).symm.trans accepted\n" ++
  "      simp at this)\n\n" ++
  s!"end {space}\n"

/-- A reader of the built challenge with the two statements as this check spells them; `result`
and `bound` are the two places that the refused variants change. -/
def reader (result bound : String) : String :=
  "import Published.Challenge\nimport ZkcFormalTests.ChallengeReader\n\n" ++ opens ++
  "#challenge_is Published.Challenge\n" ++
  s!"  | Published.probes.mapped.sound := {result} {bound}\n" ++
  "  | Published.probes.mapped.met := Soundness.Witnessed model Published.written'application0 draws\n"

private def resultSpelling := "Soundness.Result model Published.written'application0 draws covers"
private def boundSpelling := "Published.written'bound0.limit"

/-- The reader refuses a spelling of `sound` at that theorem, and Lean reports no other error
of the module. -/
private def refusedReader (name : String) (lean : Bool × String) : IO Unit := do
  if lean.1 then throw (IO.userError s!"{name}: the reader of the challenge accepted this spelling")
  expectPlacesIn name lean.2 ["Published.probes.mapped.sound: the challenge states"]

def run (work : System.FilePath) : IO Unit := do
  let project := projectOf work
  let honest ← IO.ofExcept ((← statements source).publication "Published")
  unless honest.refusals.isEmpty do throw (IO.userError s!"{honest.refusals}")
  let low ← IO.ofExcept ((← statements (source.replace "clause = explicit)\n" "clause = explicit) <= 1 / 2\n")).publication
    "Published" (data := some `Low.Stated))
  unless low.refusals.isEmpty do throw (IO.userError s!"{low.refusals}")
  -- the issuer's challenge is the three lines, and its published theorems are the two of the row
  unless honest.challenge == challenge "Published.Stated" "Published" && low.challenge == challenge "Low.Stated" "Published" do
    throw (IO.userError s!"the issuer's challenge is not the three lines:\n{honest.challenge}")
  unless honest.published == [`Published.probes.mapped.sound, `Published.probes.mapped.met] do
    throw (IO.userError s!"the issuer's published theorems are {honest.published}")
  discard <| SubjectProject.add project `Published.Stated honest.data .statements
  discard <| SubjectProject.add project `Published.Challenge honest.challenge .challenge
  discard <| SubjectProject.add project `Published.Proof (proof "Published.Stated" "Published")
  discard <| SubjectProject.add project `Low.Stated low.data .statements
  discard <| SubjectProject.add project `Low.Challenge low.challenge .challenge
  -- the shape of what the issuer publishes, and twenty-five changes of it that the controls refuse
  let control (command : String) (imported : String) :=
    s!"import {imported}\nimport ZkcFormalTests.PublicationControl\n\n{command}\n"
  let shape ← startLakeLean work "PublishedShape" (control
    "#data_module Published.Stated of Published.written'subject\n#challenge_module Published.Challenge over Published.Stated" "Published.Challenge")
    (text := false)
  let ending := "#print axioms admitted_exists"
  let bound := "def written'bound0 : Zkc.Subject.Bound := "
  let mutants : List (String × String × String) := [
    ("WithProposition", ← replaceOnce honest.data ending ("def extra : Prop := True\n" ++ ending),
      "data control: WithProposition.Stated defines the proposition Published.extra"),
    ("WithTheorem", ← replaceOnce honest.data ending ("theorem extra : True := trivial\n" ++ ending),
      "data control: WithTheorem.Stated states the theorem Published.extra"),
    ("WithPredicate", ← replaceOnce honest.data ending ("def extraOf (n : Nat) : Prop := n = n\n" ++ ending),
      "data control: WithPredicate.Stated defines the proposition Published.extraOf"),
    ("WithAliasedPredicate", ← replaceOnce honest.data ending
        ("def Claim (α : Type) : Type := α → Prop\ndef extraOf : Claim Nat := fun n => n = n\n" ++ ending),
      "data control: WithAliasedPredicate.Stated defines the proposition Published.extraOf"),
    ("WithInductive", ← replaceOnce honest.data ending ("inductive Extra : Prop where | intro\n" ++ ending),
      "data control: WithInductive.Stated declares the inductive type Published.Extra"),
    ("WithNamedTheorem", ← replaceOnce honest.data ending ("theorem extra.found'root : True := trivial\n" ++ ending),
      "data control: WithNamedTheorem.Stated states the theorem Published.extra.found'root"),
    ("WithInstance", ← replaceOnce honest.data ending ("instance : Inhabited Zkc.Subject.Bound := ⟨written'bound0⟩\n" ++ ending),
      "data control: WithInstance.Stated declares the instance"),
    ("WithImport", "import Std.Data.HashMap\n" ++ honest.data,
      "data control: WithImport.Stated imports Std.Data.HashMap, which is none of the issuer's list"),
    ("WithLibrary", "import ZkcFormal.Written.Bound\n" ++ honest.data,
      "data control: WithLibrary.Stated imports the formal library's ZkcFormal.Written.Bound"),
    ("WithTableInPlace", ← replaceOnce honest.data "number := .total written'caps0 written'bound0 }" "number := .total ⟨[]⟩ written'bound0 }",
      "data control: the number of Published.written'fields0 is not a constructor over declarations"),
    -- a row whose bound is another declaration, which is no pair of numerals and reads the table
    ("WithOtherBound", ← replaceOnce (← replaceOnce honest.data "number := .total written'caps0 written'bound0 }"
        "number := .total written'caps0 otherBound }") "def written'fields0 :"
        "def otherBound : Zkc.Subject.Bound := ⟨written'caps0.uses.length - 1, 1, by decide⟩\ndef written'fields0 :",
      "data control: the bound Published.otherBound is not two numerals"),
    ("WithReadingTable", ← replaceOnce (← replaceOnce honest.data "number := .total written'caps0 written'bound0 }"
        "number := .total otherCaps written'bound0 }") "def written'fields0 :"
        "def otherCaps : Zkc.Subject.CapTable := written'caps0\ndef written'fields0 :",
      "data control: the table Published.otherCaps reads Published.written'caps0"),
    ("WithComputedBound", ← replaceOnce honest.data (bound ++ "⟨0, 1, by decide⟩") (bound ++ "⟨0 + 0, 1, by decide⟩"),
      "data control: the bound Published.written'bound0 is not two numerals"),
    -- a numeral whose instance computes another number from the table
    ("WithInstanceNumeral", ← replaceOnce honest.data (bound ++ "⟨0, 1, by decide⟩")
        (bound ++ "⟨@OfNat.ofNat Nat (nat_lit 0) ⟨written'caps0.uses.length⟩, 1, by decide⟩"),
      "data control: the bound Published.written'bound0 is not two numerals"),
    -- a theorem about the stored program that the subject reaches through the bound's proof
    ("WithReachedTheorem", ← replaceOnce honest.data (bound ++ "⟨0, 1, by decide⟩")
        ("theorem extra : stored = stored ∧ 0 < 1 := ⟨rfl, by decide⟩\n" ++ bound ++ "⟨0, 1, extra.2⟩"),
      "data control: WithReachedTheorem.Stated states the theorem Published.extra"),
    ("WithPropositions", ← replaceOnce honest.data ending ("def extraClaims : List Prop := [True]\n" ++ ending),
      "data control: WithPropositions.Stated defines the proposition Published.extraClaims"),
    ("WithProofDefinition", ← replaceOnce honest.data ending ("set_option linter.defProp false in\ndef extraFact : 0 < 1 := by decide\n" ++ ending),
      "data control: WithProofDefinition.Stated holds a proof in the definition Published.extraFact"),
    -- a number that a computation over the table chooses
    ("WithChosenNumber", ← replaceOnce honest.data "number := .total written'caps0 written'bound0 }"
        ("number := if written'caps0.uses.length = 0 then .total written'caps0 written'bound0 " ++
          "else .total written'caps0 written'bound0 }"),
      "data control: the number of Published.written'fields0 is not a constructor over declarations"),
    -- a path, and a decision, that a computation over the table chooses
    ("WithChosenPath", ← replaceOnce honest.data "path := [\"probes\", \"mapped\"]"
        "path := if written'caps0.uses.length = 0 then [\"probes\", \"mapped\"] else [\"probes\", \"mapped\"]",
      "data control: the path of the row Published.written'slot0 is not built of constructors, literals and declarations"),
    ("WithChosenDecision", ← replaceOnce honest.data "⟨1, fun _ => written'decision0⟩"
        "⟨1, fun _ => if written'caps0.uses.length = 0 then written'decision0 else written'decision0⟩",
      "data control: the table of decisions of Published.written'subject reads Published.written'caps0, which is none of its elements"),
    -- a path that is a declaration whose value a computation chooses
    ("WithPathDeclared", ← replaceOnce (← replaceOnce honest.data "path := [\"probes\", \"mapped\"]" "path := chosenPath")
        "def written'fields0 :"
        ("def chosenPath : List String := if written'caps0.uses.length = 0 then [\"probes\", \"mapped\"] else [\"probes\", \"mapped\"]\n" ++
          "def written'fields0 :"),
      "data control: the path of the row Published.written'slot0 is not built of constructors, literals and declarations"),
    -- a cap whose numeral's instance gives another number
    ("WithCapInstance", ← replaceOnce honest.data "def written'caps0 : Zkc.Subject.CapTable := ⟨["
        "def written'caps0 : Zkc.Subject.CapTable := ⟨[⟨⟨@OfNat.ofNat Nat (nat_lit 9) ⟨7⟩⟩, .nil⟩, ",
      "data control: the table Published.written'caps0 is not built of constructors and numerals"),
    -- a selector that gives one decision whatever the index, by a conditional
    ("WithSelectorTwice", ← replaceOnce honest.data "⟨1, fun _ => written'decision0⟩"
        "⟨1, fun i => if i.val < 1 then written'decision0 else written'decision0⟩",
      "data control: the selector of the table of decisions of Published.written'subject does not give 1 elements, each at one index"),
    -- a private proposition
    ("WithPrivateTheorem", ← replaceOnce honest.data ending ("private theorem hidden : stored = stored := rfl\n" ++ ending),
      "data control: WithPrivateTheorem.Stated states the theorem")]
  let mut shapes := []
  for (name, text, refusal) in mutants do
    discard <| SubjectProject.add project s!"{name}.Stated".toName text .statements
    shapes := shapes ++ [(name, refusal, ← startLakeLean work (name ++ "Shape")
      (control s!"#data_module {name}.Stated of Published.written'subject" s!"{name}.Stated") (text := false))]
  discard <| SubjectProject.add project `Published.Views honest.views .statements
  discard <| SubjectProject.add project `Wide.Challenge
    ("import Published.Views\n" ++ honest.challenge) .challenge
  let wide ← startLakeLean work "WideShape"
    (control "#challenge_module Wide.Challenge over Published.Stated" "Wide.Challenge") (text := false)
  -- what a challenge states, by the rows: the issuer's challenge; a judgment given one name less; a
  -- challenge with one theorem more; a challenge whose `sound` is at a number and not at the row's bound
  let both := "\"Published.probes.mapped.sound\", \"Published.probes.mapped.met\""
  let byRows (challenge published : String) :=
    control s!"#challenge_theorems {challenge} of Published.written'subject published {published} beside " challenge
  discard <| SubjectProject.add project `More.Challenge
    (honest.challenge ++ "theorem Published.extra : True := trivial\n") .challenge
  discard <| SubjectProject.add project `Numbered.Challenge
    ("import Published.Stated\nimport ZkcFormal.Written.Publish\n\n" ++ opens ++
      s!"theorem Published.probes.mapped.sound : {resultSpelling} (⟨0, 1, by decide⟩ : Zkc.Subject.Bound).limit := by sorry\n" ++
      "theorem Published.probes.mapped.met : Soundness.Witnessed model Published.written'application0 draws := by sorry\n")
    .challenge
  let rowsControls := [
    ("the issuer's challenge by its rows", "PublishedByRows", byRows "Published.Challenge" both, none),
    ("a judgment that is given one name less", "FewerJudged",
      byRows "Published.Challenge" "\"Published.probes.mapped.sound\"",
      some "challenge control: the judgment is given [Published.probes.mapped.sound]; the rows of Published.written'subject publish"),
    ("a challenge with one theorem more", "MoreByRows", byRows "More.Challenge" both,
      some "challenge control: More.Challenge states"),
    ("a challenge whose `sound` is at a number", "NumberedByRows", byRows "Numbered.Challenge" both,
      some "challenge control: Published.probes.mapped.sound: the challenge states")]
  let mut byRowsPending := []
  for (title, name, text, refusal) in rowsControls do
    byRowsPending := byRowsPending ++ [(title, refusal, ← startLakeLean work name text (text := false))]
  -- A row that writes its ceiling, with an optional table that cannot be opened: what the goal
  -- publishes is its bound, and neither the challenge nor a published statement as a term reads
  -- the table; the fee facts ask for it and say that they cannot read it.
  let hidden ← replaceOnce (← replaceOnce honest.data "number := .total written'caps0 written'bound0 }"
      "number := .ceiling written'bound0 hiddenCaps }") "def written'fields0 :"
    "opaque hiddenCaps : Option Zkc.Subject.CapTable\ndef written'fields0 :"
  discard <| SubjectProject.add project `Hidden.Stated hidden .statements
  discard <| SubjectProject.add project `Hidden.Challenge (challenge "Hidden.Stated" "Published") .challenge
  let hiddenTerm ← startLakeLean work "HiddenTerm"
    ("import Hidden.Challenge\n\n" ++
      "example : Published.probes.mapped.sound = Published.probes.mapped.sound := rfl\n" ++
      "example : Prop := published% Published.written'subject probes.mapped sound\n") (text := false)
  let hiddenFees ← startLakeLean work "HiddenFees"
    "import Hidden.Stated\nimport ZkcFormal.Written.FeeFacts\n\npublish_fees Published.written'subject\n" (text := false)
  let reads ← startLakeLean work "PublishedReads" (reader resultSpelling boundSpelling) (text := false)
  let installed ← startLakeLean work "PublishedReadsInstalled"
    (reader "Soundness.Installed model Published.written'application0 draws" boundSpelling) (text := false)
  let number ← startLakeLean work "PublishedReadsNumber"
    (reader resultSpelling "(⟨0, 1, by decide⟩ : Zkc.Subject.Bound).limit") (text := false)
  let theorems := [`Published.probes.mapped.sound, `Published.probes.mapped.met]
  SubjectProject.expect project "Published" [(`Published.Challenge, `Published.Proof)] theorems WrittenSubject.allowed
  SubjectProject.expect project "Low" [(`Low.Challenge, `Published.Proof)] theorems WrittenSubject.allowed
  acceptedByLean "the reader of the built challenge" (← reads)
  acceptedByLean "the shape of the data module and of the challenge" (← shape)
  for (name, refusal, pending) in shapes do
    let (ok, output) ← pending
    expectErrorsAt s!"the data module {name}" ok output [refusal]
  let (ok, output) ← wide
  expectErrorsAt "a challenge that imports a views module" ok output
    ["challenge control: Wide.Challenge imports Published.Views"]
  for (title, refusal, pending) in byRowsPending do
    match refusal with
    | none => acceptedByLean title (← pending)
    | some refusal =>
      let (ok, output) ← pending
      expectErrorsAt title ok output [refusal]
  acceptedByLean "the challenge and the published statement of a row whose table cannot be opened" (← hiddenTerm)
  let (ok, output) ← hiddenFees
  expectErrorsAt "the fee facts of a row whose table cannot be opened" ok output
    ["publish: expected a table of caps or none"]
  refusedReader "the installed bound where the result stands" (← installed)
  refusedReader "the bound's number where its constant stands" (← number)
  let (verdict, said) ← SubjectProject.judge project "Published"
  unless verdict == .accepted do
    throw (IO.userError s!"the published theorems were not accepted against the library's challenge\n{said}")
  let (verdict, said) ← SubjectProject.judge project "Low"
  unless verdict == .refused && said.contains "Const does not match" && said.contains "written'bound0" do
    throw (IO.userError s!"the challenge at another bound was not refused at the bound\n{said}")
  IO.println ("The issuer's data module holds definitions that are no propositions, the package's " ++
    "theorems and a bound of numerals, and imports no module of the formal library; its challenge " ++
    "imports what the publication command does; 25 of 25 changes of that shape are refused.")
  IO.println ("The library states what a goal publishes from its row: the built challenge holds " ++
    "exactly the statements that the check spells, and the control by rows refuses 3 of 3 " ++
    "changes of what is stated or judged; the proof module that states them as " ++
    "`published%` is accepted, and refused against a subject at another bound.")

end WrittenPublish

#eval IO.FS.withTempDir WrittenPublish.run
