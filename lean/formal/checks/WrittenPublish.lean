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
  return ⟨claims, claims.functionsBeforeRoot⟩

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
  "    (fnMeaning model installed mappedMember (.cons x (.cons b (.cons n .nil)))) =\n" ++
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
  -- the shape of what the issuer publishes, and ten changes of it that the controls refuse
  let control (command : String) (imported : String) :=
    s!"import {imported}\nimport ZkcFormalTests.PublicationControl\n\n{command}\n"
  let shape ← startLakeLean work "PublishedShape" (control
    "#data_module Published.Stated\n#challenge_module Published.Challenge over Published.Stated" "Published.Challenge")
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
    ("WithComputedBound", ← replaceOnce honest.data (bound ++ "⟨0, 1, by decide⟩") (bound ++ "⟨0 + 0, 1, by decide⟩"),
      "data control: the bound Published.written'bound0 is not two numerals")]
  let mut shapes := []
  for (name, text, refusal) in mutants do
    discard <| SubjectProject.add project s!"{name}.Stated".toName text .statements
    shapes := shapes ++ [(name, refusal, ← startLakeLean work (name ++ "Shape")
      (control s!"#data_module {name}.Stated" s!"{name}.Stated") (text := false))]
  discard <| SubjectProject.add project `Published.Views honest.views .statements
  discard <| SubjectProject.add project `Wide.Challenge
    ("import Published.Views\n" ++ honest.challenge) .challenge
  let wide ← startLakeLean work "WideShape"
    (control "#challenge_module Wide.Challenge over Published.Stated" "Wide.Challenge") (text := false)
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
    "imports what the publication command does; 10 of 10 changes of that shape are refused.")
  IO.println ("The library states what a goal publishes from its row: the built challenge holds " ++
    "exactly the statements that the check spells; the proof module that states them as " ++
    "`published%` is accepted, and refused against a subject at another bound.")

end WrittenPublish

#eval IO.FS.withTempDir WrittenPublish.run
