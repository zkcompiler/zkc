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
* The proof module is judged by `lake comparator` against the challenge and is accepted.
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
  "theorem probes.mapped.sound : published% written'subject probes.mapped sound :=\n" ++
  "  Soundness.result_of_installed model written'application0 draws mapped_covered installedBound\n\n" ++
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

private def refusedReader (name : String) (lean : Bool × String) : IO Unit := do
  unless !lean.1 && lean.2.contains "the challenge states" do
    throw (IO.userError s!"{name}: the reader of the challenge did not refuse this spelling\n{lean.2}")

def run (work : System.FilePath) : IO Unit := do
  let project := projectOf work
  let honest ← IO.ofExcept ((← statements source).module "Published" {})
  unless honest.refusals.isEmpty do throw (IO.userError s!"{honest.refusals}")
  let low ← IO.ofExcept ((← statements (source.replace "clause = explicit)\n" "clause = explicit) <= 1 / 2\n")).module
    "Published" {} (statements := some `Low.Stated))
  unless low.refusals.isEmpty do throw (IO.userError s!"{low.refusals}")
  discard <| SubjectProject.add project `Published.Stated honest.statements .statements
  discard <| SubjectProject.add project `Published.Challenge (challenge "Published.Stated" "Published") .challenge
  discard <| SubjectProject.add project `Published.Proof (proof "Published.Stated" "Published")
  discard <| SubjectProject.add project `Low.Stated low.statements .statements
  discard <| SubjectProject.add project `Low.Challenge (challenge "Low.Stated" "Published") .challenge
  let reads ← startLakeLean work "PublishedReads" (reader resultSpelling boundSpelling) (text := false)
  let installed ← startLakeLean work "PublishedReadsInstalled"
    (reader "Soundness.Installed model Published.written'application0 draws" boundSpelling) (text := false)
  let number ← startLakeLean work "PublishedReadsNumber"
    (reader resultSpelling "(⟨0, 1, by decide⟩ : Zkc.Subject.Bound).limit") (text := false)
  let theorems := [`Published.probes.mapped.sound, `Published.probes.mapped.met]
  SubjectProject.expect project "Published" [(`Published.Challenge, `Published.Proof)] theorems WrittenSubject.allowed
  SubjectProject.expect project "Low" [(`Low.Challenge, `Published.Proof)] theorems WrittenSubject.allowed
  acceptedByLean "the reader of the built challenge" (← reads)
  refusedReader "the installed bound where the result stands" (← installed)
  refusedReader "the bound's number where its constant stands" (← number)
  let (verdict, said) ← SubjectProject.judge project "Published"
  unless verdict == .accepted do
    throw (IO.userError s!"the published theorems were not accepted against the library's challenge\n{said}")
  let (verdict, said) ← SubjectProject.judge project "Low"
  unless verdict == .refused && said.contains "Const does not match" && said.contains "written'bound0" do
    throw (IO.userError s!"the challenge at another bound was not refused at the bound\n{said}")
  IO.println ("The library states what a goal publishes from its row: the built challenge holds " ++
    "exactly the statements that the check spells; the proof module that states them as " ++
    "`published%` is accepted, and refused against a subject at another bound.")

end WrittenPublish

#eval IO.FS.withTempDir WrittenPublish.run
