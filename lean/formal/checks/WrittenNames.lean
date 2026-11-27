import ZkcFormalTests.WrittenSubject

/-!
Source names for the library's terms.

A published statement is the library's term, whose binders have the library's names. The tools
of `ZkcFormal.Written.SourceNames` read the source names of a subject's root (the instance of
`Zkc.Subject.SourceNames` that the issuer prints) and name the binders of a library term after
them: `source_intro` when a proof introduces them, `named%` for an application by name,
`source_view` for a named proposition beside the term with the theorem that it is the term, and
`#view_names`, which holds a view's names to those that the source gives.

The subject is the explicit clause of the author checks: the verifier holds `claim` and `right`
and not `flag` and `n`.

* A proof module that introduces the inputs by their source names and applies the receipt's step
  by name is judged by `lake comparator` against the library's challenge and is accepted.
* The views of the two published statements are declared and their names are the source's.
* A view made with two source names exchanged is the same proposition to Lean, and `#view_names`
  refuses it.
* An application by the name of an input that the verifier does not hold is refused.
* Where a source name is taken in the scope, the binder falls back to `port<ordinal>`.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace WrittenNames

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

private def head : String :=
  "import Named.Stated\nimport ZkcFormal.Written.Publish\nimport ZkcFormal.Written.SourceNames\n\n" ++
  "open Zkc.Core ZkcFormal ZkcFormal.ProbabilisticProcess ZkcFormal.Written OracleComp ProbComp\n" ++
  "open scoped NNRat ENNReal\n" ++
  "open ZkcFormal.Written.StandardInterpretation (model served draws covers)\n" ++
  "namespace Named\n\n"

private def receiptStep := "(named% Soundness.witnessed_of model written'application0 draws served)"

/-- The author's proof module, with the inputs under their source names. -/
def proof : String :=
  head ++
  "theorem acceptsLaw (x b : Bool) (n : Nat) : functionResult (t := .bool)\n" ++
  "    (fnMeaning model installed mappedMember (.cons x (.cons b (.cons n .nil)))) =\n" ++
  "      some (x && (b || (n == 0))) := by\n" ++
  "  kernel_rfl\n\n" ++
  "theorem installedBound : Soundness.Installed model written'application0 draws written'bound0.limit := by\n" ++
  "  source_intro\n" ++
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
  "  simp [run, Process.interpret]\n\n" ++
  "theorem probes.mapped.sound : published% written'subject probes.mapped sound :=\n" ++
  "  Soundness.result_of_installed model written'application0 draws mapped_covered installedBound\n\n" ++
  "theorem probes.mapped.met : published% written'subject probes.mapped met :=\n" ++
  s!"  {receiptStep} (input_right := false) (input_claim := true) trivial trivial\n" ++
  "    (fun b n _ _ accepted => by\n" ++
  "      have := (acceptsLaw false b n).symm.trans accepted\n" ++
  "      simp at this)\n\n" ++
  "end Named\n"

/-- The views of the two published statements, with their names held to the source's. -/
def views : String :=
  head ++
  "source_view soundView : published% written'subject probes.mapped sound\n" ++
  "source_view metView : published% written'subject probes.mapped met\n" ++
  "#view_names soundView : published% written'subject probes.mapped sound\n" ++
  "#view_names metView : published% written'subject probes.mapped met\n" ++
  "example : soundView ↔ published% written'subject probes.mapped sound := soundView_iff\n\n" ++
  "end Named\n"

/-- A view of the receipt made with the names of `claim` and `right` exchanged. -/
def exchanged : String :=
  head ++
  "section\n" ++
  "noncomputable local instance (priority := high) exchangedNames : Zkc.Subject.SourceNames written'root :=\n" ++
  "  ⟨{ written'origins with inputNames := #[\"right\", \"flag\", \"claim\", \"n\"], aligned := rfl }⟩\n" ++
  "def exchangedView : Prop := source_view% (published% written'subject probes.mapped met)\n" ++
  "end\n" ++
  "example : exchangedView ↔ published% written'subject probes.mapped met := Iff.rfl\n" ++
  "#view_names exchangedView : published% written'subject probes.mapped met\n\n" ++
  "end Named\n"

/-- An application by the name of an input that the verifier does not hold. -/
def notHeld : String :=
  head ++ s!"example := {receiptStep} (input_flag := true)\n\nend Named\n"

/-- The name `input_claim` is taken in the scope: the binder of `claim` is `port0`. -/
def taken : String :=
  head ++ "def input_claim : Nat := 0\n\n" ++
  s!"example := {receiptStep} (port0 := true) (input_right := false)\n\nend Named\n"

/-- Lean refuses the module by one error, which says `said`. -/
private def refused (name : String) (lean : Bool × String) (said : String) : IO Unit := do
  let errors := (lean.2.splitOn "error: ").length - 1
  unless !lean.1 && lean.2.contains said && errors ≤ 2 do
    throw (IO.userError s!"{name}: not refused by the one error `{said}`\n{lean.2}")

def run (work : System.FilePath) : IO Unit := do
  let project := projectOf work
  let honest ← IO.ofExcept ((← statements source).module "Named" {})
  unless honest.refusals.isEmpty do throw (IO.userError s!"{honest.refusals}")
  discard <| SubjectProject.add project `Named.Stated honest.statements .statements
  discard <| SubjectProject.add project `Named.Challenge
    "import Named.Stated\nimport ZkcFormal.Written.Publish\n\npublish_goals Named.written'subject\n" .challenge
  discard <| SubjectProject.add project `Named.Proof proof
  let viewed ← startLakeLean work "NamedViews" views (text := false)
  let exchangedNames ← startLakeLean work "NamedExchanged" exchanged (text := false)
  let unheld ← startLakeLean work "NamedNotHeld" notHeld
  let takenName ← startLakeLean work "NamedTaken" taken
  SubjectProject.expect project "Named" [(`Named.Challenge, `Named.Proof)]
    [`Named.probes.mapped.sound, `Named.probes.mapped.met] WrittenSubject.allowed
  acceptedByLean "the views of the published statements" (← viewed)
  refused "a view with two names exchanged" (← exchangedNames)
    "Named.exchangedView: the view's names are not those that the origins give"
  refused "the name of an input that the verifier does not hold" (← unheld) "input_flag"
  acceptedByLean "a binder whose source name is taken" (← takenName)
  let (verdict, said) ← SubjectProject.judge project "Named"
  unless verdict == .accepted do
    throw (IO.userError s!"the proof by source names was not accepted against the library's challenge\n{said}")
  IO.println ("The binders of the library's terms take the source's names: a proof by them is " ++
    "accepted; the views' names are the source's; exchanged names and a name that the verifier " ++
    "does not hold are refused.")

end WrittenNames

#eval IO.FS.withTempDir WrittenNames.run
