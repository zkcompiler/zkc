import ZkcFormalTests.WrittenSubject
import ZkcFormalTests.ViewRows

/-!
Fee facts declared by the library's command over a subject, decided row by row, and a proof by
fees closed through them.

The subject is the guarded verifier of the bound checks (`fixtures/written-bound-guard.zkc`): the
verifier draws once and rejects a claim that is not set; its table of caps is that one draw at one
over four. A fees module is its imports and `publish_fees S`.

* The goal at one over four, the table's budget: the command declares `counted`, `budget` (at the
  bound's numbers), `total_eq_limit`, the view of the judgment within that budget with its
  `view_iff`, and `installed_of_judged`; the reader of names and types reads the view. An author's
  proof of the judgment on its view (the input by the view's name, a rewrite on the verifier's
  meaning), closed by `installed_of_judged` and the views' `sound_of_installed`, is judged by
  `lake comparator` through the published theorems.
* The goal at one over two, above the budget: `budget` is at the table's numbers, there is no
  `total_eq_limit`, and the same text closes at the goal's bound and is judged. The goal at two over
  eight (the statements' bound rewritten), the budget in other numbers: `budget` is at the bound's
  numbers, with `total_eq_limit`.
* A bound below the budget (the statements' bound rewritten to one over eight), and a table that
  does not count as the stored program does (its count rewritten): the row gets no fee facts and a
  line that says which; the text that closed is refused at the judgment's view and at the step
  from it, which are not declared. (The statements carry the generated family's own theorems about
  a goal's table; the three that a rewritten table makes false are taken out.)
* Two rows of one subject, the second's table miscounted: the first row has its facts, the second
  has none.

With `ZKC_WORK` naming a folder the check's project is kept there.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace WrittenFees

/-- The statements module of the goals of a source, in the name space `space`. -/
def statementsOf (text : String) (goals : List String) (space : String) : IO String := do
  let assembly ← Driver.assembleFiles ⟨"source.zkc", Syntax.parseString "source.zkc" text⟩
    ["../../libraries"]
  let some first := goals.head? | throw (IO.userError "no goal")
  let root ← IO.ofExcept (admitSoundnessGoal assembly first)
  let claims ← IO.ofExcept (goalClaims root goals)
  let issued ← IO.ofExcept ((⟨claims, claims.functionsBeforeRoot⟩ : Statements).module space {})
  unless issued.refusals.isEmpty do throw (IO.userError s!"{issued.refusals}")
  return issued.statements

/-- The statements without the theorems that the generated family states of a goal's own table
(`<goal>_counted`, `<goal>_budget`, `<goal>_ceiling`), which a rewritten table makes false: what is
left is a subject whose table is wrong, for the library's command to decide. -/
def withoutTableFacts (stated goal : String) : IO String := do
  let names := ["counted", "budget", "ceiling"].map (s!"{goal}_{·}")
  let states (block : String) := names.any fun name =>
    (block.splitOn "\n").any (·.startsWith s!"theorem {name} ")
  let blocks := stated.splitOn "\n\n"
  unless (blocks.filter states).length == names.length do
    throw (IO.userError s!"expected one theorem for each of {names}")
  let kept := "\n\n".intercalate (blocks.filter (!states ·))
  return "\n".intercalate ((kept.splitOn "\n").filter fun line =>
    !names.any (line == s!"#print axioms {·}"))

def opens : String :=
  "open Zkc.Core ZkcFormal ZkcFormal.ProbabilisticProcess ZkcFormal.Written OracleComp ProbComp\n" ++
  "open scoped NNRat ENNReal\n" ++
  "open ZkcFormal.Written.StandardInterpretation (model served draws covers)\n"

/-- An author's text for the goal at `path`: the judgment by fees proved on its declared view, and
the two published theorems through the declared steps. -/
def authorText (path : String) : String :=
  "theorem relationValue (x : Bool) :\n" ++
  "    functionResult (t := .bool) (fnMeaning model installed member'fn0 (.cons x .nil)) = some x := by\n" ++
  "  kernel_rfl\n\n" ++
  s!"theorem judged : {path}.fees.judged.view := by\n" ++
  "  intro path input_claim valid_input_claim rejected\n" ++
  "  cases input_claim with\n" ++
  "  | true => exact False.elim (rejected (relationValue true))\n" ++
  "  | false =>\n" ++
  "    have shape : roleMeaning model installed rootMember verifierRole path\n" ++
  "        (.cons () (.cons false .nil)) =\n" ++
  "        .call (.own (.coin (.uniform (.fin 4))) [0] ⟨path, ⟨0⟩⟩ [] .nil (.fin 4))\n" ++
  "          (fun _ ↦ .halt (.declared .reject ⟨path, ⟨1⟩⟩)) := by kernel_rfl\n" ++
  "    rw [shape]\n" ++
  "    exact charged_free _ _ _ _ _ _ (fun _ _ ↦ True.intro)\n\n" ++
  s!"theorem {path}.sound : published% written'subject {path} sound :=\n" ++
  s!"  {path}.sound_of_installed ({path}.installed.view_iff.mpr ({path}.fees.installed_of_judged judged))\n\n" ++
  s!"theorem {path}.met : published% written'subject {path} met :=\n" ++
  s!"  {path}.met.view_iff.mp ⟨false, trivial, served, fun accepted => by\n" ++
  "    have := (relationValue false).symm.trans accepted\n" ++
  "    simp at this⟩\n"

/-- The end of a module that says its fee facts: their names in order on one line, or `none`. -/
def factsLine : String :=
  "  let names := (facts.toArray.qsort (·.toString < ·.toString)).toList.map toString\n" ++
  "  logInfo (\"fee facts: \" ++ if names.isEmpty then \"none\" else \" \".intercalate names)\n"

/-- A module that says which fee facts a fees module declared under a row's path. -/
def factsOf (space path : String) : String :=
  s!"import {space}.Fees\n\nopen Lean in\n#eval show CoreM Unit from do\n" ++
  s!"  let under := `{space}.{path}.fees\n" ++
  "  let facts := ((← getEnv).constants.toList.map (·.1)).filter (under.isPrefixOf ·)\n" ++ factsLine

def run (work : System.FilePath) : IO Unit := do
  let project := projectOf work
  let add (name text : String) (kind : SubjectProject.Kind) : IO Unit :=
    discard <| SubjectProject.add project name.toName text kind
  let result (name : String) := SubjectProject.result project name.toName
  let source ← IO.FS.readFile "fixtures/written-bound-guard.zkc"
  let path := "guard_bound.loose"
  let fees (space : String) := s!"import {space}.Stated\nimport ZkcFormal.Written.FeeFacts\n\npublish_fees {space}.written'subject\n"
  let views (space : String) := s!"import {space}.Stated\nimport ZkcFormal.Written.Views\n\npublish_views {space}.written'subject\n"
  let proof (space : String) :=
    s!"import {space}.Views\nimport {space}.Fees\nimport ZkcFormal.Written.Publish\n\n" ++ opens ++
      s!"namespace {space}\n\n" ++ authorText path ++ s!"\nend {space}\n"
  -- a subject with its challenge, its views, its fee facts and the author's text
  let subject (space stated : String) (judged : Bool) : IO Unit := do
    add s!"{space}.Stated" stated .statements
    add s!"{space}.Views" (views space) .statements
    add s!"{space}.Fees" (fees space) .statements
    add s!"{space}Facts" (factsOf space path) .statements
    add s!"{space}.Proof" (proof space) .module
    if judged then
      add s!"{space}.Challenge"
        s!"import {space}.Stated\nimport ZkcFormal.Written.Publish\n\npublish_goals {space}.written'subject\n" .challenge
      SubjectProject.expect project space [(s!"{space}.Challenge".toName, s!"{space}.Proof".toName)]
        [s!"{space}.{path}.sound".toName, s!"{space}.{path}.met".toName] WrittenSubject.allowed
  let atBound ← statementsOf source ["loose"] "AtBound"
  subject "AtBound" atBound true
  let wider ← replaceOnce source "stage = written) <= 1 / 4" "stage = written) <= 1 / 2"
  subject "Below" (← statementsOf wider ["loose"] "Below") true
  -- a bound in other numbers than the budget's (the issuer writes a bound in lowest terms, so the
  -- statements' bound is rewritten): the fact `budget` is at the bound's own numbers
  let bound := "def written'bound0 : Zkc.Subject.Bound := "
  add "Unreduced.Stated" (← replaceOnce (← statementsOf source ["loose"] "Unreduced")
    (bound ++ "⟨1, 4, by decide⟩") (bound ++ "⟨2, 8, by decide⟩")) .statements
  add "Unreduced.Fees" (fees "Unreduced") .statements
  add "UnreducedFacts" (factsOf "Unreduced" path ++ s!"#check @Unreduced.{path}.fees.budget\n") .statements
  let above ← statementsOf source ["loose"] "Above"
  subject "Above" (← replaceOnce above (bound ++ "⟨1, 4, by decide⟩") (bound ++ "⟨1, 8, by decide⟩")) false
  let miscounted ← statementsOf source ["loose"] "Miscounted"
  subject "Miscounted" (← replaceOnce (← withoutTableFacts miscounted "loose")
    "1, 4, 1⟩) .nil)⟩]⟩" "1, 4, 2⟩) .nil)⟩]⟩") false
  -- two rows of one subject, the second's table miscounted
  let two := source ++ "goal other = soundness(Checked, stage = written) <= 1 / 4\n"
  let mixed ← statementsOf two ["loose", "other"] "Mixed"
  let caps1 := "def written'caps1 : Zkc.Subject.CapTable := "
  let some table := ((mixed.splitOn caps1).getD 1 "").splitOn "\n" |>.head?
    | throw (IO.userError "the second goal has no table of caps")
  add "Mixed.Stated" (← replaceOnce (← withoutTableFacts mixed "other") (caps1 ++ table)
    (caps1 ++ table.replace "1, 4, 1⟩) .nil)⟩]⟩" "1, 4, 2⟩) .nil)⟩]⟩")) .statements
  add "Mixed.Fees" (fees "Mixed") .statements
  add "MixedFacts" ("import Mixed.Fees\n\nopen Lean in\n#eval show CoreM Unit from do\n" ++
    "  let facts := ((← getEnv).constants.toList.map (·.1)).filter fun n =>\n" ++
    "    (`Mixed.guard_bound).isPrefixOf n && (n.toString.splitOn \".fees.\").length > 1\n" ++ factsLine) .statements
  -- the judgment's view, read by name and type from a second reading of the source
  let rows ← ViewRows.expectedRows source "loose" false
  add "AtBoundReads" (ViewRows.reader ["AtBound.Fees"]
    [(s!"AtBound.{path}.fees.judged.view", "AtBound.written'subject", rows)]) .statements
  add "AtBoundPrint" (s!"import AtBound.Fees\n\n#print AtBound.{path}.fees.judged.view\n" ++
    s!"#check @AtBound.{path}.fees.budget\n#check @AtBound.{path}.fees.installed_of_judged\n") .statements
  add "BelowPrint" (s!"import Below.Fees\n\n#check @Below.{path}.fees.budget\n" ++
    s!"#check @Below.{path}.fees.installed_of_judged\n") .statements
  -- what Lean says
  for name in ["AtBound.Fees", "AtBoundFacts", "AtBoundReads", "AtBoundPrint", "Below.Fees", "BelowFacts",
      "BelowPrint", "Unreduced.Fees", "UnreducedFacts", "Above.Fees", "AboveFacts", "Miscounted.Fees", "MiscountedFacts", "Mixed.Fees", "MixedFacts"] do
    let (ok, output) ← result name
    unless ok do throw (IO.userError s!"{name}: Lean refused the module\n{output}")
    IO.println s!"{name}: accepted\n{output}"
  let said (name : String) (texts : List String) : IO Unit := do
    let output := (← result name).2
    for text in texts do
      unless output.contains text do throw (IO.userError s!"{name}: Lean did not say `{text}`\n{output}")
  -- the line of a facts module: the whole list, and no fact after it
  let facts (name : String) (names : List String) : IO Unit := do
    let output := (← result name).2
    let line := "fee facts: " ++ if names.isEmpty then "none" else " ".intercalate names
    unless (output.splitOn "\n").any (·.endsWith line) do
      throw (IO.userError s!"{name}: Lean did not say the line `{line}`\n{output}")
  let silent (name : String) (texts : List String) : IO Unit := do
    let output := (← result name).2
    for text in texts do
      if output.contains text then throw (IO.userError s!"{name}: Lean said `{text}`\n{output}")
  let all := ["budget", "counted", "installed_of_judged", "judged.view", "judged.view_iff", "total_eq_limit"]
  facts "AtBoundFacts" (all.map (s!"AtBound.{path}.fees.{·}"))
  said "AtBoundPrint" ["AtBound.written'caps0.budget = ↑1 / ↑4"]
  facts "BelowFacts" ((all.filter (· != "total_eq_limit")).map (s!"Below.{path}.fees.{·}"))
  said "BelowPrint" ["Below.written'caps0.budget = ↑1 / ↑4", "Below.written'bound0.limit"]
  facts "UnreducedFacts" (all.map (s!"Unreduced.{path}.fees.{·}"))
  said "UnreducedFacts" ["Unreduced.written'caps0.budget = ↑2 / ↑8"]
  facts "AboveFacts" []
  said "Above.Fees" [s!"publish_fees: {path}: the budget of Above.written'caps0 is above the bound 1/8; no fee facts"]
  facts "MiscountedFacts" []
  said "Miscounted.Fees" [s!"publish_fees: {path}: the table Miscounted.written'caps0 does not count as the stored program; no fee facts"]
  said "Mixed.Fees" ["publish_fees: guard_bound.other: the table Mixed.written'caps1 does not count as the stored program; no fee facts"]
  facts "MixedFacts" (all.map (s!"Mixed.{path}.fees.{·}"))
  silent "Mixed.Fees" [s!"publish_fees: {path}:"]
  -- the author's text: judged where the facts are, refused at the judgment's view where they are not
  for space in ["AtBound", "Below"] do
    let (ok, output) ← result s!"{space}.Proof"
    unless ok do throw (IO.userError s!"{space}: Lean refused the author's text\n{output}")
    let (verdict, words) ← SubjectProject.judge project space
    unless verdict == .accepted do
      throw (IO.userError s!"{space}: the proof through the fee facts was not accepted\n{words}")
    IO.println s!"{space}: judgment {verdict.word}"
  for space in ["Above", "Miscounted"] do
    let (ok, output) ← result s!"{space}.Proof"
    expectErrorsAt s!"{space}: the author's text without fee facts" ok output
      [s!"Unknown identifier `{path}.fees.judged.view`", "Tactic `introN` failed",
        s!"Unknown identifier `{path}.fees.installed_of_judged`"]
    IO.println s!"{space}.Proof: refused\n{output}"
  IO.println ("Fee facts by the library's command: at the bound and above the budget the facts are " ++
    "declared, the judgment's view is read by name and type, and the proof through them is accepted by " ++
    "lake comparator; a bound below the budget and a miscounted table get no facts, row by row.")

end WrittenFees

#eval show IO Unit from do
  match ← IO.getEnv "ZKC_WORK" with
  | some work => WrittenFees.run work
  | none => IO.FS.withTempDir WrittenFees.run
