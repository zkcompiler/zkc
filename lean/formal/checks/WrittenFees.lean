import ZkcFormalTests.WrittenSubject
import ZkcFormalTests.ViewRows

/-!
Fee facts declared by the library's command over a subject, decided row by row, and proofs by
fees closed through them. A fees module is its imports and `publish_fees S`.

Sources. The first three are judged by the comparator; the fourth's text is refused by Lean:

* The guarded verifier of the bound checks (`fixtures/written-bound-guard.zkc`: one draw at one
  over four, a claim that is not set is rejected), its goal at one over four: the command
  declares `counted`, `budget` (at the bound's numbers), `total_eq_limit`, the view of the
  judgment within that budget with its `view_iff`, and `installed_of_judged`; the reader of names
  and types reads the view. An author's proof of the judgment on its view, closed by
  `installed_of_judged` and the views' `sound_of_installed`, is judged by `lake comparator`
  through the published theorems. On the rejected input that verifier's draw is followed for
  free.
* The same with the goal at one over two, above the budget: `budget` is at the table's numbers,
  there is no `total_eq_limit`, and the same text closes at the goal's bound and is judged.
* A verifier that draws twice and returns, with the caps one and zero at its two draws: the
  author pays the whole fee at the first draw, within the cap that the judgment's term reads from
  the table, and the proof is judged. With the two caps exchanged in the source, the same text is
  refused at the first draw's allowance.

Rows that the issuer does not print, built as typed rows over the first subject's root, clauses
and origins:

* a bound in other numbers than the budget's (two over eight): `budget` is at the bound's
  numbers, with `total_eq_limit`; a table of caps that is an expression and no constant: the six
  facts; a row with a proof argument: the six facts;
* a bound below the budget, a table whose count is not the stored program's with its budget
  within the bound, and one with its budget above it: no fee facts and a line with the reason,
  each row by itself, and the row after them has its six facts; the author's text on such a row
  is refused at the judgment's view and at the step from it, which are not declared;
* a row of a property that publishes nothing, a bound that is no constant, one path twice (the
  first of the two rows without facts) and a table whose count the kernel does not evaluate: the
  command is refused by one error.

The scope of the caller: inside a name space and a section, with a local instance of classical
decidability at a high priority, local notations for the interpretation's names, a variable named
like an input and a printing option, the command declares the same six facts with the same terms.

With `ZKC_WORK` naming a folder the check's project is kept there.
-/

open Zkc.Frontend Zkc.Frontend.Written Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace WrittenFees

/-- What the issuer publishes for the goals of a source, in the name space `space`. -/
def publicationOf (text : String) (goals : List String) (space : String) : IO Publication := do
  let assembly ← Driver.assembleFiles ⟨"source.zkc", Syntax.parseString "source.zkc" text⟩
    ["../../libraries"]
  let some first := goals.head? | throw (IO.userError "no goal")
  let root ← IO.ofExcept (admitSoundnessGoal assembly first)
  let claims ← IO.ofExcept (goalClaims root goals)
  let issued ← IO.ofExcept ((⟨claims, claims.functionsBeforeRoot⟩ : Statements).publication space)
  unless issued.refusals.isEmpty do throw (IO.userError s!"{issued.refusals}")
  return issued

/-- A verifier that draws twice and returns whatever the claim, with a cap at each draw. -/
def payingSource (first second : String) : String :=
  "module guard_bound\nuse zkc::security::{soundness}\n\n" ++
  "relation IsSet(claim: bool): claim\n" ++
  "protocol Check roles(P,V)(hidden: bool @P, claim: bool @(P,V)):\n" ++
  "    r <- draw index<4> from V to P\n    s <- draw index<4> from V to P\n    guard @V true\n" ++
  s!"spec for Check:\n    proves @V IsSet(claim)\n    charge sites.r <= {first}\n    charge sites.s <= {second}\n" ++
  "scheme Checked = Check:\n    prover P\n    construction interactive\n" ++
  "goal loose = soundness(Checked, stage = written) <= 1\n"

def opens : String :=
  "open Zkc.Core ZkcFormal ZkcFormal.ProbabilisticProcess ZkcFormal.Written OracleComp ProbComp\n" ++
  "open scoped NNRat ENNReal\n" ++
  "open ZkcFormal.Written.StandardInterpretation (model served draws covers)\n"

/-- The guarded verifier's judgment, after the input is introduced: on the rejected input the
draw is followed for free. -/
def guardedJudgment : String :=
  "  cases input_claim with\n" ++
  "  | true => exact False.elim (rejected (relationValue true))\n" ++
  "  | false =>\n" ++
  "    have shape : roleMeaning model installed rootMember verifierRole path\n" ++
  "        (.cons () (.cons false .nil)) =\n" ++
  "        .call (.own (.coin (.uniform (.fin 4))) [0] ⟨path, ⟨0⟩⟩ [] .nil (.fin 4))\n" ++
  "          (fun _ ↦ .halt (.declared .reject ⟨path, ⟨1⟩⟩)) := by kernel_rfl\n" ++
  "    rw [shape]\n" ++
  "    exact charged_free _ _ _ _ _ _ (fun _ _ ↦ True.intro)\n"

/-- The paying verifier's judgment: the whole fee is paid at the first draw, every reply of which
is excluded; the cap of that draw is read from the table. -/
def payingJudgment : String :=
  "  have shape : roleMeaning model installed rootMember verifierRole path\n" ++
  "      (.cons () (.cons input_claim .nil)) =\n" ++
  "      .call (.own (.coin (.uniform (.fin 4))) [0] ⟨path, ⟨0⟩⟩ [] .nil (.fin 4))\n" ++
  "        (fun _ ↦ .call (.own (.coin (.uniform (.fin 4))) [0] ⟨path, ⟨1⟩⟩ [] .nil (.fin 4))\n" ++
  "          (fun _ ↦ .done .nil)) := by cases input_claim <;> kernel_rfl\n" ++
  "  rw [shape]\n" ++
  "  apply charged_pay_at (rest := []) (key := ⟨0⟩) (fee := 1) (excluded := fun _ => True)\n" ++
  "  · simp [ROp.occurrence]\n" ++
  "  · rfl\n" ++
  "  · simp [toProbability]\n" ++
  "  · decide +kernel\n" ++
  "  · decide +kernel\n" ++
  "  · intro _ _ h\n" ++
  "    exact (h trivial).elim\n"

/-- An author's text for the goal at `path` of the subject `subject`: the judgment by fees proved
on its declared view, and the two published theorems through the declared steps. -/
def authorText (subject path judgment : String) : String :=
  "theorem relationValue (x : Bool) :\n" ++
  "    functionResult (t := .bool) (fnMeaning model installed member'fn0 (.cons x .nil)) = some x := by\n" ++
  "  kernel_rfl\n\n" ++
  s!"theorem judged : {path}.fees.judged.view := by\n" ++
  "  intro path input_claim valid_input_claim rejected\n" ++ judgment ++ "\n" ++
  s!"theorem {path}.sound : published% {subject} {path} sound :=\n" ++
  s!"  {path}.sound_of_installed ({path}.installed.view_iff.mpr ({path}.fees.installed_of_judged judged))\n\n" ++
  s!"theorem {path}.met : published% {subject} {path} met :=\n" ++
  s!"  {path}.met.view_iff.mp ⟨false, trivial, served, fun accepted => by\n" ++
  "    have := (relationValue false).symm.trans accepted\n" ++
  "    simp at this⟩\n"

/-- The end of a module that says its fee facts: their names in order on one line, or `none`. -/
def factsLine : String :=
  "  let names := (facts.toArray.qsort (·.toString < ·.toString)).toList.map toString\n" ++
  "  logInfo (\"fee facts: \" ++ if names.isEmpty then \"none\" else \" \".intercalate names)\n"

/-- A module that says which fee facts the module `fees` declared under a name. -/
def factsOf (fees under : String) : String :=
  s!"import {fees}\n\nopen Lean in\n#eval show CoreM Unit from do\n" ++
  s!"  let under := `{under}\n" ++
  "  let facts := ((← getEnv).constants.toList.map (·.1)).filter (under.isPrefixOf ·)\n" ++ factsLine

/-- The typed rows over the first subject: fields and rows that the issuer does not print, and a
subject of them in their order. The literal of the table is held to the issued table. -/
def typedRows : String :=
  "import AtBound.Stated\n\nnamespace Rows\nopen AtBound\n\n" ++
  "def table (count : Nat) : Zkc.Subject.CapTable := ⟨[⟨⟨1⟩, .item (.draw ⟨⟨0⟩, 1, 4, count⟩) .nil⟩]⟩\n" ++
  "example : table 1 = written'caps0 := rfl\n" ++
  "def twoEighths : Zkc.Subject.Bound := ⟨2, 8, by decide⟩\n" ++
  "def oneEighth : Zkc.Subject.Bound := ⟨1, 8, by decide⟩\n" ++
  "def countZero : Zkc.Subject.CapTable := table 0\n" ++
  "def countTwo : Zkc.Subject.CapTable := table 2\n" ++
  "noncomputable def row (name : String) (fields : Zkc.Subject.GoalFields) :\n" ++
  "    Zkc.Subject.GoalSlot written'clauses.size :=\n" ++
  "  { path := [name], property := Zkc.Security.Property.soundness, clause := ⟨0, by decide⟩, fields }\n" ++
  "noncomputable def unreducedRow := row \"unreduced\" { specification := [], caps := written'caps0, bound := twoEighths }\n" ++
  "noncomputable def inPlaceRow := row \"inPlace\"\n" ++
  "  { specification := [], caps := table 1, bound := written'bound0 }\n" ++
  "noncomputable def arguedRow := row \"argued\" { specification := [7], caps := written'caps0, bound := written'bound0 }\n" ++
  "noncomputable def aboveRow := row \"above\" { specification := [], caps := written'caps0, bound := oneEighth }\n" ++
  "noncomputable def miscountedRow := row \"miscounted\" { specification := [], caps := countZero, bound := written'bound0 }\n" ++
  "noncomputable def overcountedRow := row \"overcounted\" { specification := [], caps := countTwo, bound := written'bound0 }\n" ++
  "noncomputable def lastRow := row \"last\" written'fields0\n" ++
  "noncomputable def subject : Zkc.Subject.WrittenSubject written'root :=\n" ++
  "  ⟨written'clauses, ⟨7, fun i => if i.val == 0 then unreducedRow else if i.val == 1 then inPlaceRow\n" ++
  "    else if i.val == 2 then arguedRow else if i.val == 3 then aboveRow else if i.val == 4 then miscountedRow\n" ++
  "    else if i.val == 5 then overcountedRow else lastRow⟩, written'origins⟩\n\n" ++
  "-- a row of a property that publishes nothing; a bound that is no constant\n" ++
  "noncomputable def completeRow : Zkc.Subject.GoalSlot written'clauses.size :=\n" ++
  "  { row \"complete\" written'fields0 with property := Zkc.Security.Property.completeness }\n" ++
  "noncomputable def complete : Zkc.Subject.WrittenSubject written'root :=\n" ++
  "  ⟨written'clauses, ⟨1, fun _ => completeRow⟩, written'origins⟩\n" ++
  "noncomputable def boundInPlaceRow :=\n" ++
  "  row \"boundInPlace\" { specification := [], caps := written'caps0, bound := ⟨1, 4, by decide⟩ }\n" ++
  "noncomputable def boundInPlace : Zkc.Subject.WrittenSubject written'root :=\n" ++
  "  ⟨written'clauses, ⟨1, fun _ => boundInPlaceRow⟩, written'origins⟩\n" ++
  "-- one path twice, the first row without facts\n" ++
  "noncomputable def twin : Zkc.Subject.WrittenSubject written'root :=\n" ++
  "  ⟨written'clauses, ⟨2, fun i => if i.val == 0 then { aboveRow with path := [\"same\"] } else\n" ++
  "    row \"same\" written'fields0⟩, written'origins⟩\n" ++
  "-- a table whose count the kernel cannot evaluate\n" ++
  "opaque unknown : Nat\n" ++
  "noncomputable def unknownRow := row \"unknown\" { specification := [], caps := table unknown, bound := written'bound0 }\n" ++
  "noncomputable def uncounted : Zkc.Subject.WrittenSubject written'root :=\n" ++
  "  ⟨written'clauses, ⟨1, fun _ => unknownRow⟩, written'origins⟩\n\n" ++
  "end Rows\n"

/-- The scope of a caller around a command: a name space and a section, a local instance of
classical decidability at a high priority, local notations for the interpretation's names, a
variable named like an input, and a printing option. -/
def scope : String :=
  "namespace Customer\nsection\n" ++
  "variable (input_claim : Nat)\nlocal notation \"model\" => Unit\nlocal notation \"draws\" => False\n" ++
  "attribute [local instance 2000] Classical.propDecidable\nset_option pp.universes true in\n"

def run (work : System.FilePath) : IO Unit := do
  let project := projectOf work
  let add (name text : String) (kind : SubjectProject.Kind) : IO Unit :=
    discard <| SubjectProject.add project name.toName text kind
  let result (name : String) := SubjectProject.result project name.toName
  let path := "guard_bound.loose"
  let command (name : String) (imports : List String) (subject : String) (before := "") :=
    String.join (imports.map (s!"import {·}\n")) ++ s!"\n{before}{name} {subject}\n"
  -- a source as the issuer publishes it (the data module, the challenge, the views and the fees
  -- module), with the author's text in the issuer's frame, judged
  let sourced (space text judgment : String) (judged := true) : IO Unit := do
    let issued ← publicationOf text ["loose"] space
    add (toString issued.dataName) issued.data .statements
    add (toString issued.challengeName) issued.challenge .challenge
    add (toString issued.viewsName) issued.views .statements
    add (toString issued.feesName) issued.fees .statements
    add s!"{space}Facts" (factsOf s!"{space}.Fees" s!"{space}.{path}.fees" ++
      s!"#check @{space}.{path}.fees.budget\n#check @{space}.{path}.fees.installed_of_judged\n") .statements
    add s!"{space}.Proof" (issued.proof (authorText "written'subject" path judgment)) .module
    unless issued.published == [s!"{space}.{path}.sound".toName, s!"{space}.{path}.met".toName] do
      throw (IO.userError s!"{space}: the issuer's published theorems are {issued.published}")
    if judged then
      SubjectProject.expect project space [(issued.challengeName, s!"{space}.Proof".toName)]
        issued.published WrittenSubject.allowed
  let source ← IO.FS.readFile "fixtures/written-bound-guard.zkc"
  sourced "AtBound" source guardedJudgment
  sourced "Below" (← replaceOnce source "stage = written) <= 1 / 4" "stage = written) <= 1 / 2") guardedJudgment
  sourced "Paying" (payingSource "1" "0") payingJudgment
  sourced "Exchanged" (payingSource "0" "1") payingJudgment (judged := false)
  -- the judgment's view, read by name and type from a second reading of the source
  let rows ← ViewRows.expectedRows source "loose" false
  add "AtBoundReads" (ViewRows.reader ["AtBound.Fees"]
    [(s!"AtBound.{path}.fees.judged.view", "AtBound.written'subject", rows)]) .statements
  -- the typed rows
  add "Rows.Typed" typedRows .statements
  add "Rows.Views" (command "publish_views" ["Rows.Typed", "ZkcFormal.Written.Views"] "Rows.subject") .statements
  add "Rows.Fees" (command "publish_fees" ["Rows.Typed", "ZkcFormal.Written.FeeFacts"] "Rows.subject") .statements
  let typed := ["unreduced", "inPlace", "argued", "above", "miscounted", "overcounted", "last"]
  for name in typed do
    add s!"Rows{name}Facts" (factsOf "Rows.Fees" s!"Rows.{name}.fees" ++
      (if name == "unreduced" then "#check @Rows.unreduced.fees.budget\n" else "")) .statements
  for name in ["above", "miscounted"] do
    add s!"Rows.{name}Proof" ("import Rows.Views\nimport Rows.Fees\nimport ZkcFormal.Written.Publish\n\n" ++ opens ++
      "namespace Rows\nopen AtBound\n\n" ++ authorText "subject" name guardedJudgment ++ "\nend Rows\n") .module
  add "CompleteFees" (command "publish_fees" ["Rows.Typed", "ZkcFormal.Written.FeeFacts"] "Rows.complete") .statements
  add "BoundInPlaceFees" (command "publish_fees" ["Rows.Typed", "ZkcFormal.Written.FeeFacts"] "Rows.boundInPlace") .statements
  add "TwinFees" (command "publish_fees" ["Rows.Typed", "ZkcFormal.Written.FeeFacts"] "Rows.twin") .statements
  add "UncountedFees" (command "publish_fees" ["Rows.Typed", "ZkcFormal.Written.FeeFacts"] "Rows.uncounted") .statements
  -- the caller's scope around the command, and the terms printed in full with it and without it
  add "Scoped.Fees" (command "publish_fees" ["AtBound.Stated", "ZkcFormal.Written.FeeFacts"] "AtBound.written'subject"
    (before := scope)) .statements
  let printAll (fees : String) : String :=
    s!"import {fees}\n\nset_option pp.all true\n" ++
      String.join (["counted", "budget", "total_eq_limit", "judged.view", "judged.view_iff", "installed_of_judged"].map
        fun fact => s!"#print AtBound.{path}.fees.{fact}\n")
  add "PrintPlain" (printAll "AtBound.Fees") .statements
  add "PrintScoped" (printAll "Scoped.Fees") .statements
  add "ScopedFacts" (factsOf "Scoped.Fees" s!"AtBound.{path}.fees") .statements
  -- what Lean says
  let accepted := ["AtBound.Fees", "AtBoundFacts", "AtBoundReads", "Below.Fees", "BelowFacts", "Paying.Fees",
    "PayingFacts", "Exchanged.Fees", "ExchangedFacts", "Rows.Views", "Rows.Fees", "Scoped.Fees", "ScopedFacts",
    "PrintPlain", "PrintScoped"] ++ typed.map (s!"Rows{·}Facts")
  for name in accepted do
    let (ok, output) ← result name
    unless ok do throw (IO.userError s!"{name}: Lean refused the module\n{output}")
    IO.println s!"{name}: accepted\n{output}"
  let said (name : String) (texts : List String) : IO Unit := do
    let output := (← result name).2
    for text in texts do
      unless output.contains text do throw (IO.userError s!"{name}: Lean did not say `{text}`\n{output}")
  -- the line of a facts module: the whole list, and no fact after it
  let facts (name under : String) (names : List String) : IO Unit := do
    let output := (← result name).2
    let line := "fee facts: " ++ if names.isEmpty then "none" else " ".intercalate (names.map (s!"{under}.fees.{·}"))
    unless (output.splitOn "\n").any (·.endsWith line) do
      throw (IO.userError s!"{name}: Lean did not say the line `{line}`\n{output}")
  let all := ["budget", "counted", "installed_of_judged", "judged.view", "judged.view_iff", "total_eq_limit"]
  let unequal := all.filter (· != "total_eq_limit")
  facts "AtBoundFacts" s!"AtBound.{path}" all
  said "AtBoundFacts" ["AtBound.written'caps0.budget = ↑1 / ↑4", "AtBound.written'bound0.limit"]
  facts "BelowFacts" s!"Below.{path}" unequal
  said "BelowFacts" ["Below.written'caps0.budget = ↑1 / ↑4", "Below.written'bound0.limit"]
  facts "PayingFacts" s!"Paying.{path}" all
  said "PayingFacts" ["Paying.written'caps0.budget = ↑1 / ↑1"]
  facts "ExchangedFacts" s!"Exchanged.{path}" all
  -- the typed rows, each by itself
  facts "RowsunreducedFacts" "Rows.unreduced" all
  said "RowsunreducedFacts" ["AtBound.written'caps0.budget = ↑2 / ↑8"]
  facts "RowsinPlaceFacts" "Rows.inPlace" all
  facts "RowsarguedFacts" "Rows.argued" all
  facts "RowsaboveFacts" "Rows.above" []
  facts "RowsmiscountedFacts" "Rows.miscounted" []
  facts "RowsovercountedFacts" "Rows.overcounted" []
  facts "RowslastFacts" "Rows.last" all
  let (_, rowsSaid) ← result "Rows.Fees"
  let lines := (rowsSaid.splitOn "\n").filter (·.contains "publish_fees: ")
  let reasons := [
    "publish_fees: above: the budget of AtBound.written'caps0 is above the bound 1/8; no fee facts",
    "publish_fees: miscounted: the table Rows.countZero does not count as the stored program; no fee facts",
    "publish_fees: overcounted: the table Rows.countTwo does not count as the stored program; no fee facts"]
  unless lines.length == reasons.length && (lines.zip reasons).all (fun (line, reason) => line.endsWith reason) do
    throw (IO.userError s!"the fee facts of the typed rows: the lines are not the three reasons, in order\n{rowsSaid}")
  -- the subjects that the command refuses, each by one error
  expectErrorsAt "a row of a property that publishes nothing" (← result "CompleteFees").1 (← result "CompleteFees").2
    ["publish: the written subject publishes nothing for the property Zkc.Security.Property.completeness"]
  expectErrorsAt "a bound that is no constant" (← result "BoundInPlaceFees").1 (← result "BoundInPlaceFees").2
    ["publish: expected a constant"]
  expectErrorsAt "one path twice, the first row without facts" (← result "TwinFees").1 (← result "TwinFees").2
    ["publish: the path [same] is the path of two rows of Rows.twin"]
  expectErrorsAt "a count that the kernel does not evaluate" (← result "UncountedFees").1 (← result "UncountedFees").2
    ["publish_fees: the kernel did not evaluate whether the table counts as the stored program"]
  -- the scope of the caller changes neither the facts nor their terms
  facts "ScopedFacts" s!"AtBound.{path}" all
  let printed (name : String) : IO String := do
    return "\n".intercalate (((← result name).2.splitOn "\n").map fun line =>
      match line.splitOn ": info: " with
      | [_, rest] => rest
      | _ => line)
  unless (← printed "PrintPlain") == (← printed "PrintScoped") do
    throw (IO.userError "the scope around the command changed a fee fact's term")
  IO.println "PrintPlain = PrintScoped: the six fee facts' terms (pp.all) are the same with the caller's scope around the command"
  -- the authors' texts: judged where the facts are and the fee is within its cap
  for space in ["AtBound", "Below", "Paying"] do
    let (ok, output) ← result s!"{space}.Proof"
    unless ok do throw (IO.userError s!"{space}: Lean refused the author's text\n{output}")
    let (verdict, words) ← SubjectProject.judge project space
    unless verdict == .accepted do
      throw (IO.userError s!"{space}: the proof through the fee facts was not accepted\n{words}")
    IO.println s!"{space}: judgment {verdict.word}"
  let (ok, output) ← result "Exchanged.Proof"
  expectErrorsAt "the fee paid at a draw whose cap is zero" ok output ["Tactic `decide` failed"]
  -- the obligation that fails is the fee of one against the cap of the first draw, the site 0
  unless output.contains "(1 ≤ written'caps0.capFrom written'caps0.root (Frame.applications []) { number := 0 })" do
    throw (IO.userError s!"the paying text is not refused at the first draw's allowance\n{output}")
  IO.println s!"Exchanged.Proof: refused\n{output}"
  for name in ["above", "miscounted"] do
    let (ok, output) ← result s!"Rows.{name}Proof"
    expectErrorsAt s!"{name}: the author's text without fee facts" ok output
      [s!"Unknown identifier `{name}.fees.judged.view`", "Tactic `introN` failed",
        s!"Unknown identifier `{name}.fees.installed_of_judged`"]
    IO.println s!"Rows.{name}Proof: refused\n{output}"
  IO.println ("Fee facts by the library's command: at the bound and above the budget the facts are " ++
    "declared, the judgment's view is read by name and type, and the proofs through them (a draw followed " ++
    "for free; a fee paid within its cap) are accepted by lake comparator; a fee above its cap is refused; " ++
    "typed rows get their facts or a reason, each by itself; the caller's scope changes nothing.")

end WrittenFees

#eval show IO Unit from do
  match ← IO.getEnv "ZKC_WORK" with
  | some work => WrittenFees.run work
  | none => IO.FS.withTempDir WrittenFees.run
