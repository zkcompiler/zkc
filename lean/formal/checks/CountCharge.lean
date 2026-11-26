import ZkcFormalTests.WrittenSubject
import Zkc.Tests.Frontend.SyntaxHarness

/-! Source charges, coverage, and the exact probabilities attained at the two tables. -/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Subject (CapTable)
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport
open ZkcFormalTests ZkcFormalTests.WrittenSubject

namespace CountCharge

/-- What the check asserts of what the frontend read of a source of the subject: both goals
select one root; each reads the clause `proves @V NearZero(xs)`, decided by the verifier of the
scheme, on the only port of the protocol; each gives one proof argument, the tolerance; and
the coins draw uniform positions. What the two claim is
one package, and the table of caps of each goal is read with its claim. -/
def reading : Reading where
  goals := ["loose", "strict"]
  ports := #["xs"]
  clause := ⟨"proves", none, "V", "NearZero", ["xs"], []⟩
  operands := #[0]
  arguments := 1

/-- A source of the subject read, with what is asserted of the reading. -/
def read (text : String) : IO Subject := WrittenSubject.read text reading

/-- The root, the verifier and the prover of a subject. -/
def places (s : Subject) : Nat × Nat × Nat :=
  (s.statements.claims.root, s.statements.claims.verifier, s.statements.claims.prover)

/-- The name, the proof arguments and the table of caps of each goal. -/
def tables (s : Subject) : List (String × Array Nat × CapTable) :=
  s.goals.map fun goal => (goal.goal, goal.specification, goal.caps)

/-- The stored text of the definitions of the root's own package. -/
def deployed (s : Subject) : IO (List (Nat × String)) := do
  let c ← IO.ofExcept (goalRoot s.text "loose")
  let own := c.emission.package ⟨[], [], [], [], []⟩
  return own.named.definitions.map fun d => (d.key.number, storedDefinition (b := own.bindings) d)

/-- The source with its one occurrence of `before` replaced. -/
def edit (text before after : String) : IO String := replaceOnce text before after

def run (corpus template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let blocks := readBlocks (← IO.FS.readFile corpus)
  let some source := (blocks.find? (·.id == "N-GL2a")).bind (·.files[0]?)
    | throw (IO.userError "missing the reference case N-GL2a")
  let checks := template.parent.getD "."
  let template ← IO.FS.readFile template
  let written ← read source
  unless places written == (1, 1, 0) do
    throw (IO.userError "the root and the roles of the source are not where they were")
  -- The tables of caps, as the frontend read them: the one draw of the root, once, at the
  -- charge of each goal's tolerance.
  unless (tables written).map (·.2.2) ==
      [⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 3, 8, 1⟩] [])]⟩, ⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 3, 4, 1⟩] [])]⟩] do
    throw (IO.userError s!"the tables of caps are not the draw of the root at 3/8 and at 3/4: {repr ((tables written).map (·.2.2))}")

  -- The roster reversed: the verifier is the first role, and the key of the root is as it was.
  let turned ← read (← edit source "protocol Count roles(P, V)" "protocol Count roles(V, P)")
  unless places turned == (1, 0, 1) do
    throw (IO.userError "with the roster reversed the verifier is not the first role")
  unless tables turned == tables written do
    throw (IO.userError "with the roster reversed the goals changed")

  -- The relation changed: the deployed definitions and both tables are what they were, and the
  -- package of the claims has another function for the relation.
  let changed ← read (← edit source "else 1) <= e\n" "else 1) < e\n")
  unless (← deployed changed) == (← deployed written) && tables changed == tables written do
    throw (IO.userError "a change of the relation changed a deployed definition or a table of caps")
  if changed.package == written.package then
    throw (IO.userError "a change of the relation changed nothing in the package of the claims")

  -- Other sizes, read by the frontend alone. With five entries and the tolerance 4 a table
  -- outside the relation has no zero entry, and the charge is zero; with four entries the
  -- ceiling that the source writes is negative, and no charge is read.
  let five ← read (← edit source "scheme Checked = Count<8>:" "scheme Checked = Count<5>:")
  unless ((tables five).map fun (_, _, caps) => caps.ratio) == [0, (3 : Rat) / 5] do
    throw (IO.userError "the charges of Count<5> are not 0 and 3/5")
  let four ← edit source "scheme Checked = Count<8>:" "scheme Checked = Count<4>:"
  let .error refusal := (goalRoot four "loose").bind (goalClaims · ["loose"])
    | throw (IO.userError "a negative ceiling was read as a charge")
  unless refusal.contains "nonnegative" do
    throw (IO.userError s!"Count<4> was refused for another reason: {refusal}")

  -- A goal that states a ceiling. At the total of its table, 3/8, the statement is issued with the
  -- comparison, which the kernel decides; below it no statement is issued (GL4).
  let goalLine := "goal loose = soundness(Checked, spec e = 4)"
  let atTotal ← read (← edit source goalLine (goalLine ++ " <= 3/8"))
  let ceilingProof ← startLakeLean work "CeilingAtTotal"
    (← IO.ofExcept (atTotal.statements.ceilingModule "CeilingAtTotal")).text (text := false)
  let below ← read (← edit source goalLine (goalLine ++ " <= 1/4"))
  match below.statements.ceilings with
  | .ok _ => throw (IO.userError "a goal whose ceiling is below the total of its table was issued a statement")
  | .error why =>
    unless why.contains "GL4" && why.contains "1/4" && why.contains "3/8" do
      throw (IO.userError s!"the ceiling below the total was refused for another reason: {why}")

  -- The roles exchanged in the source: with `V` the prover of the scheme the verifier is `P`,
  -- and the clause, which `V` decides, is not decided by the verifier of the scheme.
  let exchanged ← edit source "scheme Checked = Count<8>:\n    prover P\n" "scheme Checked = Count<8>:\n    prover V\n"
  match (goalRoot exchanged "loose").bind (goalClaims · ["loose", "strict"]) with
  | .ok _ => throw (IO.userError "a goal whose clause is decided by the prover of its scheme was read")
  | .error why =>
    unless why.contains "GL3" && why.contains "the deciding role of the clause is the verifier of the scheme" do
      throw (IO.userError s!"the scheme with the roles exchanged was refused for another reason: {why}")

  -- The controls of the charge are sources: no caller gives a statement its table. In each the
  -- program is what it was, and the table of caps is another.
  -- The charge below the bound of each tolerance.
  let chargeLine := "        charge sites.z <= 1 - (e + 1) / n\n"
  let small ← read (← edit source chargeLine "        charge sites.z <= 1 - (e + 2) / n\n")
  -- The charge on a draw of a loop that does not run, which is not emitted.
  let elsewhere ← read (← edit
    (← edit source "        guard @V xs[z] == 0\n"
      "        guard @V xs[z] == 0\n        for j in 0..0:\n            y <- draw index<n> from V to P\n")
    chargeLine "        charge sites.y <= 1 - (e + 1) / n\n")
  -- The charge in the contract of another protocol, on its draw of the same name.
  let foreign ← read (← edit (← edit source chargeLine "")
    "    spec for Count:\n"
    ("    protocol Other roles(P, V)(xs: [F; n] @(P, V)):\n        z <- draw index<n> from V to P\n" ++
      "    spec for Other:\n" ++ chargeLine ++ "    spec for Count:\n"))
  for (title, control) in [("below the bound", small), ("on a loop that does not run", elsewhere),
      ("of another protocol", foreign)] do
    unless (← deployed control) == (← deployed written) do
      throw (IO.userError s!"the charge {title}: a deployed definition changed")
    if tables control == tables written then
      throw (IO.userError s!"the charge {title}: the tables of caps are what they were")
  unless (tables small).map (·.2.2) ==
      [⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 1, 4, 1⟩] [])]⟩, ⟨[(.flat ⟨1⟩ [⟨⟨0⟩, 5, 8, 1⟩] [])]⟩] do
    throw (IO.userError "the smaller charge is not 1/4 and 5/8 at the draw")
  for control in [elsewhere, foreign] do
    unless (tables control).all (·.2.2 == ⟨[(.flat ⟨1⟩ [] [])]⟩) do
      throw (IO.userError s!"a charge that is not on the draw of the root gave a cap: {repr ((tables control).map (·.2.2))}")
  -- A row outside the table of the model, inside the loop of the relation: the power of a field
  -- element, which the standard model gives a constant.
  let uncovered ← WrittenSubject.read
    (← edit source "if xs[i] == 0 then 0 else 1" "if xs[i] ^ 2 == 0 then 0 else 1")
    reading
  for issue in [(uncovered.statements.coverageModule "CoverageControl").map (fun _ => ()),
      (uncovered.statements.module "UncoveredControl" {}).map (fun _ => ())] do
    match issue with
    | .ok _ => throw (IO.userError "issued a statement for an uninterpreted power")
    | .error why => unless why.contains "pow" && why.contains "loose" && why.contains "strict" do
        throw (IO.userError why)

  -- Independently ask the kernel about the actual program, including the power in the relation.
  let testCoverage (goal : ClaimedGoal) := Statements.header (Statements.imports false) ++ "namespace CoverageControl\n" ++
    (Written.package uncovered.statements.package).text ++ statementOpens ++ uncovered.statements.facts ++
    Statements.coverage [goal] ++ "end CoverageControl\n"
  let coverageChecks ← uncovered.goals.mapM fun goal => do
    let checked ← startLakeLean work (goal.goal ++ "CoverageControl") (testCoverage goal) (text := false)
    return (goal.goal, checked)
  let names := ["loose_exact", "strict_exact", "loose_within", "strict_within",
    "Witness.loose_attained", "Witness.strict_attained", "Witness.misplaced_not_counted",
    "Witness.foreign_not_counted", "Witness.fixed_position_does_not_follow"]
  let count ← written.module "Count" { text := template, theorems := [] }
  let lemmas ← startLemmas work "Count" count template names written
  let reversed ← turned.module "CountTurned" { text := template, theorems := [] }
  let other ← startLemmas work "CountTurned" reversed template names turned
  let caps ← [("BoundControl", small), ("SiteControl", elsewhere), ("OwnerControl", foreign)].mapM
    fun (name, subject) => do
      let m ← subject.module name { text := template, theorems := [] }
      startLemmas work name m template names (refusal := ["drawCap looseCaps =", "drawCap strictCaps ="])
        (unproved := ["loose_exact", "strict_exact", "Witness.loose_attained", "Witness.strict_attained"])
  let altered ← changed.module "RelationControl" { text := template, theorems := [] }
  let verifier ← startLemmas work "RelationControl" altered template names
  let roots ← startLakeLean work "CountBoundRoots" (← IO.FS.readFile (checks / "CountBoundRoots.lean.in")) (text := false)
  let endpoints ← startLakeLean work "CountBounds" (← IO.FS.readFile (checks / "CountBounds.lean.in"))
  lemmas
  other
  verifier
  caps.forM id
  acceptedByLean "CountBoundRoots" (← roots)
  acceptedByLean "CountBounds" (← endpoints)
  let (ok, output) ← finishLean ceilingProof
  acceptedOutput "CeilingAtTotal" ok output ["loose_ceiling"] allowed
  for (goal, checked) in coverageChecks do
    let (covered, reason) ← finishLean checked
    if covered then throw (IO.userError s!"accepted the power in the relation of {goal}")
    unless reason.contains s!"covers stored rootKey {goal}Key = true" && reason.contains "is false" do
      throw (IO.userError reason)

end CountCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work =>
    CountCharge.run "../../language/conformance/layer-b.txt" "checks/CountCharge.lean.in" work
