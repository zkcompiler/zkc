import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Written.Package
import Zkc.Tests.Frontend.SyntaxHarness
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Core.Admission.Theorems
import Zkc.Kernel
import Zkc.Vocabulary.Project
import Zkc.Formal

/-!
An admitted protocol judged within the charges that its source declares, and the judgment taken
to a probability.

The subject is the reference case `N-GL2a`: `Count<8>` draws a position of a table of eight
field elements and returns when the entry there is zero; its relation holds of a table with at
most `e` entries that are not zero, and its charge on the draw is `1 - (e + 1) / n`. Two goals
give `e` the values 4 and 1.

The check reads the source with the frontend and writes two modules, on which Lean is run.

- The proof module has the printed package of the root, what was read from the source as terms
  (the key of the root, the roles, and for each goal the value of its proof argument and its
  charge on the draw), and the text of `CountCharge.lean.in`. It imports nothing of the
  frontend but the record of a charge. Its theorems are about every program that admission
  gives for the stored program of the package: the verifier is judged never to return on a
  table outside the relation,
  within the budget of the goal's charge and with each fee within what the charge allows the
  effect that pays it; against every service that draws the position uniformly, it returns
  with probability at most the total of the charge. For each goal a concrete table and a
  service meet every hypothesis, and there the verifier returns with probability exactly the
  total of the charge; a charge on another instruction, and a charge of another definition,
  judge it at no budget.
- The comparison module has the same printed package and the frontend: the program by names
  and the association that Lean reads from the package are those that the frontend gave to
  admission for the root that the goal selects.

What the source says and the proof module takes as given is asserted here against the source:
the clause that each goal reads, by `goalClause`; the port that the relation is applied to; and
the line of the relation, which the proof module binds by hand. Two more subjects show what the
check distinguishes. With the roster reversed the verifier is the first role, and the same text
proves the same theorems. With `<=` of the relation changed to `<`, the package and both charges
are what they were, and only the assertion of the relation's line refuses the source: nothing
in a package says what a relation means.

Four controls are refused by Lean, each for the theorems that depend on what it changes: the
roles exchanged, a charge below the bound of its tolerance, a charge on another instruction,
and a charge of another definition. Two other sizes are read by the frontend alone: the charge
of `Count<5>` at the tolerance 4 is zero, and the negative ceiling of `Count<4>` is no charge.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

namespace CountCharge

/-- What a goal gives: the value of its proof argument, and its charge on the draw. -/
structure Goal where
  name : String
  tolerance : Nat
  charge : DrawCharge
  deriving DecidableEq

/-- What the check reads of a source. -/
structure Subject where
  text : String
  root : Nat
  verifier : Nat
  prover : Nat
  /-- The name, in the package, of the program before the root. -/
  callees : String
  package : String
  goals : List Goal

def noAssociation : Association := ⟨[], [], [], [], []⟩

/-- The relation as the proof module reads it. -/
def relationLine := "    relation NearZero(xs: [F; n]): (∑ i ∈ 0..n, if xs[i] == 0 then 0 else 1) <= e\n"

/-- The source with its one occurrence of `before` replaced. -/
def edit (text before after : String) : IO String := do
  unless (text.splitOn before).length == 2 do
    throw (IO.userError s!"expected one occurrence of {before}")
  return text.replace before after

/-- A source read: both goals select one root; each reads the clause `proves @V NearZero(xs)`,
decided by the verifier of the scheme, on the only port of the protocol; each gives one proof
argument; each has a charge on the draw `z`. -/
def read (text : String) : IO Subject := do
  let c ← IO.ofExcept (goalRoot text "loose")
  let head ← IO.ofExcept (SourceClause.rootHead c)
  unless head.ports.map (·.binder.name) == #["xs"] do
    throw (IO.userError "the protocol has other ports than the table")
  let mut goals := []
  for goal in ["loose", "strict"] do
    let clause ← IO.ofExcept (SourceClause.seen c goal)
    unless clause == ⟨"proves", none, "V", "NearZero", ["xs"], []⟩ do
      throw (IO.userError s!"goal {goal} reads another clause: {repr clause}")
    let (selected, _) ← IO.ofExcept (selectNamedGoal c.state goal .soundness)
    let #[tolerance] := selected.specification
      | throw (IO.userError s!"goal {goal} gives other proof arguments than the tolerance")
    goals := goals ++ [⟨goal, tolerance, ← IO.ofExcept (goalDrawCharge c goal [] "z")⟩]
  let some verifier := (← IO.ofExcept (goalClause c "loose")).role
    | throw (IO.userError "the clause has no deciding role")
  let some prover := head.roster.toList.idxOf? "P" | throw (IO.userError "the roster has no prover")
  let printed := Written.package (c.emission.package noAssociation)
  let some (root, true) := printed.definitions.getLast?
    | throw (IO.userError "the root of the package is no protocol")
  unless root.number == c.id do throw (IO.userError "the package ends in another definition")
  let callees := match printed.definitions.dropLast.getLast? with
    | some (key, _) => s!"program{key.number}"
    | none => s!"program{Written.baseSuffix}"
  return ⟨text, root.number, verifier, prover, callees, printed.text, goals⟩

def chargeTerm (charge : DrawCharge) : String :=
  let draw (blocks : List (Key × Nat)) (key : Key) :=
    let around := ", ".intercalate (blocks.map fun (block, number) => s!"(⟨{block.number}⟩, {number})")
    s!"([{around}], ⟨{key.number}⟩)"
  let draws := ", ".intercalate (charge.draws.map fun (blocks, key) => draw blocks key)
  s!"⟨⟨{charge.owner.number}⟩, {charge.numerator}, {charge.denominator}, [{draws}]⟩"

/-- What was read from the source, as terms for the proof module. -/
def facts (s : Subject) : String :=
  s!"abbrev rootKey : Key := ⟨{s.root}⟩\n" ++
  s!"noncomputable abbrev rootHeader := header{s.root}\n" ++
  s!"noncomputable abbrev rootNames := names{s.root}\n" ++
  s!"noncomputable abbrev rootBody := body{s.root}\n" ++
  s!"noncomputable abbrev calleeProgram : Typed V := {s.callees}\n" ++
  s!"abbrev verifierRole : Role := {s.verifier}\nabbrev proverRole : Role := {s.prover}\n" ++
  String.join (s.goals.map fun goal =>
    s!"def {goal.name}Charge : Zkc.Frontend.Written.DrawCharge := {chargeTerm goal.charge}\n" ++
    s!"def {goal.name}Tolerance : Nat := {goal.tolerance}\n")

def imports (others : List String) : String :=
  String.join ((Written.packageImports ++ others).map (s!"import {·}\n")) ++ "\nopen Zkc.Core\n"

/-- The theorems of the proof module, whose axioms the check reads. -/
def theorems : List String := [
  "verifier.eq", "walked_within", "walked_excludes", "walk_reads_any_key", "judged_within",
  "returns_within", "loose_sound", "strict_sound", "Witness.loose_at_table",
  "Witness.strict_at_table", "Witness.loose_attained", "Witness.strict_attained",
  "Witness.misplaced_judges_nothing", "Witness.foreign_judges_nothing"]

def proofModule (name : String) (s : Subject) (template : String) : String :=
  imports ["Zkc.Formal.Walk", "Zkc.Formal.Written.PortSamplers", "Zkc.Formal.Written.SiteAllowance",
    "Zkc.Formal.Written.StandardModel", "Zkc.Formal.Written.FiniteModel"] ++
  s!"namespace {name}\n" ++ s.package ++ facts s ++ template ++
  String.join (theorems.map (s!"#print axioms {·}\n")) ++ s!"end {name}\n"

def comparisonModule (name : String) (s : Subject) : String :=
  imports ["Zkc.Tests.Frontend.PrintedPackageSupport"] ++ s!"namespace {name}\n" ++ s.package ++
  s!"#eval Zkc.Tests.Frontend.PrintedPackageSupport.expectGoalRoot {literal s.text} \"loose\" " ++
  s!"({Written.associationTerm noAssociation}) stored association\nend {name}\n"

/-- Lean on a module, in the formal package, as a task. -/
def start (work : System.FilePath) (name text : String) :
    IO (Task (Except IO.Error (Bool × String))) := do
  let path := work / s!"{name}.lean"
  IO.FS.writeFile path text
  IO.asTask (runLakeLean path)

def finish (task : Task (Except IO.Error (Bool × String))) : IO (Bool × String) :=
  IO.ofExcept task.get

/-- A control: Lean refuses the module, and the theorems that are left unproved, itself or by
what they use, are the expected ones. -/
def expectUnproved (title name : String) (task : Task (Except IO.Error (Bool × String)))
    (expected : List String) : IO Unit := do
  let (ok, output) ← finish task
  if ok then throw (IO.userError s!"{title}: Lean accepted a control that must be refused")
  let unproved := theorems.filter fun theorem_ =>
    ((axiomsOf s!"{name}.{theorem_}" output).getD ["sorryAx"]).contains "sorryAx"
  unless unproved == expected do
    throw (IO.userError s!"{title}: unproved are {unproved}, expected {expected}\n{output}")

def run (corpus template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let blocks := readBlocks (← IO.FS.readFile corpus)
  let some source := (blocks.find? (·.id == "N-GL2a")).bind (·.files[0]?)
    | throw (IO.userError "missing the reference case N-GL2a")
  let template ← IO.FS.readFile template
  unless (source.splitOn relationLine).length == 2 do
    throw (IO.userError "the relation of the source is not the relation that the proof module reads")
  let written ← read source
  unless (written.root, written.verifier, written.prover) == (1, 1, 0) do
    throw (IO.userError "the root and the roles of the source are not where they were")

  -- The roster reversed: the verifier is the first role, and the key of the root is as it was.
  let turned ← read (← edit source "protocol Count roles(P, V)" "protocol Count roles(V, P)")
  unless (turned.root, turned.verifier, turned.prover) == (1, 0, 1) do
    throw (IO.userError "with the roster reversed the verifier is not the first role")
  unless turned.goals == written.goals do
    throw (IO.userError "with the roster reversed the goals changed")

  -- The relation changed: no part of the package and no charge says so.
  let stricter ← edit source "else 1) <= e\n" "else 1) < e\n"
  if (stricter.splitOn relationLine).length == 2 then
    throw (IO.userError "the changed relation is still the relation that the proof module reads")
  let changed ← read stricter
  unless changed.package == written.package && changed.goals == written.goals do
    throw (IO.userError "a change of the relation changed the package or a charge")

  -- Other sizes, read by the frontend alone. With five entries and the tolerance 4 a table
  -- outside the relation has no zero entry, and the charge is zero; with four entries the
  -- ceiling that the source writes is negative, and no charge is read.
  let five ← read (← edit source "scheme Checked = Count<8>:" "scheme Checked = Count<5>:")
  unless (five.goals.map fun goal => (goal.charge.numerator, goal.charge.denominator)) == [(0, 1), (3, 5)] do
    throw (IO.userError "the charges of Count<5> are not 0 and 3/5")
  let four ← edit source "scheme Checked = Count<8>:" "scheme Checked = Count<4>:"
  let .error refusal := (goalRoot four "loose").bind (goalDrawCharge · "loose" [] "z")
    | throw (IO.userError "a negative ceiling was read as a charge")
  unless refusal.contains "nonnegative" do
    throw (IO.userError s!"Count<4> was refused for another reason: {refusal}")

  -- The controls: the roles exchanged; the charge of `loose` below the bound of its tolerance;
  -- the charge of `loose` on the guard; the charge of `loose` owned by another definition.
  let some loose := written.goals.find? (·.name == "loose") | throw (IO.userError "missing the goal loose")
  let withLoose (charge : DrawCharge) : Subject :=
    { written with goals := written.goals.map fun goal =>
        if goal.name == "loose" then { goal with charge } else goal }
  let exchanged := { written with verifier := written.prover, prover := written.verifier }
  let small := withLoose { loose.charge with numerator := loose.charge.numerator - 1 }
  let elsewhere := withLoose { loose.charge with draws := [([], ⟨5⟩)] }
  let foreign := withLoose { loose.charge with owner := ⟨loose.charge.owner.number + 1⟩ }

  let proof ← start work "Count" (proofModule "Count" written template)
  let comparison ← start work "CountSource" (comparisonModule "CountSource" written)
  let turnedProof ← start work "CountTurned" (proofModule "CountTurned" turned template)
  let turnedComparison ← start work "CountTurnedSource" (comparisonModule "CountTurnedSource" turned)
  let exchangedProof ← start work "RolesControl" (proofModule "RolesControl" exchanged template)
  let smallProof ← start work "BoundControl" (proofModule "BoundControl" small template)
  let elsewhereProof ← start work "SiteControl" (proofModule "SiteControl" elsewhere template)
  let foreignProof ← start work "OwnerControl" (proofModule "OwnerControl" foreign template)

  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  for (name, task) in [("Count", proof), ("CountTurned", turnedProof)] do
    let (ok, output) ← finish task
    acceptedOutput name ok output theorems allowed
  for (name, task) in [("CountSource", comparison), ("CountTurnedSource", turnedComparison)] do
    let (ok, output) ← finish task
    acceptedOutput name ok output []
  -- The prover's program is not the one that draws: no theorem about the walk is proved.
  expectUnproved "the roles exchanged" "RolesControl" exchangedProof (theorems.drop 1)
  -- Only `loose` and what is stated of it at its table fail, and `strict` stands.
  expectUnproved "a charge below the bound" "BoundControl" smallProof
    ["loose_sound", "Witness.loose_at_table", "Witness.loose_attained"]
  expectUnproved "a charge on another instruction" "SiteControl" elsewhereProof
    ["loose_sound", "Witness.loose_at_table"]
  expectUnproved "a charge of another definition" "OwnerControl" foreignProof
    ["loose_sound", "Witness.loose_at_table"]
  let charges := ", ".intercalate (written.goals.map fun goal =>
    s!"{goal.name} at tolerance {goal.tolerance} within {goal.charge.numerator}/{goal.charge.denominator}")
  IO.println (s!"Count<8> is judged within the charges of its goals ({charges}), " ++
    "in either order of the roster; 4 of 4 controls refused.")

end CountCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work =>
    CountCharge.run "../../language/conformance/layer-b.txt" "checks/CountCharge.lean.in" work
