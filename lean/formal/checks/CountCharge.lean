import Zkc.Frontend.Written.Claim
import Zkc.Frontend.Written.Charge
import Zkc.Frontend.Written.Package
import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SyntaxHarness
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import Zkc.Core.Admission.Theorems
import Zkc.Kernel
import Zkc.Vocabulary.Project

/-!
An admitted protocol judged within the charges that its source declares, and the judgment taken
to a probability.

The subject is the reference case `N-GL2a`: `Count<8>` draws a position of a table of eight
field elements and returns when the entry there is zero; its relation holds of a table with at
most `e` entries that are not zero, and its charge on the draw is `1 - (e + 1) / n`. Two goals
give `e` the values 4 and 1.

The check reads the source with the frontend and writes two modules, on which Lean is run.

- The proof module has the printed package of what the two goals claim: the protocol of the
  scheme, then the relation of the clause at the value of each goal, as the functions that the
  frontend emits (`Written.goalClaims`). Around the text of `CountCharge.lean.in` stands what
  `Written.Statements` writes from what the frontend read: the facts (the key of the root, the
  verifier and the prover of the scheme, and for each goal the value of its proof argument, its
  charge on the draw and its relation), where the walks start, the transfer of a statement to every admitted program, the
  claim of each goal about the installed program (`looseClaim`, `strictClaim`) with its goal
  for every admitted program, its result with the coverage and the statement that its
  hypotheses are met, all as propositions defined before the text; and after the text the
  theorems of those (`loose_sound`, `loose_result`, `loose_met`, and the same for `strict`). The text of the check proves the
  claims (`loose_installed`, `strict_installed`) and chooses nothing of them. The module
  imports nothing of the frontend but the record of a charge. Its theorems are about every
  program that admission gives for the stored program of the package. The function of each
  relation returns whether at most the goal's tolerance of the entries are not zero. On a table
  on which that function returns false, the verifier is judged never to return within the
  budget of the goal's charge, with each fee within what the charge allows the effect that pays
  it; against every service that is no more likely to answer a coin within a set of replies
  than the sampler of the coin's law is to draw one there, it returns with probability at most
  the total of the charge. The statement names no port and no sampler: the
  samplers are those of the laws of the model (`lawSamplers`). For each goal a concrete table
  and a service meet every hypothesis, and there the verifier returns with probability exactly
  the total of the charge; a charge on another instruction, and a charge of another definition,
  judge it at no budget; a service that always gives one position does not follow the samplers.
- The proof module also states that the standard model covers the package (`covered`): it
  interprets every row of the vocabulary that the package links, read from the stored program
  through its loops and arms, and has a sampler for the law of every coin that it draws.
- The comparison module has the same printed package and the frontend: the program by names
  and the association that Lean reads from the package are those that the frontend gives to
  admission for the claims, and its first definitions are those of the root's own package.

What the source says and the proof module takes as given is asserted here against the source:
the clause that each goal reads, by `goalClause`, and the port that the relation is applied
to. Nothing of the relation is bound by hand. Two more subjects show what the check
distinguishes. With the roster reversed the verifier is the first role, and the same text
proves the same theorems. With `<=` of the relation changed to `<`, the deployed definitions
and both charges are what they were and the relation is another function: Lean refuses the
theorems that say what the relation computes and those that rest on them.

Five controls are refused by Lean, each for the theorems that depend on what it changes: a row
outside the table of the model inside the loop of the relation (the model does not cover that
package), the relation changed, a charge below the bound of its tolerance, a charge on another
instruction, and a charge of another definition. The deciding role of a statement is the
verifier of the goals' scheme and no caller chooses it, so the roles are exchanged in the
source: a scheme whose prover is `V` makes `P` the verifier, and the frontend refuses the goal,
whose clause is decided by `V` (GL3). Two other sizes are read by the frontend alone: the charge of `Count<5>` at the tolerance 4 is zero, and the negative ceiling
of `Count<4>` is no charge. A goal that states a ceiling at the total of its charge is issued
the comparison, which the kernel decides; one that states a ceiling below it is issued no
statement.
-/

open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

namespace CountCharge

/-- What the check reads of a source: what its two goals claim, with what their statements
need, and the stored text of the definitions of the root's own package. -/
structure Subject where
  text : String
  statements : Statements
  deployed : List (Nat × String)

/-- The root, the verifier and the prover of a subject. -/
def Subject.places (s : Subject) : Nat × Nat × Nat :=
  (s.statements.claims.root, s.statements.claims.verifier, s.statements.claims.prover)

/-- The name, the proof arguments and the charge of each goal. -/
def Subject.goals (s : Subject) : List (String × Array Nat × DrawCharge) :=
  s.statements.goals.map fun goal => (goal.claimed.goal, goal.claimed.specification, goal.charge)

/-- The printed package of the claims. -/
def Subject.package (s : Subject) : String := (Written.package s.statements.package).text

def noAssociation : Association := ⟨[], [], [], [], []⟩

/-- The source with its one occurrence of `before` replaced. -/
def edit (text before after : String) : IO String := do
  unless (text.splitOn before).length == 2 do
    throw (IO.userError s!"expected one occurrence of {before}")
  return text.replace before after

/-- A source read: both goals select one root; each reads the clause `proves @V NearZero(xs)`,
decided by the verifier of the scheme, on the only port of the protocol; each gives one proof
argument; each has a charge on the draw `z`; and what the two claim is one package. -/
def read (text : String) : IO Subject := do
  let c ← IO.ofExcept (goalRoot text "loose")
  let head ← IO.ofExcept (SourceClause.rootHead c)
  unless head.ports.map (·.binder.name) == #["xs"] do
    throw (IO.userError "the protocol has other ports than the table")
  let claims ← IO.ofExcept (goalClaims c ["loose", "strict"])
  let mut goals := []
  for claimed in claims.goals do
    let goal := claimed.goal
    let clause ← IO.ofExcept (SourceClause.seen c goal)
    unless clause == ⟨"proves", none, "V", "NearZero", ["xs"], []⟩ do
      throw (IO.userError s!"goal {goal} reads another clause: {repr clause}")
    unless claimed.statement == #[0] && claimed.witness == some #[] do
      throw (IO.userError s!"goal {goal}: the relation is applied to other ports than the table")
    unless claimed.specification.size == 1 do
      throw (IO.userError s!"goal {goal} gives other proof arguments than the tolerance")
    goals := goals ++ [{ claimed, charge := ← IO.ofExcept (goalDrawCharge c goal [] "z") : StatedGoal }]
  unless (head.roster[claims.verifier]?, head.roster[claims.prover]?) == (some "V", some "P") do
    throw (IO.userError "the verifier and the prover of the scheme are not the roles V and P")
  let own := c.emission.package noAssociation
  let deployed := own.named.definitions.map fun d => (d.key.number, storedDefinition (b := own.bindings) d)
  return ⟨text, ⟨claims, goals, []⟩, deployed⟩

/-- The theorems of the proof module, whose axioms the check reads. -/
def theorems : List String := [
  "admitted_exists", "covered", "verifierProgram.eq", "verifier_meaning", "loose_meaning",
  "strict_meaning", "loose_relation", "strict_relation", "walked_within", "walked_excludes",
  "walk_reads_any_key", "judged_within", "returns_within", "loose_installed", "strict_installed",
  "Witness.loose_at_table", "Witness.strict_at_table", "Witness.loose_attained",
  "Witness.strict_attained", "Witness.misplaced_judges_nothing", "Witness.foreign_judges_nothing",
  "Witness.fixed_position_does_not_follow", "loose_witnessed", "strict_witnessed",
  "loose_sound", "loose_result", "loose_met", "strict_sound", "strict_result", "strict_met"]

/-- The theorems that say what the relations compute, and those that rest on them. -/
def ofRelation : List String :=
  ["loose_relation", "strict_relation", "loose_installed", "strict_installed",
    "Witness.loose_at_table", "Witness.strict_at_table", "loose_witnessed", "strict_witnessed",
    "loose_sound", "loose_result", "loose_met", "strict_sound", "strict_result", "strict_met"]

/-- The claim of `loose` and what rests on it. -/
def ofLoose : List String := ["loose_installed", "Witness.loose_at_table", "loose_sound", "loose_result"]

/-- The proof module: the package of the claims; what the frontend read, the transfers to an
admitted program and the claims of the goals, all generated; the proofs written for the
protocol; and the goals for every admitted program, generated. -/
def proofModule (name : String) (s : Subject) (template : String) : IO String := do
  refuseUnchecked name template
  let stated := s.statements
  let claims ← IO.ofExcept (stated.claimTexts standardModelText)
  let closings := stated.closings
  let ceilings ← IO.ofExcept stated.ceilings
  return packageHeader ["Zkc.Formal.Walk", "Zkc.Formal.OracleProcess", "Zkc.Formal.Written.PortSamplers",
      "Zkc.Formal.Written.LawSamplers", "Zkc.Formal.Written.SiteAllowance",
      "Zkc.Formal.Written.FunctionMeaning", "Zkc.Formal.Written.StandardModel",
      "Zkc.Formal.Written.FiniteModel"] ++
    s!"namespace {name}\n" ++ s.package ++ Statements.opens ++ stated.facts ++ "\n" ++
    Statements.coverage standardModelText ++ stated.entries ++ stated.transfers ++ claims ++
    template ++ "\n" ++
    closings ++ ceilings ++
    String.join (theorems.map (s!"#print axioms {·}\n")) ++ s!"end {name}\n"

/-- A module with the package of a subject, its facts, and the comparison of each goal's total
with its ceiling. -/
def ceilingModule (name : String) (s : Subject) : IO String := do
  let ceilings ← IO.ofExcept s.statements.ceilings
  return packageHeader ["Zkc.Formal.Written.Ceiling"] ++ s!"namespace {name}\n" ++ s.package ++
    Statements.opens ++ s.statements.facts ++ "\n" ++ ceilings ++
    s!"#print axioms loose_ceiling\nend {name}\n"

/-- A module with the package of a subject and the one theorem that the standard model covers
it. -/
def coverageModule (name : String) (s : Subject) : String :=
  packageHeader ["Zkc.Formal.Written.LawSamplers"] ++ s!"namespace {name}\n" ++ s.package ++
  "open Zkc.Formal.Written\n" ++ Statements.coverage standardModelText ++
  s!"#print axioms covered\nend {name}\n"

def comparisonModule (name : String) (s : Subject) : String :=
  packageHeader ["Zkc.Tests.Frontend.PrintedPackageSupport"] ++ s!"namespace {name}\n" ++ s.package ++
  s!"#eval Zkc.Tests.Frontend.PrintedPackageSupport.expectGoalClaims {literal s.text} " ++
  s!"{reprStr (s.goals.map (·.1))} " ++
  s!"({Written.associationTerm noAssociation}) stored association\nend {name}\n"

def run (corpus template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let blocks := readBlocks (← IO.FS.readFile corpus)
  let some source := (blocks.find? (·.id == "N-GL2a")).bind (·.files[0]?)
    | throw (IO.userError "missing the reference case N-GL2a")
  let template ← IO.FS.readFile template
  let written ← read source
  unless written.places == (1, 1, 0) do
    throw (IO.userError "the root and the roles of the source are not where they were")
  unless (written.statements.entryNames ++ written.statements.closingNames).all theorems.contains do
    throw (IO.userError "a generated theorem is not among the theorems read")

  -- The roster reversed: the verifier is the first role, and the key of the root is as it was.
  let turned ← read (← edit source "protocol Count roles(P, V)" "protocol Count roles(V, P)")
  unless turned.places == (1, 0, 1) do
    throw (IO.userError "with the roster reversed the verifier is not the first role")
  unless turned.goals == written.goals do
    throw (IO.userError "with the roster reversed the goals changed")

  -- The relation changed: the deployed definitions and both charges are what they were, and the
  -- package of the claims has another function for the relation.
  let changed ← read (← edit source "else 1) <= e\n" "else 1) < e\n")
  unless changed.deployed == written.deployed && changed.goals == written.goals do
    throw (IO.userError "a change of the relation changed a deployed definition or a charge")
  if changed.package == written.package then
    throw (IO.userError "a change of the relation changed nothing in the package of the claims")

  -- Other sizes, read by the frontend alone. With five entries and the tolerance 4 a table
  -- outside the relation has no zero entry, and the charge is zero; with four entries the
  -- ceiling that the source writes is negative, and no charge is read.
  let five ← read (← edit source "scheme Checked = Count<8>:" "scheme Checked = Count<5>:")
  unless (five.goals.map fun (_, _, charge) => (charge.numerator, charge.denominator)) == [(0, 1), (3, 5)] do
    throw (IO.userError "the charges of Count<5> are not 0 and 3/5")
  let four ← edit source "scheme Checked = Count<8>:" "scheme Checked = Count<4>:"
  let .error refusal := (goalRoot four "loose").bind (goalDrawCharge · "loose" [] "z")
    | throw (IO.userError "a negative ceiling was read as a charge")
  unless refusal.contains "nonnegative" do
    throw (IO.userError s!"Count<4> was refused for another reason: {refusal}")

  -- A goal that states a ceiling. At the total of its charge, 3/8, the statement is issued with the
  -- comparison, which the kernel decides; below it no statement is issued (GL4).
  let goalLine := "goal loose = soundness(Checked, spec e = 4)"
  let atTotal ← read (← edit source goalLine (goalLine ++ " <= 3/8"))
  let ceilingProof ← startLakeLean work "CeilingAtTotal" (← ceilingModule "CeilingAtTotal" atTotal)
  let below ← read (← edit source goalLine (goalLine ++ " <= 1/4"))
  match below.statements.ceilings with
  | .ok _ => throw (IO.userError "a goal whose ceiling is below the total of its charge was issued a statement")
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

  -- The controls: the charge of `loose` below the bound of its tolerance; the charge of `loose`
  -- on the guard; the charge of `loose` owned by another definition.
  let some (_, _, loose) := written.goals.find? (·.1 == "loose")
    | throw (IO.userError "missing the goal loose")
  let withLoose (charge : DrawCharge) : Subject :=
    { written with statements := { written.statements with
        goals := written.statements.goals.map fun goal =>
          if goal.claimed.goal == "loose" then { goal with charge } else goal } }
  -- A row outside the table of the model, inside the loop of the relation: the power of a field
  -- element, which the standard model gives a constant.
  let uncovered ← read (← edit source "if xs[i] == 0 then 0 else 1" "if xs[i] ^ 2 == 0 then 0 else 1")
  let uncoveredProof ← startLakeLean work "CoverageControl" (coverageModule "CoverageControl" uncovered)
  let changedProof ← startLakeLean work "RelationControl" (← proofModule "RelationControl" changed template)
  let small := withLoose { loose with numerator := loose.numerator - 1 }
  let elsewhere := withLoose { loose with draws := [([], ⟨5⟩)] }
  let foreign := withLoose { loose with owner := ⟨loose.owner.number + 1⟩ }

  let proof ← startLakeLean work "Count" (← proofModule "Count" written template)
  let comparison ← startLakeLean work "CountSource" (comparisonModule "CountSource" written)
  let turnedProof ← startLakeLean work "CountTurned" (← proofModule "CountTurned" turned template)
  let turnedComparison ← startLakeLean work "CountTurnedSource" (comparisonModule "CountTurnedSource" turned)
  let smallProof ← startLakeLean work "BoundControl" (← proofModule "BoundControl" small template)
  let elsewhereProof ← startLakeLean work "SiteControl" (← proofModule "SiteControl" elsewhere template)
  let foreignProof ← startLakeLean work "OwnerControl" (← proofModule "OwnerControl" foreign template)

  let allowed := ["propext", "Classical.choice", "Quot.sound"]
  for (name, task) in [("Count", proof), ("CountTurned", turnedProof)] do
    let (ok, output) ← finishLean task
    acceptedOutput name ok output theorems allowed
  for (name, task) in [("CountSource", comparison), ("CountTurnedSource", turnedComparison)] do
    let (ok, output) ← finishLean task
    acceptedOutput name ok output []
  let (ok, output) ← finishLean ceilingProof
  acceptedOutput "CeilingAtTotal" ok output ["loose_ceiling"] allowed
  -- The package with a row outside the table is not covered: the kernel decides it.
  let (ok, output) ← finishLean uncoveredProof
  if ok then throw (IO.userError "Lean accepted that the model covers a package with a row outside its table")
  unless output.contains "StandardModel.covers stored = true" && output.contains "is false" do
    throw (IO.userError s!"the coverage control was refused for another reason\n{output}")
  -- With `<` for `<=` the function of the relation computes another comparison: what is said
  -- of it, and what rests on that, is not proved; the theorems about the verifier stand.
  expectUnproved "the relation changed" "RelationControl" theorems changedProof ofRelation
  -- Only `loose` and what is stated of it at its table fail, and `strict` stands.
  expectUnproved "a charge below the bound" "BoundControl" theorems smallProof
    ["loose_installed", "Witness.loose_at_table", "Witness.loose_attained", "loose_sound",
      "loose_result"]
  expectUnproved "a charge on another instruction" "SiteControl" theorems elsewhereProof ofLoose
  expectUnproved "a charge of another definition" "OwnerControl" theorems foreignProof ofLoose
  let charges := ", ".intercalate (written.goals.map fun (name, arguments, charge) =>
    s!"{name} at tolerance {arguments[0]!} within {charge.numerator}/{charge.denominator}")
  IO.println (s!"Count<8> is judged within the charges of its goals ({charges}), " ++
    "on the tables on which the admitted relation returns false, in either order of the roster; " ++
    "5 of 5 controls refused, and a scheme whose prover decides the clause is refused by the frontend.")

end CountCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work =>
    CountCharge.run "../../language/conformance/layer-b.txt" "checks/CountCharge.lean.in" work
