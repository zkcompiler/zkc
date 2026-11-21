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
An admitted protocol judged within the table of caps that the frontend reads for its goal from
the charges of its source, and the judgment taken to a probability.

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
  table of caps (`looseCaps`, `strictCaps`: the root at the goal's proof arguments, with the cap
  of its charged draw and how many times it runs) and its relation), that the counts of each
  table are those of the stored program and what its budget is (`loose_counted`,
  `loose_budget`), where the walks start, the transfer of a statement to every admitted program, the
  claim of each goal about the installed program (`looseClaim`, `strictClaim`) with its goal
  for every admitted program, its result with the coverage and the statement that its
  hypotheses are met, all as propositions defined before the text; and after the text the
  theorems of those (`loose_sound`, `loose_result`, `loose_met`, and the same for `strict`).
  Before the text stands also the judgment that establishes each claim (`looseJudged`,
  `strictJudged`) with the theorem that the claim follows from it. The text of the check proves
  the judgments (`loose_judged`, `strict_judged`) and chooses nothing of them; it states neither
  a claim nor where a walk starts. The module
  imports nothing of the frontend but the records of a table of caps. Its theorems are about every
  program that admission gives for the stored program of the package. The function of each
  relation returns whether at most the goal's tolerance of the entries are not zero. On a table
  on which that function returns false, the verifier is judged never to return within the
  budget of the goal's table, with each fee within the cap that the table gives the draw that
  pays it; against every service that is no more likely to answer a coin within a set of replies
  than the sampler of the coin's law is to draw one there, it returns with probability at most
  the total of the table. The statement names no port and no sampler: the
  samplers are those of the laws of the model (`lawSamplers`). For each goal a concrete table
  and a service meet every hypothesis, and there the verifier returns with probability exactly
  the total of the table; a table that caps another instruction judges it at no budget and has
  not the counts of the stored program, as a table of another definition has not; a service
  that always gives one position does not follow the samplers.
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
and both tables are what they were and the relation is another function: Lean refuses the
theorems that say what the relation computes and those that rest on them.

Five controls are refused by Lean, each for the theorems that depend on what it changes: a row
outside the table of the model inside the loop of the relation (the model does not cover that
package), the relation changed, and three charges, each written in the source, since no caller
gives a statement its table: a charge below the bound of its tolerance, a charge on the draw of
a loop that does not run, and a charge in another protocol. The last two give the root no cap,
which is asserted of the tables that the frontend reads. The deciding role of a statement is the
verifier of the goals' scheme and no caller chooses it, so the roles are exchanged in the
source: a scheme whose prover is `V` makes `P` the verifier, and the frontend refuses the goal,
whose clause is decided by `V` (GL3). Two other sizes are read by the frontend alone: the charge of `Count<5>` at the tolerance 4 is zero, and the negative ceiling
of `Count<4>` is no charge. A goal that states a ceiling at the total of its table is issued
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

/-- The name, the proof arguments and the table of caps of each goal. -/
def Subject.goals (s : Subject) : List (String × Array Nat × CapTable) :=
  s.statements.claims.goals.map fun goal => (goal.goal, goal.specification, goal.caps)

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
argument; and what the two claim is one package. The table of caps of each goal is read with
its claim. -/
def read (text : String) : IO Subject := do
  let c ← IO.ofExcept (goalRoot text "loose")
  let head ← IO.ofExcept (SourceClause.rootHead c)
  unless head.ports.map (·.binder.name) == #["xs"] do
    throw (IO.userError "the protocol has other ports than the table")
  let claims ← IO.ofExcept (goalClaims c ["loose", "strict"])
  for claimed in claims.goals do
    let goal := claimed.goal
    let clause ← IO.ofExcept (SourceClause.seen c goal)
    unless clause == ⟨"proves", none, "V", "NearZero", ["xs"], []⟩ do
      throw (IO.userError s!"goal {goal} reads another clause: {repr clause}")
    unless claimed.statement == #[0] && claimed.witness == some #[] do
      throw (IO.userError s!"goal {goal}: the relation is applied to other ports than the table")
    unless claimed.specification.size == 1 do
      throw (IO.userError s!"goal {goal} gives other proof arguments than the tolerance")
  unless (head.roster[claims.verifier]?, head.roster[claims.prover]?) == (some "V", some "P") do
    throw (IO.userError "the verifier and the prover of the scheme are not the roles V and P")
  let own := c.emission.package noAssociation
  let deployed := own.named.definitions.map fun d => (d.key.number, storedDefinition (b := own.bindings) d)
  return ⟨text, ⟨claims, []⟩, deployed⟩

/-- The theorems of the text of the proofs. -/
def ofText : List String := [
  "loose_exact", "strict_exact", "loose_within", "strict_within", "walked_within",
  "walked_excludes", "walk_reads_any_key", "loose_relation", "strict_relation",
  "returns_installed", "loose_judged", "strict_judged", "Witness.loose_at_table",
  "Witness.strict_at_table", "Witness.loose_attained", "Witness.strict_attained",
  "Witness.misplaced_judges_nothing", "Witness.misplaced_not_counted",
  "Witness.foreign_not_counted", "Witness.fixed_position_does_not_follow", "loose_witnessed",
  "strict_witnessed"]

/-- The theorems that say what the relations compute, and those that rest on them. -/
def ofRelation : List String :=
  ["loose_relation", "strict_relation", "loose_judged", "strict_judged", "loose_installed",
    "strict_installed",
    "Witness.loose_at_table", "Witness.strict_at_table", "loose_witnessed", "strict_witnessed",
    "loose_sound", "loose_result", "loose_met", "strict_sound", "strict_result", "strict_met"]

/-- What the text says of the caps of the two goals, and what rests on it. -/
def ofCharge : List String :=
  ["loose_judged", "strict_judged", "loose_installed", "strict_installed",
    "Witness.loose_at_table", "Witness.strict_at_table",
    "Witness.loose_attained", "Witness.strict_attained", "loose_exact", "strict_exact",
    "loose_sound", "loose_result", "strict_sound", "strict_result"]

/-- The proof module, as the generator assembles it: the package of the claims and what is
generated around the proofs written for the protocol. -/
def proofModule (name : String) (s : Subject) (template : String) : IO Module :=
  IO.ofExcept (s.statements.module standardModelText name { text := template, theorems := ofText })

def run (corpus template : System.FilePath) (work : System.FilePath) : IO Unit := do
  let blocks := readBlocks (← IO.FS.readFile corpus)
  let some source := (blocks.find? (·.id == "N-GL2a")).bind (·.files[0]?)
    | throw (IO.userError "missing the reference case N-GL2a")
  let template ← IO.FS.readFile template
  let written ← read source
  unless written.places == (1, 1, 0) do
    throw (IO.userError "the root and the roles of the source are not where they were")
  -- The tables of caps, as the frontend read them: the one draw of the root, once, at the
  -- charge of each goal's tolerance.
  unless written.goals.map (·.2.2) ==
      [⟨[⟨⟨1⟩, [⟨⟨0⟩, 3, 8, 1⟩], []⟩]⟩, ⟨[⟨⟨1⟩, [⟨⟨0⟩, 3, 4, 1⟩], []⟩]⟩] do
    throw (IO.userError s!"the tables of caps are not the draw of the root at 3/8 and at 3/4: {repr (written.goals.map (·.2.2))}")

  -- The roster reversed: the verifier is the first role, and the key of the root is as it was.
  let turned ← read (← edit source "protocol Count roles(P, V)" "protocol Count roles(V, P)")
  unless turned.places == (1, 0, 1) do
    throw (IO.userError "with the roster reversed the verifier is not the first role")
  unless turned.goals == written.goals do
    throw (IO.userError "with the roster reversed the goals changed")

  -- The relation changed: the deployed definitions and both tables are what they were, and the
  -- package of the claims has another function for the relation.
  let changed ← read (← edit source "else 1) <= e\n" "else 1) < e\n")
  unless changed.deployed == written.deployed && changed.goals == written.goals do
    throw (IO.userError "a change of the relation changed a deployed definition or a table of caps")
  if changed.package == written.package then
    throw (IO.userError "a change of the relation changed nothing in the package of the claims")

  -- Other sizes, read by the frontend alone. With five entries and the tolerance 4 a table
  -- outside the relation has no zero entry, and the charge is zero; with four entries the
  -- ceiling that the source writes is negative, and no charge is read.
  let five ← read (← edit source "scheme Checked = Count<8>:" "scheme Checked = Count<5>:")
  unless (five.goals.map fun (_, _, caps) => caps.ratio) == [0, (3 : Rat) / 5] do
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
    (← IO.ofExcept (atTotal.statements.ceilingModule "CeilingAtTotal")).text
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
    unless control.deployed == written.deployed do
      throw (IO.userError s!"the charge {title}: a deployed definition changed")
    if control.goals == written.goals then
      throw (IO.userError s!"the charge {title}: the tables of caps are what they were")
  unless small.goals.map (·.2.2) ==
      [⟨[⟨⟨1⟩, [⟨⟨0⟩, 1, 4, 1⟩], []⟩]⟩, ⟨[⟨⟨1⟩, [⟨⟨0⟩, 5, 8, 1⟩], []⟩]⟩] do
    throw (IO.userError "the smaller charge is not 1/4 and 5/8 at the draw")
  for control in [elsewhere, foreign] do
    unless control.goals.all (·.2.2 == ⟨[⟨⟨1⟩, [], []⟩]⟩) do
      throw (IO.userError s!"a charge that is not on the draw of the root gave a cap: {repr (control.goals.map (·.2.2))}")
  -- A row outside the table of the model, inside the loop of the relation: the power of a field
  -- element, which the standard model gives a constant.
  let uncovered ← read (← edit source "if xs[i] == 0 then 0 else 1" "if xs[i] ^ 2 == 0 then 0 else 1")
  let uncoveredProof ← startLakeLean work "CoverageControl"
    (uncovered.statements.coverageModule standardModelText "CoverageControl").text
  let changedProof ← startLakeLean work "RelationControl" (← proofModule "RelationControl" changed template).text

  let module ← proofModule "Count" written template
  let theorems := module.theorems
  let proof ← startLakeLean work "Count" module.text
  let comparison ← startLakeLean work "CountSource" (comparisonModule "CountSource" written.text (written.goals.map (·.1)) written.package)
  let turnedProof ← startLakeLean work "CountTurned" (← proofModule "CountTurned" turned template).text
  let turnedComparison ← startLakeLean work "CountTurnedSource" (comparisonModule "CountTurnedSource" turned.text (turned.goals.map (·.1)) turned.package)
  let smallProof ← startLakeLean work "BoundControl" (← proofModule "BoundControl" small template).text
  let elsewhereProof ← startLakeLean work "SiteControl" (← proofModule "SiteControl" elsewhere template).text
  let foreignProof ← startLakeLean work "OwnerControl" (← proofModule "OwnerControl" foreign template).text

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
  -- The caps of both goals are below the bounds of their tolerances: the text reads another
  -- cap from each table than the bound, and what rests on it is not proved.
  expectUnproved "a charge below the bound" "BoundControl" theorems smallProof ofCharge
  -- In these two the root has no charged draw, so the module has no theorem of a draw's cap.
  let uncapped := theorems.filter fun name => !written.statements.siteNames.contains name
  expectUnproved "a charge on a loop that does not run" "SiteControl" uncapped elsewhereProof ofCharge
  expectUnproved "a charge of another protocol" "OwnerControl" uncapped foreignProof ofCharge
  -- Each is refused where the text reads the cap of the draw from the table.
  for (title, task) in [("below the bound", smallProof), ("on a loop that does not run", elsewhereProof),
      ("of another protocol", foreignProof)] do
    let (_, output) ← finishLean task
    unless output.contains "drawCap looseCaps = " && output.contains "drawCap strictCaps = " do
      throw (IO.userError s!"the charge {title}: refused for another reason\n{output}")
  let charges := ", ".intercalate (written.goals.map fun (name, arguments, caps) =>
    s!"{name} at tolerance {arguments[0]!} within {caps.ratio}")
  IO.println (s!"Count<8> is judged within the tables of caps of its goals ({charges}), " ++
    "on the tables on which the admitted relation returns false, in either order of the roster; " ++
    "5 of 5 controls refused, and a scheme whose prover decides the clause is refused by the frontend.")

end CountCharge

#eval show IO Unit from
  IO.FS.withTempDir fun work =>
    CountCharge.run "../../language/conformance/layer-b.txt" "checks/CountCharge.lean.in" work
