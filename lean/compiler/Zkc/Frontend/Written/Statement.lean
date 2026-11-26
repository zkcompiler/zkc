module

public import Zkc.Frontend.Written.Subject
public import Zkc.Frontend.Written.Charge
public import Zkc.Subject.Coverage
public import Zkc.Frontend.Written.Package

@[expose] public section

/-!
The statements of written soundness goals, as the text of a module.

A module about what goals claim holds the printed package of the claims (`goalClaims`). This
file writes what stands around a proof in such a module, from what the frontend read and from
the library, at the standard interpretation of the vocabulary:

- `factsOf`: the keys, headers and places of the root and goal relations, the headers and
  places of the named functions before the root, the verifier and the prover of the scheme, and each goal's
  proof arguments and table of caps, as terms;
- `counts`: for each goal, that the counts of its table are those of the stored program and
  that its budget is the number that the frontend computed, both decided by the kernel;
- `coverage`: for each goal, that its reachable definitions are covered;
- `sites`: the key of each named draw of the root under the name of its site in the source
  (`site_<name>`), and for each goal the cap that its table gives the draw
  (`<goal>_cap_<name>`), decided by the kernel;
- `verifierEntry`: the verifier’s projected program and the equation for its meaning;
- `transfers`: that what holds of the root and of a relation in the installed program holds of
  them in every program that admission gives, each found by its key;
- `claimTexts`: for each goal, the propositions that are stated before any proof. The claim
  about a program (`<goal>ClaimOf`, and `<goal>Claim` about the installed one): on valid inputs
  of the deciding role, where the relation of the goal's clause returns false at its operands
  (for every valid witness, when the relation has witness parameters), the deciding role
  returns within the total of the goal's table of caps, in the experiment that the formal library
  defines (`ReturnsWithin`, `ZkcFormal/ReturnExperiment.lean`): against every service that is
  no more likely to answer a coin within a set of replies than the sampler of the coin's law
  is to draw one there (it may also not answer) and that answers only what is permitted. The formal library reads the process, samplers and bound from the resolved goal. The goal for every admitted program (`<goal>Goal`), the result with the coverage
  and the counts of the table (`<goal>Result`), and that the hypotheses of the claim are met together (`<goal>Witnessed`);
- `judgments`, for a text that establishes its claims by the judgment with fees
  (`Method.fees`): for each goal the proposition `<goal>Judged` that the text has to prove
  and the theorem `<goal>_claim_of_judged` that the claim follows from it, and the
  theorem `<goal>_witnessed_of` that the hypotheses of the claim are met at any valid inputs
  on which the relation returns false;
- `goalPublications` selects the published theorem and proposition pairs and their closing
  proofs. Full publication includes the installed claim, soundness for every admission, the
  result and the witness. With fees the installed claim follows from the author's judgment.
  With a direct proof the author supplies the installed theorem. A witness-only request
  publishes just `<goal>_met : <goal>Witnessed` from the author's witness;
- `ceilings`: for each goal that states a ceiling, the theorem `<goal>_ceiling` that the total
  of its table of caps is within it, stated and proved before the text. A goal whose ceiling is
  below that total is refused here (GL4), before any module is written.

`Statements.module` issues two modules. The statements module holds the package, facts,
transfers, subject, goal propositions, coverage, counts, sites, the optional verifier entry,
fee judgments when requested, and ceilings. The proof module imports the statements and
holds the author's text, the selected closing proofs and the check's consumers. A caller gives the text of the proofs with
what that text imports and the names of its theorems, and what it adds after the closing
theorems. Every statement that is published is a proposition of the module of the statements: a
text is not read where it is elaborated, and a name that the text declares cannot be one of
it. The subject selects the formal library’s experiment and its parameters before the author text is read.

What a statement says of its goal is read from the claims (`goalClaims`) and from nothing that
a caller gives beside them: the deciding role is the verifier of the claims' scheme, the
operands are the inputs of the deployed header at the places that the claims give, and the
proof arguments, the ceiling and the table of caps are the goal's. A caller gives the labels of
the functions that the text names. A goal whose clause is a `reduces` gets no
statement: the statement of a reduction is about a return on which the reduced statement is
true, and a bound on every return is another claim.

The standard interpretation supplies the model and its service. The kernel checks coverage
for the reach of each goal in the stored program. The bound is the total of its table of caps.
-/

namespace Zkc.Frontend.Written
open Zkc.Subject Zkc.Subject.Print
open Core

/-- The claims of goals of one scheme, with what their statements need beside them: the labels
of the functions that the text names. The deciding role is the verifier of the claims' scheme;
the text names it `verifierRole` and the prover `proverRole`. The goals of the statements are
those of the claims. -/
structure Statements where
  claims : GoalClaims
  /-- The functions of the package before the root that the text names, each with the label of
  its name (`apply` gives `applyMember`): what the root may call. -/
  functions : List (String × Nat) := []

/-- How the text of a module establishes the claim of a goal. -/
inductive Method where
  /-- By the judgment with fees: the text proves `<goal>_judged : <goal>Judged`, and the claim
  is concluded from it by a theorem that is generated. -/
  | fees
  /-- The text proves `<goal>_installed : <goal>Claim` itself. -/
  | direct
  deriving DecidableEq

/-- The proofs that an author writes for a protocol: their text, the modules that they use
beside those of the generator and of the model, and the names of their theorems, whose axioms
the module asks Lean to report. -/
structure ProofText where
  text : String := ""
  imports : List String := []
  theorems : List String := []
  /-- How the text establishes the claim of each goal. -/
  method : Method := .fees

/-- The names that a text, and a consumer after it, may use. -/
def opens : String :=
  "open ZkcFormal ZkcFormal.ProbabilisticProcess ZkcFormal.Written OracleComp ProbComp\n" ++
  "open Zkc.Subject (CapTable UseCaps DrawCap CallCap)\n" ++
  "open scoped NNRat ENNReal\n"

/-- Imports for the shared scope, including a consumer challenge with minimal statements. -/
def statementOpenImports : List String :=
  ["Zkc.Subject.Charges", "ZkcFormal.Written.StandardInterpretation"]

/-- Names shared by the statements, proof text and consumer challenge. -/
def statementOpens : String := opens ++
  "open ZkcFormal.Written.StandardInterpretation (F G D model samplers served large)\n" ++
  "open scoped ZkcFormal.Written.ScalarField\n"

/-- A theorem that a check writes after the closing theorems of a proof module: a consumer of
the published theorems, as a reader of the source could write it. It is given in parts, so
that its statement can stand in the challenge with no proof (`Module.challenge`): the lines
before it (a section and its variables), its signature from `theorem` up to the `:=`, its
proof, and the lines after it. The statement is elaborated on both sides and compared as
terms, so it should make no auxiliary declaration (a `match`, a nested proof): a text with a
declaration of the same shape would have Lean reuse its own, and the pair would be refused. -/
structure Consumer where
  name : String
  before : String := ""
  signature : String
  proof : String
  after : String := ""
  imports : List String := []

/-- A consumer as it stands in the proof module. -/
def Consumer.text (c : Consumer) : String :=
  c.before ++ c.signature ++ " := " ++ c.proof ++ "\n" ++ c.after

/-- A consumer as it stands in the challenge: its statement, with no proof. -/
def Consumer.stated (c : Consumer) : String :=
  c.before ++ c.signature ++ " := by sorry\n" ++ c.after

/-- **The two modules of the goals of one scheme**, as Lean reads them: the module of the
statements, which holds everything that the generator states before a proof and no word of an
author, and the proof module, which imports it and holds the author's text with what is proved
after it. -/
structure Module where
  /-- The name space of the declarations of both modules. -/
  space : String
  /-- The name of the module of the statements, under which the proof module imports it. -/
  statementsName : Lean.Name
  /-- The module of the statements. It ends with a request for the axioms of each of its
  theorems. -/
  statements : String
  /-- The theorems of the module of the statements, in its order. -/
  stated : List String
  /-- What the module of the statements imports. -/
  statedImports : List String
  /-- The proof module: the import of the statements and of what the text asks for, the name
  space with the names that a text may use, the text, and what is proved after it. It asks for
  no axioms: a module that is accepted is judged by its published theorems, and a control appends
  `requests`. -/
  proof : String
  /-- The theorems of the proof module, in its order. -/
  proved : List String
  /-- What the proof module imports beside the module of the statements. -/
  proofImports : List String
  /-- The line of the proof module at which the author's text starts, the first line being 1,
  and the number of lines of the text. -/
  textLine : Nat
  textLines : Nat
  /-- The published theorems of the proof module, each with its proposition, under their full
  names. A check writes them as Lean prints a name and reads them again (`String.toName`
  reads the quotation of a component that is no identifier). -/
  published : List (Lean.Name × Lean.Name) := []
  /-- The consumers that a check wrote after the closing theorems, which are judged with the
  published theorems. -/
  consumers : List Consumer := []
  /-- Diagnostics for goals omitted because their reach has no standard interpretation. -/
  refusals : List String := []

/-- The challenge of a pair, as `lake comparator` takes one: a module that imports the module
of the statements and states each published theorem over its proposition, and each consumer
as the check wrote its statement, with no proof. It is the trusted side with the statements;
the proof module is the solution. A consumer is stated in the name space and under the names
that the proof module opens, so that its statement is read as it is there. -/
def Module.challenge (m : Module) : String :=
  let scope := if m.consumers.isEmpty then [] else statementOpenImports
  s!"import {m.statementsName}\n" ++
    String.join ((scope ++ m.consumers.flatMap (·.imports)).eraseDups.map (s!"import {·}\n")) ++
    String.join (m.published.map fun (theorem_, proposition) =>
      s!"theorem {theorem_} : {proposition} := by sorry\n") ++
    (if m.consumers.isEmpty then "" else
      s!"\nopen Zkc.Core\nnamespace {m.space}\n" ++ statementOpens ++ String.join (m.consumers.map (·.stated)) ++
        s!"end {m.space}\n")

/-- The theorems of a pair that the judgment is of: the published ones and the consumers,
under their full names. -/
def Module.judged (m : Module) : List Lean.Name :=
  m.published.map (·.1) ++ m.consumers.map fun c => .str m.space.toName c.name

/-- Requests for the axioms of the theorems of the proof module, by their full names: what a
control appends to the proof module, to read from Lean's reports which theorems are left
unproved. -/
def Module.requests (m : Module) : String :=
  String.join (m.proved.map fun theorem_ => s!"#print axioms {m.space}.{theorem_}\n")

/-- A module of one source, with the theorems whose axioms it asks for, in the order in which
the module states them. -/
structure PlainModule where
  text : String
  theorems : List String
  /-- Diagnostics for goals omitted because their reach has no standard interpretation. -/
  refusals : List String := []

namespace Statements

/-- The package of the claims. -/
def package (s : Statements) : SourcePackage := s.claims.emission.package ⟨[], [], [], [], []⟩

/-- The goals of a statements module share one root. Compute a value for the first goal
of each relation, retaining all the goals in source order. -/
def cacheRelations {ρ α : Type} (goals : List ρ) (key : ρ → InstanceId) (value : ρ → α) :
    Array (ρ × α) := Id.run do
  let mut results := #[]
  let mut cache : Std.HashMap InstanceId α := {}
  for g in goals do
    let relation := key g
    if let some v := cache[relation]? then
      results := results.push (g, v)
    else
      let v := value g
      cache := cache.insert relation v
      results := results.push (g, v)
  return results

def perRelation {α : Type} (goals : List ClaimedGoal) (value : ClaimedGoal → α) :
    Array (ClaimedGoal × α) :=
  cacheRelations goals (·.relation) value

/-- Issue covered goals of the package and retain a diagnostic for each uncovered goal.
A project primitive requires a model of its binding, even if another goal does not use it. -/
def coveredOccurrences (s : Statements) :
    Except String (List { g // g ∈ s.claims.goals } × List String) := do
  let p := s.package
  if let (primitive, _) :: _ := p.bindings.rows then
    throw s!"a written statement for a package that links a project primitive {primitive.name} is not issued yet: there is no model of the primitive"
  let mut goals := #[]
  let mut refusals := #[]
  let decisions := cacheRelations s.claims.goals.attach (·.val.relation) fun g =>
    Coverage.missing (b := p.bindings) p.named ⟨s.claims.root⟩ ⟨g.val.relation⟩
  for (g, decision) in decisions do
    match decision with
    | none => goals := goals.push g
    | some missing =>
      let reason := match missing with
        | .definition k => s!"missing definition {k.number}"
        | .sort k => s!"no carrier for sort {linkedTypeKey k}"
        | .row k => s!"no interpretation of row {linkedRowKey k}"
        | .law k t => s!"no sampler for law {lawKey k} at {linkedTy t}"
      refusals := refusals.push s!"{g.val.goal}: {reason}"
  if goals.isEmpty && !refusals.isEmpty then throw ("\n".intercalate refusals.toList)
  return (goals.toList, refusals.toList)

/-- The keys of the definitions of the package in order, and whether each is a protocol. -/
def definitions (s : Statements) : List (Nat × Bool) :=
  (definitionKeys s.package.named).map fun (key, isProtocol) => (key.number, isProtocol)

/-- The name, in the package, of the program before the definition with a key. -/
def programBefore (s : Statements) (key : Nat) : String :=
  match (s.definitions.takeWhile (·.1 != key)).getLast? with
  | some (before, _) => s!"program{before}"
  | none => s!"program{baseSuffix}"

/-- The place of a definition among those of its kind in the installed program, which stand
last first: as many places after the head as definitions of its kind follow it. -/
def memberOf (s : Statements) (key : Nat) (isProtocol : Bool) : String :=
  memberAt (((s.definitions.dropWhile (·.1 != key)).drop 1).filter (·.2 == isProtocol)).length

/-- Whether a name of the source can stand in a generated name as it is: letters of the basic
alphabet, digits and underscores, not beginning with a digit. A name of the source may be any
identifier of Unicode, of which Lean reads some as other tokens. -/
def plainName (name : String) : Bool :=
  !name.isEmpty && name.all (fun c => c.isAlphanum || c == '_') && !name.front.isDigit

/-- Keep ordinary source labels readable. Escaped labels use an apostrophe, which cannot
occur in a source identifier. The prefixes `at_` and `site_` introduce generated declarations. -/
def usableSourceLabel (name : String) : Bool :=
  plainName name && name != "at" && !name.startsWith "at_" && name != "site" &&
    !name.startsWith "site_" && !name.contains "_cap_" && !name.endsWith "_cap"

/-- A goal keeps its source spelling for diagnostics and source readback. Its Lean label
also has to coexist with the protocol root, the verifier entry and other generated names. -/
def labelOfSpelling (spelling : String) : String :=
  if usableSourceLabel spelling && !spelling.endsWith "_claim_of" then spelling
  else "goal'" ++ String.join (spelling.toList.map fun c =>
    if c.isAlphanum then String.singleton c else s!"'{c.toNat}'")

def _root_.Zkc.Frontend.Written.ClaimedGoal.label (goal : ClaimedGoal) : String :=
  labelOfSpelling goal.goal

/-- The relation aliases and transfer lemma share a namespace with fixed protocol facts.
Keep `root_sound` and `verifier_sound` under their source names in the public challenge. -/
def _root_.Zkc.Frontend.Written.ClaimedGoal.relationLabel (goal : ClaimedGoal) : String :=
  if goal.goal == "root" || goal.goal == "verifier" then "relation'" ++ goal.goal else goal.label

/-- Functions before the root keep their source labels where unique. The key in a fallback
label belongs to this package. Retain the ordinary numbered fallback when available. -/
def _root_.Zkc.Frontend.Written.GoalClaims.functionsBeforeRoot (claims : GoalClaims) :
    List (String × Nat) :=
  let definitions := definitionKeys claims.emission.named
  let before := (definitions.takeWhile (·.1.number != claims.root)).filter (!·.2)
  let named : List (String × Nat) := before.map fun (key, _) =>
    let name := match claims.state.table.allocatedKey? key.number with
      | some instanceKey => claims.state.program.nameOf instanceKey.declaration
      | none => ""
    (name, key.number)
  let reserved := claims.goals.foldl (fun names goal => names.insert goal.label)
    (Std.HashSet.ofList ["root", "callee", "verifier", "prover", "site"])
  let (sourceNames, taken) := named.foldl (init := (∅, reserved)) fun (seen, taken) (name, _) =>
    ((seen : Std.HashSet String).insert name, if seen.contains name then taken.insert name else taken)
  let (_, labels) := named.foldl (init := (reserved, #[])) fun (used, labels) (name, key) => Id.run do
    let numbered := s!"{name}{key}"
    let label :=
      if usableSourceLabel name && !taken.contains name then name
      else if usableSourceLabel name && !sourceNames.contains numbered && !used.contains numbered then numbered
      else s!"function'{key}"
    return (used.insert label, labels.push (label, key))
  labels.toList

/-- The place of a function among the functions of the program before the root, which stand
last first. -/
def calleeMember (s : Statements) (key : Nat) : String :=
  let before := s.definitions.takeWhile (·.1 != s.claims.root)
  memberAt (((before.dropWhile (·.1 != key)).drop 1).filter (!·.2)).length

/-- What was read from the source, as terms: the root, the roles, the functions before the root
that the text names, and for each goal its proof arguments, its table of caps and its
relation. -/
def factsOf (s : Statements) (layout : SubjectLayout s.claims) : String :=
  let root := s.claims.root
  s!"abbrev rootKey : Key := ⟨{root}⟩\n" ++
  s!"noncomputable abbrev rootHeader := header{root}\n" ++
  s!"noncomputable abbrev rootNames := names{root}\n" ++
  s!"noncomputable abbrev rootBody := body{root}\n" ++
  s!"noncomputable abbrev calleeProgram : Typed V := {s.programBefore root}\n" ++
  s!"noncomputable abbrev rootMember : Member installed.headers.protocols header{root} :=\n" ++
  s!"  {s.memberOf root true}\n" ++
  s!"abbrev verifierRole : Role := {s.claims.verifier}\n" ++
  s!"abbrev proverRole : Role := {s.claims.prover}\n" ++
  String.join (s.functions.map fun (label, key) =>
    s!"noncomputable abbrev {label}Header := header{key}\n" ++
    s!"noncomputable abbrev {label}Member : Member calleeProgram.headers.fns header{key} :=\n" ++
    s!"  {s.calleeMember key}\n") ++
  layout.goalFacts ClaimedGoal.label ++
  layout.relationFacts ClaimedGoal.relationLabel (fun key => s.memberOf key false)

/-- Root, relation, cap and argument names for a module that only needs facts. -/
def facts (s : Statements) (goals := s.claims.goals.attach) : String :=
  s.factsOf (.ofGoals s.claims goals)

/-- The deciding role of the installed root, as a projected program with its entry equation. -/
def verifierEntry : String :=
  let label := "verifier"
  "noncomputable section\n\n" ++
      s!"-- The program of the {label}, in the kernel's normal form.\n" ++
      s!"kernel_normal {label}Program :\n" ++
      s!"    Term (roleDialect V calleeProgram.headers {label}Role) (Ctx.empty.extend rootNames) rootHeader.outs :=\n" ++
      s!"  project {label}Role rootBody\n\n" ++
      s!"/-- The process of the {label} in a run of the installed program is the denotation of its\n" ++
      "program. -/\n" ++
      s!"theorem {label}_meaning (M : Model V) (path : List Frame)\n" ++
      s!"    (inputs : HList (RV M {label}Role) rootHeader.ins) :\n" ++
      s!"    roleMeaning M installed rootMember {label}Role path inputs =\n" ++
      s!"      ({label}Program.denote (roleSem M {label}Role (Defs.fnTable M calleeProgram.defs)\n" ++
      s!"        (Defs.rTable M calleeProgram.defs)) path (Env.empty.extend rootNames inputs)).sealed := by\n" ++
      s!"  rw [Process.sealed_eq, {label}Program.eq]\n" ++
      s!"  exact roleMeaning_entry M installed rootMember {label}Role path inputs\n\n" ++ "end\n\n"

/-- Specialize the package transport to the installed root and relations. Each distinct
lookup has one kernel proof, including when several source labels name the same relation. -/
def transfers (s : Statements) (goals := s.claims.goals) : String := Id.run do
  let admitted := "{a : Admitted V} (admitted : admit stored association = .ok a)"
  let root := "rootKey rootMember found'root"
  let mut text :=
    "theorem found'root : installed.findProtocol rootKey = some ⟨rootHeader, rootMember⟩ := by kernel_rfl\n" ++
    s!"abbrev at_root {admitted} :=\n  subjectPackage.atProtocol admitted {root}\n\n"
  for (goal, first) in perRelation goals (·.relationLabel) do
    let name := goal.relationLabel
    let found := s!"found'fn{goal.relation}"
    if name == first then
      text := text ++ s!"theorem {found} : installed.find {name}Key = some (.fn {name}Member) := by kernel_rfl\n"
    text := text ++ s!"abbrev at_{name} {admitted} :=\n" ++
      s!"  subjectPackage.atProtocolAndFunction admitted {root} {name}Key {name}Member {found}\n\n"
  return text

/-- The total of a goal's table of caps, as the frontend computes it. -/
def _root_.Zkc.Frontend.Written.ClaimedGoal.total (goal : ClaimedGoal) : Rat := goal.caps.ratio

/-- The ceilings of the goals (GL4): a goal that states a ceiling is issued a statement only when
the total of its table of caps is within it. A source whose charges add up to more than its goal
promises gets no statement, and is told the two numbers. -/
def checkCeilings (s : Statements) (goals := s.claims.goals) : Except String Unit := do
  for goal in goals do
    let some ceiling := goal.ceiling | continue
    unless goal.total ≤ ceiling do
      throw (s!"GL4: the goal `{goal.goal}` states the ceiling {ceiling}, and the total of its " ++
        s!"charges is {goal.total}")

/-- For each goal, what the module states of its table before any proof: the counts of the table
are those of the stored program (`<goal>_counted`), and its budget is the number that the
frontend computed (`<goal>_budget`), both decided by the kernel. The second ties the total of a
statement to the number that GL4 compares with a ceiling and that a reader can write down. -/
def counts (s : Statements) (goals := s.claims.goals) : String :=
  String.join (goals.map fun goal =>
    let name := goal.label
    let total := goal.total
    s!"/-- The table of caps of `{name}` adds up as the stored program does: its counts and its arms are the program's. -/\n" ++
    s!"theorem {name}_counted : {name}Caps.counted stored rootKey = true := by decide +kernel\n\n" ++
    s!"/-- The budget of the table of caps of `{name}`: the number that the frontend computed. -/\n" ++
    s!"theorem {name}_budget : {name}Caps.budget = (({total.num.toNat} : ℕ) : ℚ≥0) / ({total.den} : ℕ) := by\n" ++
    "  decide +kernel\n\n")

/-- The names of the theorems that `counts` writes. -/
def countNames (s : Statements) (goals := s.claims.goals) : List String :=
  goals.flatMap fun goal => [s!"{goal.label}_counted", s!"{goal.label}_budget"]

/-- For each goal with a ceiling, the theorem `<goal>_ceiling`: the total of the goal's table is
within the ceiling, the comparison decided by the kernel. -/
def ceilings (s : Statements) (goals := s.claims.goals) : Except String String := do
  s.checkCeilings goals
  let mut text := ""
  for goal in goals do
    let some ceiling := goal.ceiling | continue
    let name := goal.label
    text := text ++
      s!"/-- The total of the charges of `{name}` is within the ceiling that the goal states. -/\n" ++
      s!"theorem {name}_ceiling : {name}Caps.total ≤ (({ceiling.num.toNat} : ℕ) : ℝ≥0∞) / ({ceiling.den} : ℕ) :=\n" ++
      s!"  {name}Caps.total_le_div {ceiling.num.toNat} {ceiling.den} (by decide) (by decide +kernel)\n\n"
  return text

/-- Each goal has a coverage theorem. Goals with the same entries reuse the first proof. -/
def coverage (goals : List ClaimedGoal) : String := Id.run do
  let mut text := ""
  for (g, firstGoal) in perRelation goals (·.label) do
    let proof := if g.label == firstGoal then "by decide +kernel" else s!"{firstGoal}_covered"
    text := text ++ s!"theorem {g.label}_covered : StandardInterpretation.covers stored rootKey {g.relationLabel}Key = true := {proof}\n\n"
  return text

/-- The declarations against which a deployed input spelling is disambiguated for this label. -/
def originFor (g : ClaimedGoal) : String :=
  s!"written'origins ({g.label}Caps, {g.relationLabel}Member, {g.label}Witnessed)"

/-- Apply a library definition to one resolved goal in the standard interpretation. -/
def denotation (property row : String) : String :=
  s!"ZkcFormal.Written.Goal.{property} StandardInterpretation.model {row} StandardInterpretation.draws"

/-- The five public propositions. Their mathematical definitions and the checked presentation
of the concrete verifier inputs and relation witnesses belong to the formal library. -/
def claimTexts {owner : GoalClaims} (layout : SubjectLayout owner) : String := Id.run do
  let mut text := ""
  for (goal, row) in layout.namedGoals do
    let name := goal.label
    let relation := goal.relationLabel
    let origin := originFor goal
    text := text ++ s!"noncomputable def {name}ClaimOf (p : Typed V)\n" ++
      s!"    (root : Member p.headers.protocols rootHeader) (relation : Member p.headers.fns {relation}Header) : Prop :=\n" ++
      s!"  goal_surface% claim {origin} StandardInterpretation.samplers in ({denotation "ClaimOf" row} p root relation)\n\n" ++
      s!"def {name}Claim : Prop := {name}ClaimOf installed rootMember {relation}Member\n\n" ++
      s!"def {name}Goal : Prop := ZkcFormal.Written.Goal.checkedSurface\n" ++
      s!"  (ZkcFormal.Written.Goal.admittedAt {row} {name}ClaimOf)\n" ++
      s!"  (ZkcFormal.Written.Goal.admission stored association rootHeader rootKey {relation}Header {relation}Key {name}ClaimOf) rfl\n\n" ++
      s!"def {name}Result : Prop := ZkcFormal.Written.Goal.checkedSurface\n" ++
      s!"  (ZkcFormal.Written.Goal.resultOf {row} StandardInterpretation.covers {name}Goal)\n" ++
      s!"  (ZkcFormal.Written.Goal.countedResult stored rootKey {relation}Key {name}Caps StandardInterpretation.covers {name}Goal) rfl\n\n" ++
      s!"def {name}Witnessed : Prop :=\n  goal_receipt% {origin} in ({denotation "Witnessed" row})\n" ++
      s!"    using ({denotation "witnessed_of" row} StandardInterpretation.served)\n\n"
  return text

/-- The name of a draw of the root in a module: the name of its site in the source, with
its place among the draws that realize the site where a stepped loop gives several. -/
def siteLabel (site : String) (index count : Nat) : String :=
  if count == 1 then site else s!"{site}_{index}"

/-- The named draws of a goal's root, each with the name of its site in the source, its name
in a module and its key. The name in a module is the site's (`siteLabel`) where that is a plain
name, and `key<number>` of the draw where it is not. A name that two charged draws would share
(a site `r_0` beside the first draw of a stepped loop over `r`) is followed by the key of each.
The name of a charged draw does not depend on the draws that the contract does not charge: a
draw without a charge whose name another draw has is the one that is followed by its key. -/
def _root_.Zkc.Frontend.Written.ClaimedGoal.siteLabels (goal : ClaimedGoal) :
    List (String × String × Core.Key) :=
  let capped := (goal.caps.uses.getLast?.map (·.draws)).getD []
  let charged := Std.HashSet.ofList (capped.map (·.key.number))
  let draws := goal.sites.flatMap fun (site, keys) =>
    keys.zipIdx.map fun (key, index) =>
      let label := if plainName site then siteLabel site index keys.length else s!"key{key.number}"
      -- Applied sites reserve labels beginning with site_ and a numeric address.
      let reserved := label.startsWith "site_" && (label.drop 5).front?.any Char.isDigit
      (site, if reserved then s!"draw'{key.number}" else label, key)
  let disambiguate (draws : List (String × String × Core.Key)) (fallback : String → Nat → String) :=
    let counts := draws.foldl (init := ({} : Std.HashMap String (Nat × Nat))) fun counts (_, label, key) =>
      let (all, paid) := counts[label]?.getD (0, 0)
      counts.insert label (all + 1, paid + (if charged.contains key.number then 1 else 0))
    draws.map fun (site, label, key) =>
      let (all, paid) := counts[label]?.getD (0, 0)
      let shared := (if charged.contains key.number then paid else all) > 1
      (site, if shared then fallback label key.number else label, key)
  -- A source site can itself be called r_0_key0. The final fallback is disjoint from
  -- every source spelling and unique by instruction key.
  let numbered := disambiguate draws fun label key => s!"{label}_key{key}"
  disambiguate numbered fun _ key => s!"draw'{key}"

/-- The draws of a goal's root that its table of caps gives a cap, each with its name
in a module and that cap. -/
def _root_.Zkc.Frontend.Written.ClaimedGoal.siteCaps (goal : ClaimedGoal) :
    List (String × DrawCap) :=
  let capped := (goal.caps.uses.getLast?.map (·.draws)).getD []
  goal.siteLabels.filterMap fun (_, label, key) =>
    (capped.find? (·.key == key)).map fun cap => (label, cap)

/-- The name, in a module, of a draw below applications of the root: `site_`, then the keys of
the applications in their order, then the key of the draw. A number follows `site_`, where the
name of a draw of the root has the name of a site of the source or `key`, so the two never
meet. -/
def appliedSite (site : Core.Site) : String :=
  "site_" ++ "_".intercalate ((site.through ++ [site.key]).map fun key => toString key.number)

/-- The draws of the root under the names of their sites: the key of each
(`site_<name>`, and `site_<name>_<index>` for each block of a stepped loop), once for the
package, and for each goal the cap that its table gives the draw (`<goal>_cap_<name>`), decided
by the kernel. The label `walk_cap` identifies the equations giving those caps. -/
def sites (s : Statements) (goals := s.claims.goals) : String :=
  let named := (goals.flatMap (·.siteLabels)).eraseDups
  String.join (named.map fun (site, label, key) =>
    s!"/-- A draw of the root: `sites.{site}` of the source. -/\n" ++
    s!"abbrev site_{label} : Key := ⟨{key.number}⟩\n\n") ++
  String.join (goals.map fun goal =>
    String.join (goal.siteCaps.map fun (label, cap) =>
      s!"/-- The cap that the table of `{goal.label}` gives the draw `{label}`. -/\n" ++
      s!"@[walk_cap]\ntheorem {goal.label}_cap_{label} :\n" ++
      s!"    {goal.label}Caps.capFrom {goal.label}Caps.root [] site_{label} = " ++
      s!"{cap.numerator} / {cap.denominator} := by\n  decide +kernel\n\n")) ++
  -- the draws below applications: a draw is charged in the contract of the protocol that has
  -- it, and the table gives the root its cap through the applications that reach it
  let applied := (goals.flatMap fun goal =>
    (goal.caps.sites.filter (!·.1.through.isEmpty)).map (·.1)).eraseDups
  String.join (applied.map fun site =>
    s!"/-- A draw below the applications {site.through.map (·.number)} of the root: the draw with\n" ++
    s!"key {site.key.number} of the protocol that the last of them applies. -/\n" ++
    s!"abbrev {appliedSite site} : Key := ⟨{site.key.number}⟩\n\n") ++
  String.join (goals.map fun goal =>
    String.join ((goal.caps.sites.filter (!·.1.through.isEmpty)).map
      fun (site, numerator, denominator, _) =>
        let through := ", ".intercalate (site.through.map fun key => s!"⟨{key.number}⟩")
        s!"/-- The cap that the table of `{goal.label}` gives the draw `{appliedSite site}`. -/\n" ++
        s!"@[walk_cap]\ntheorem {goal.label}_cap_{appliedSite site} :\n" ++
        s!"    {goal.label}Caps.capFrom {goal.label}Caps.root [{through}] {appliedSite site} = " ++
        s!"{numerator} / {denominator} := by\n  decide +kernel\n\n"))

/-- The names of the theorems that `sites` writes. -/
def siteNames (s : Statements) (goals := s.claims.goals) : List String :=
  goals.flatMap fun goal =>
    (goal.siteCaps.map fun (label, _) => s!"{goal.label}_cap_{label}") ++
    ((goal.caps.sites.filter (!·.1.through.isEmpty)).map fun (site, _) =>
      s!"{goal.label}_cap_{appliedSite site}")

/-- The fees judgment and both library proofs at the same resolved goal. -/
def judgments {owner : GoalClaims} (layout : SubjectLayout owner) : String := Id.run do
  let mut text := ""
  for (goal, row) in layout.namedGoals do
    let name := goal.label
    let origin := originFor goal
    let witness := s!"{denotation "witnessed_of" row} StandardInterpretation.served"
    text := text ++ s!"def {name}Judged : Prop :=\n" ++
      s!"  goal_surface% judged {origin} StandardInterpretation.samplers in ({denotation "Judged" row})\n\n" ++
      s!"theorem {name}_claim_of_judged (judged : {name}Judged) : {name}Claim :=\n" ++
      s!"  {denotation "claim_of_judged" row} judged\n\n" ++
      s!"theorem {name}_witnessed_of :\n" ++
      s!"    goal_helper% {origin} in ({witness}) returning {name}Witnessed :=\n  {witness}\n\n"
  return text

/-- The names of the theorems that `judgments` writes. -/
def judgmentNames (s : Statements) (goals := s.claims.goals) : List String :=
  goals.flatMap fun goal =>
    [s!"{goal.label}_claim_of_judged", s!"{goal.label}_witnessed_of"]

/-- A publication in the goal's namespace. Its closing, when generated after the author text,
gives the documentation and proof of the named proposition. -/
structure Publication where
  name : String
  proposition : String
  closing : Option (String × String) := none

/-- The installed claim, when requested, and the publications that follow it. -/
def goalPublications (goal : ClaimedGoal) (method : Method) (witnessesOnly : Bool) :
    Option Publication × List Publication := Id.run do
  let n := goal.label
  let witness : Publication := ⟨n ++ "_met", n ++ "Witnessed",
    some (s!"The hypotheses of the claim of `{n}` are met.", s!" {n}_witnessed")⟩
  if witnessesOnly then return (none, [witness])
  let installed := match method with
    | .fees => some (s!"The claim of `{n}`, from the judgment that the text established.",
        s!"\n  {n}_claim_of_judged {n}_judged")
    | .direct => none
  return (some ⟨n ++ "_installed", n ++ "Claim", installed⟩, [
    ⟨n ++ "_sound", n ++ "Goal", some (s!"The goal `{n}`, for every admitted program.",
      s!"\n  fun admitted => at_{goal.relationLabel} admitted {n}ClaimOf ({n}_installed : {n}Claim)")⟩,
    ⟨n ++ "_result", n ++ "Result", some (s!"The result of the goal `{n}`.",
      s!" ⟨{n}_covered, {n}_counted, {n}_sound⟩")⟩, witness])

def Publication.closingText (p : Publication) : String :=
  match p.closing with
  | none => ""
  | some (doc, proof) => s!"/-- {doc} -/\ntheorem {p.name} : {p.proposition} :={proof}\n\n"

def Publication.pair (p : Publication) (space : Lean.Name) : Lean.Name × Lean.Name :=
  (.str space p.name, .str space p.proposition)

/-- The names of the theorems that `ceilings` writes. -/
def ceilingNames (s : Statements) (goals := s.claims.goals) : List String :=
  goals.filterMap fun goal => goal.ceiling.map fun _ => s!"{goal.label}_ceiling"

/-- The modules that a module of statements imports: those of the printed package, those of
the library that the generated statements name, and the model's. -/
def imports (withEntries : Bool) : List String :=
  subjectPackageImports ++ (if withEntries then ["Zkc.Core.Evidence.ProtocolReadback"] else []) ++
    ["Zkc.Subject.WrittenGoal", "ZkcFormal.Written.GoalPresentation",
      "ZkcFormal.OracleProcess", "ZkcFormal.ReturnExperiment", "ZkcFormal.Written.LawSamplers",
      "ZkcFormal.Written.SiteCaps", "ZkcFormal.Written.FunctionMeaning"] ++ statementOpenImports

/-- The lines that open a module: its imports, and the namespace of the core. -/
def header (modules : List String) : String :=
  String.join (modules.map (s!"import {·}\n")) ++ "\nopen Zkc.Core\n"

/-- The requests for the axioms of theorems, and the end of the module's name space. -/
def footer (name : String) (theorems : List String) : String :=
  String.join (theorems.map (s!"#print axioms {·}\n")) ++ s!"end {name}\n"

/-- **The modules of the goals of one scheme.**

*The module of the statements* (`<name>.Stated`): the package of the claims and what is
generated before any proof (the facts, the transfers, the propositions of each goal, the
coverage, the counts, the names of the draws and, for a text of the
method of fees, the judgment of each goal with what follows from it, and the comparisons with
the ceilings), with a request for the axioms of each of its theorems. No word and no choice of
an author is in it, and it imports nothing that a text asks for.

*The proof module* imports it, with what the text and the check ask for, and holds, in the name
space of the statements: the author's text; the claim of each goal from the text's judgment,
for the method of fees; the closing theorems; and what a check writes after them (`after`: a
consumer of the published theorems).

This function fixes the order of the parts, the imports and the names of the generated
theorems. It checks coverage before issuing each goal.

**What a check rests on.** A text is arbitrary Lean: it can turn off the kernel's check of its
declarations, write into the kernel's environment, and declare a variable that becomes a
hypothesis of the theorems after it, and Lean then accepts the proof module and reports no
axiom. So Lean's acceptance of the proof module is not what a check of a subject rests on. The
two modules are the trusted and the untrusted side of a judgment that the toolchain makes
(`lake comparator`, Lean's own way to judge a proof that may be malicious): the module of the
statements and the challenge (`Module.challenge`: each published theorem stated over its
proposition, with no proof) are written by the generator and hold no word of an author; the
proof module is the solution. A check builds and exports the trusted side before any text is
read, builds the solution confined, and gives the two exports to the comparator
(`ZkcFormalTests.SubjectProject`), which loads no object: each published theorem of the
solution has the statement of the challenge, with every definition that the statement uses, the
kernel accepts the solution, and the published theorems rest on the allowed axioms.

What is trusted is then Lean's logic and a kernel, the comparator and the exporter, the
sandbox in which a text is read, the imports as built, and this generator and the frontend, for
the statements saying what the source claims. A statement that a check itself writes after the
text (a `Consumer`, with its numerals and notations) stands in the challenge as well, read
there in the name space and under the names that the generator opens, and is judged with the
published theorems; in the proof module it is read in the scope that the text leaves, and a
text that changes what it says there is refused by its statement.

`statements` names the module of the statements where it is not `<name>.Stated`: a control
whose statements differ from its subject's keeps the subject's name space and has a module of
statements of its own. With `witnessesOnly`, the challenge and proof publish only the witness
of each goal; the issued statements are the same. -/
def module (s : Statements) (name : String) (proof : ProofText)
    (withEntries := true) (after : List Consumer := [])
    (statements : Option Lean.Name := none) (witnessesOnly := false) :
    Except String Module := do
  let (retained, refusals) ← s.coveredOccurrences
  let layout := SubjectLayout.ofGoals s.claims retained
  let goals := layout.publicGoals
  let subject ← layout.text
  let ceilings ← s.ceilings goals
  let fees := proof.method == .fees
  let feeText := if fees then judgments layout else ""
  let stated := ["admitted_exists"] ++ goals.map (s!"{·.label}_covered") ++ s.countNames goals ++ s.siteNames goals ++
    (if withEntries then ["verifierProgram.eq", "verifier_meaning"] else []) ++
    (if fees then s.judgmentNames goals else []) ++
    s.ceilingNames goals
  let stating := header (imports withEntries) ++ s!"namespace {name}\n" ++
    subjectPackage s.package ++ statementOpens ++ s.factsOf layout ++ "\n" ++ s.transfers goals ++
    subject ++ claimTexts layout ++
    coverage goals ++ s.counts goals ++ s.sites goals ++ (if withEntries then verifierEntry else "") ++
    feeText ++ ceilings ++ footer name stated
  let statementsName : Lean.Name := statements.getD (.str name.toName "Stated")
  let byGoal := goals.map (goalPublications · proof.method witnessesOnly)
  let publications := byGoal.flatMap fun (claim, rest) => claim.toList ++ rest
  -- The proof module establishes the installed claims before the remaining closings.
  let generated := (byGoal.filterMap Prod.fst ++ byGoal.flatMap Prod.snd).filter (·.closing.isSome)
  let proofImports := ("ZkcFormal.Written.ClaimIntro" :: proof.imports ++ after.flatMap (·.imports)).eraseDups
  -- the proof module reopens the name space and the names that the statements were read with
  let opening := header (toString statementsName :: proofImports) ++ s!"namespace {name}\n" ++ statementOpens
  let text := opening ++ proof.text ++ "\n" ++
    String.join (generated.map Publication.closingText) ++ String.join (after.map (·.text)) ++ s!"end {name}\n"
  return {
    space := name, statementsName, statements := stating, stated, statedImports := imports withEntries
    proof := text
    proved := proof.theorems ++ generated.map (·.name) ++ after.map (·.name)
    proofImports
    textLine := (opening.splitOn "\n").length
    textLines := (proof.text.splitOn "\n").length
    published := publications.map (·.pair name.toName)
    consumers := after, refusals }

/-- A module with the package of the claims and the propositions of the goals alone: the facts,
the transfers and the propositions, with nothing proved. Lean elaborates the statements. -/
def claimsModule (s : Statements) (name : String) :
    Except String PlainModule := do
  let (retained, refusals) ← s.coveredOccurrences
  let layout := SubjectLayout.ofGoals s.claims retained
  let text := header (imports false) ++ s!"namespace {name}\n" ++
    subjectPackage s.package ++ statementOpens ++ s.factsOf layout ++ "\n" ++ s.transfers layout.publicGoals ++
    (← layout.text) ++ claimTexts layout ++ s!"end {name}\n"
  return {text, theorems := [], refusals}

/-- A module with the package of the claims and the coverage theorems of its issued goals. -/
def coverageModule (s : Statements) (name : String) :
    Except String PlainModule := do
  let (retained, refusals) ← s.coveredOccurrences
  let layout := SubjectLayout.ofGoals s.claims retained
  let goals := layout.publicGoals
  let theorems := goals.map (s!"{·.label}_covered")
  let text := header (imports false) ++ s!"namespace {name}\n" ++
    subjectPackage s.package ++ statementOpens ++ s.factsOf layout ++ "\n" ++
    coverage goals ++ footer name theorems
  return {text, theorems, refusals}

/-- A module with the package of the claims, its facts, and the comparison of each goal's total
with the ceiling that it states. A goal whose ceiling is below its total gives no module. -/
def ceilingModule (s : Statements) (name : String) : Except String PlainModule := do
  let layout := SubjectLayout.ofGoals s.claims
  let goals := layout.publicGoals
  let ceilings ← s.ceilings goals
  let text := header (subjectPackageImports ++ ["Zkc.Subject.WrittenGoal", "ZkcFormal.Written.SiteCaps"]) ++
    s!"namespace {name}\n" ++ subjectPackage s.package ++ opens ++ s.factsOf layout ++ "\n" ++
    ceilings ++ footer name (s.ceilingNames goals)
  return { text, theorems := s.ceilingNames goals }

end Statements

end Zkc.Frontend.Written
