module

public import Zkc.Frontend.Written.Subject
public import Zkc.Frontend.Written.Charge
public import Zkc.Subject.Coverage
public import Zkc.Frontend.Written.Package

@[expose] public section

/-!
What the issuer writes for written soundness goals, as the text of modules.

The goals of one scheme are published through the formal library (`Statements.publication`):

- *the data module* holds the printed package of the claims (`goalClaims`) and its installation;
  `factsOf`: the key, header and place of the root, the place of each relation and of each
  function before the root by its key, the verifier and the prover of the scheme, and each
  goal's table of caps, bound and fields, as terms; `lookups`: the root and each relation found
  in the installed program by their keys; and the typed subject
  (`SubjectLayout.text`): a short application and a decision for each clause, a row for each
  goal with the path of its declaration, its property, its bound (the ceiling that the goal
  writes, else the total of its charges) and its table of caps, and the source names of the root.
  It states no proposition about the protocol and imports no module of the formal library;
- *the challenge*, *the views module* and *the fees module* are their imports and one command
  of the formal library over the subject.

What a goal publishes, its named views and the facts of its table are the library's definitions
applied to the goal's row; the issuer writes none of them as text.

What the data say of a goal is read from the claims and from nothing that a caller gives beside
them: the deciding role is the verifier of the claims' scheme, the operands are the inputs of
the deployed header at the places that the claims give, and the proof arguments, the bound and
the table of caps are the goal's. No declaration of the data module is named after a name of
the source: a relation and a function before the root are named by their keys, and a goal by its
row. A goal whose clause is a `reduces` is not issued: the statement of a reduction is about a return
on which the reduced statement is true. A goal whose reach the standard interpretation does not
cover is not issued and is reported.
-/

namespace Zkc.Frontend.Written
open Zkc.Subject Zkc.Subject.Print
open Core

/-- The claims of goals of one scheme. The deciding role is the verifier of the claims' scheme;
the text names it `verifierRole` and the prover `proverRole`. The goals of the statements are
those of the claims. -/
structure Statements where
  claims : GoalClaims

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

/-- The functions of the package before the root, which the root may call: each with its name in
the source and its key. -/
def _root_.Zkc.Frontend.Written.GoalClaims.functionsBeforeRoot (claims : GoalClaims) :
    List (String × Nat) :=
  let definitions := definitionKeys claims.emission.named
  let before := (definitions.takeWhile (·.1.number != claims.root)).filter (!·.2)
  before.map fun (key, _) =>
    let name := match claims.state.table.allocatedKey? key.number with
      | some instanceKey => claims.state.program.nameOf instanceKey.declaration
      | none => ""
    (name, key.number)

/-- The functions before the root, by name in the source and key. -/
def functions (s : Statements) : List (String × Nat) := s.claims.functionsBeforeRoot

/-- The place of a function among the functions of the program before the root, which stand
last first. -/
def calleeMember (s : Statements) (key : Nat) : String :=
  let before := s.definitions.takeWhile (·.1 != s.claims.root)
  memberAt (((before.dropWhile (·.1 != key)).drop 1).filter (!·.2)).length

/-- What was read from the source, as terms: the root, the roles, the functions before the root
by their keys, and for each goal its table of caps, its bound and its fields, and the member of
its relation. A function before the root is `member'callee<key>`, a member of `calleeProgram`,
with the function's name in the source in its comment; a relation is `member'fn<key>`, a
member of `installed`. -/
def factsOf (s : Statements) (layout : SubjectLayout s.claims) : String :=
  let root := s.claims.root
  s!"abbrev rootKey : Key := ⟨{root}⟩\n" ++
  s!"noncomputable abbrev rootHeader := header{root}\n" ++
  (if s.functions.isEmpty then "" else
    s!"noncomputable abbrev calleeProgram : Typed V := {s.programBefore root}\n") ++
  s!"noncomputable abbrev rootMember : Member installed.headers.protocols header{root} :=\n" ++
  s!"  {s.memberOf root true}\n" ++
  s!"abbrev verifierRole : Role := {s.claims.verifier}\n" ++
  s!"abbrev proverRole : Role := {s.claims.prover}\n" ++
  String.join (s.functions.map fun (name, key) =>
    s!"/-- The function `{name}` of the source. -/\n" ++
    s!"noncomputable abbrev member'callee{key} : Member calleeProgram.headers.fns header{key} :=\n" ++
    s!"  {s.calleeMember key}\n") ++
  layout.goalFacts ++
  layout.relationFacts (fun key => s.memberOf key false)

/-- The lines that open a module: its imports, and the namespace of the core. -/
def header (modules : List String) : String :=
  String.join (modules.map (s!"import {·}\n")) ++ "\nopen Zkc.Core\n"

/-- The requests for the axioms of theorems, and the end of the module's name space. -/
def footer (name : String) (theorems : List String) : String :=
  String.join (theorems.map (s!"#print axioms {·}\n")) ++ s!"end {name}\n"

/-- The lookups of the installed root and relations that the typed subject is closed over: one
kernel proof for each distinct lookup. -/
def lookups (goals : List ClaimedGoal) : String := Id.run do
  let mut text :=
    "theorem found'root : installed.findProtocol rootKey = some ⟨rootHeader, rootMember⟩ := by kernel_rfl\n"
  for relation in (goals.map (·.relation)).eraseDups do
    text := text ++ s!"theorem found'fn{relation} : installed.find stored{relation}.key = some (.fn member'fn{relation}) := by kernel_rfl\n"
  return text ++ "\n"

/-- The modules that a data module imports: those of the printed package and the typed subject's.
No module of the formal library is among them. -/
def dataImports : List String := subjectPackageImports ++ ["Zkc.Subject.WrittenGoal"]

end Statements

/-- **The modules of the goals of one scheme, published through the formal library.**

*The data module* (`<name>.Stated`) holds the package of the claims and its installation, the
names of the installation, the lookups, and the typed subject with a row for each goal. It holds
no proposition about the protocol and imports no module of the formal library.

*The challenge*, *the views module* and *the fees module* are their imports and one line each:
`publish_goals`, `publish_views`, `publish_fees` over the subject. What a goal publishes is the
formal library's definition applied to the goal's row, named by the path of the goal's
declaration: `<name>.<path>.sound` and `<name>.<path>.met`.

*A proof module* is `opening`, an author's text and the end of the name space; the text states
each published theorem by `published%`. Nothing is generated after it.

The data module and the challenge are the trusted side of a judgment by `lake comparator` and
hold no word of an author; the views and the fees module are for proofs and readers, and the
challenge does not import them. -/
structure Publication where
  /-- The name space of the declarations of every module. -/
  space : String
  /-- The name of the data module. -/
  dataName : Lean.Name
  data : String
  /-- The theorems of the data module whose axioms it asks for. -/
  stated : List String
  challenge : String
  views : String
  fees : String
  /-- The start of a proof module: the imports of the data, views and fees modules and of the
  term for a published statement, the name space, and the names that a text may use. A published
  theorem is named by its goal's path, so the goal `sound` publishes `sound.sound`: the opening
  turns off the linter that reports a repeated component of a name. -/
  opening : String
  /-- The published theorems under their full names: `sound` and `met` of each row. -/
  published : List Lean.Name
  /-- Diagnostics for goals omitted because their reach has no standard interpretation. -/
  refusals : List String := []
  /-- For each goal that is issued without a table of caps, the limit of a table that its
  charges met. Such a goal writes its ceiling; its row holds no table and gets no fee facts. -/
  limits : List String := []

namespace Publication

/-- The names of the challenge, the views module and the fees module. -/
def challengeName (p : Publication) : Lean.Name := .str p.space.toName "Challenge"
def viewsName (p : Publication) : Lean.Name := .str p.space.toName "Views"
def feesName (p : Publication) : Lean.Name := .str p.space.toName "Fees"

/-- A proof module of an author's text. -/
def proof (p : Publication) (text : String) : String :=
  p.opening ++ text ++ s!"\nend {p.space}\n"

/-- The line of a proof module at which the author's text starts, the first line being 1. -/
def textLine (p : Publication) : Nat := (p.opening.splitOn "\n").length

end Publication

namespace Statements

/-- The data module of a layout of goals, in the name space `name`. `publication` writes it for
the goals whose reach is covered. -/
def dataModule (s : Statements) (name : String) (layout : SubjectLayout s.claims) :
    Except String String := do
  let subject ← layout.text
  return header dataImports ++ s!"namespace {name}\n" ++
    subjectPackage s.package ++ s.factsOf layout ++ "\n" ++ lookups layout.publicGoals ++ subject ++
    footer name ["admitted_exists"]

/-- **Issue the goals of one scheme through the formal library** (`Publication`). It checks
coverage before issuing each goal; a goal is issued at its bound, whatever its table of caps
adds up to. `imports` are the modules that an author's text asks for beside the generated ones.
`data` names the data module where it is not `<name>.Stated`: a control whose data differ from its
subject's keeps the subject's name space and has a data module of its own. -/
def publication (s : Statements) (name : String) (imports : List String := [])
    (data : Option Lean.Name := none) : Except String Publication := do
  let (retained, refusals) ← s.coveredOccurrences
  let layout := SubjectLayout.ofGoals s.claims retained
  let stated := ["admitted_exists"]
  let dataName : Lean.Name := data.getD (.str name.toName "Stated")
  let data ← s.dataModule name layout
  let line (library command : String) :=
    s!"import {dataName}\nimport {library}\n\n{command} {name}.written'subject\n"
  let opening := header ([toString dataName, s!"{name}.Views", s!"{name}.Fees", "ZkcFormal.Written.Publish"] ++
    statementOpenImports ++ imports) ++ s!"namespace {name}\n" ++
    "set_option linter.dupNamespace false\n" ++ statementOpens
  let published := layout.paths.flatMap fun path =>
    let row := path.foldl (fun n c => Lean.Name.str n c) name.toName
    [.str row "sound", .str row "met"]
  let limits := retained.filterMap fun goal =>
    goal.val.limit.map fun limit => s!"{goal.val.goal}: no table of caps: {limit.describe}"
  return {
    space := name, dataName, data, stated, limits
    challenge := line "ZkcFormal.Written.Publish" "publish_goals"
    views := line "ZkcFormal.Written.Views" "publish_views"
    fees := line "ZkcFormal.Written.FeeFacts" "publish_fees"
    opening, published, refusals }

end Statements

end Zkc.Frontend.Written
