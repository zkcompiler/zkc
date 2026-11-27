import Lean.Data.Json
import Zkc.Frontend.Written.Goals
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import ZkcFormalTests.SubjectProject
import ZkcFormalTests.WrittenBinding
import ZkcFormalTests.WrittenSource

/-!
A subject of a written soundness goal, as a check states it.

A subject is a source, the text of its proofs, what the check asserts of what the frontend
read of the source, and its controls. The checks of the subjects (`lean/formal/checks/*Charge.lean`)
give these as data and share what is here: how a source is read and what is asserted of the
reading (`Reading`, `read`), how the two modules of a subject are assembled (`Subject.module`),
how the modules of a check are built and its proof modules judged (`start`, `judged`), and how
a control is stated and judged (`Control`).

A control is the subject with its source or its text altered, in a module that must be refused: by Lean in the text, by Lean in
what is generated before the text, or by the judgment where Lean accepts it. It names the
theorems that are then left unproved and the texts of the places at which it is refused; with
`only` the module is refused at those places and at no other. A text is altered with
`replaceOnce` (`PrintedPackageSupport`), which fails when the place that it alters is gone.
-/

namespace ZkcFormalTests.WrittenSubject
open Zkc.Core Zkc.Frontend Zkc.Frontend.Written
open Zkc.Tests.Frontend Zkc.Tests.Frontend.PrintedPackageSupport

/-- What a check reads of a source: the source, and what its goals claim with what their
statements need. -/
structure Subject where
  text : String
  statements : Statements

namespace Subject

/-- The printed package of the claims. -/
def package (s : Subject) : String := (Written.package s.statements.package).text

/-- The goals of the subject, as the frontend read them. -/
def goals (s : Subject) : List ClaimedGoal := s.statements.claims.goals

/-- The one goal of a subject that has one. -/
def goal (s : Subject) : IO ClaimedGoal := do
  let [goal] := s.goals | throw (IO.userError "the statements are not of one goal")
  return goal

end Subject

/-- What a check asserts of what the frontend read of a source. Each is a fact that the proof
module takes as given: the ports of the root, the clause that every goal reads and the inputs
that its relation is applied to, the number of proof arguments of a goal, the roles of the
scheme. A relation with
witness parameters is not a subject yet: `read` asserts that the clause gives none. -/
structure Reading where
  /-- The goals, the first of which selects the root. -/
  goals : List String
  /-- The names of the ports of the root, in their order. -/
  ports : Array String
  /-- The clause that every goal reads, by the names of the source. -/
  clause : SourceClause.Seen
  /-- The inputs of the deployed header that the relation is applied to. -/
  operands : Array Nat
  /-- How many proof arguments each goal gives. -/
  arguments : Nat := 0
  /-- The verifier and the prover of the scheme, by the names of their roles. -/
  verifier : String := "V"
  prover : String := "P"


/-- A source read, with what the check asserts of the reading. A reading that is not what the
check asserts is an error of the check: the text of the proofs is written against it. -/
def read (text : String) (reading : Reading) : IO Subject := do
  let some first := reading.goals.head? | throw (IO.userError "a subject has a goal")
  let c ← IO.ofExcept (goalRoot text first)
  let head ← IO.ofExcept (SourceClause.rootHead c)
  unless head.ports.map (·.binder.name) == reading.ports do
    throw (IO.userError s!"the protocol has other ports than {reading.ports}")
  let claims ← IO.ofExcept (goalClaims c reading.goals)
  unless claims.goals.map (·.goal) == reading.goals do
    throw (IO.userError s!"the claims are not of the goals {reading.goals}")
  for claimed in claims.goals do
    let clause ← IO.ofExcept (SourceClause.seen c claimed.goal)
    unless clause == reading.clause do
      throw (IO.userError s!"goal {claimed.goal} reads another clause: {repr clause}")
    unless claimed.statement == reading.operands && claimed.witness == some #[] do
      throw (IO.userError s!"goal {claimed.goal}: the relation is applied to other inputs")
    unless claimed.specification.size == reading.arguments do
      throw (IO.userError s!"goal {claimed.goal}: not {reading.arguments} proof arguments")
  unless (head.roster[claims.verifier]?, head.roster[claims.prover]?) ==
      (some reading.verifier, some reading.prover) do
    throw (IO.userError "the verifier and the prover of the scheme are not the roles asserted")
  let statements : Statements := ⟨claims⟩
  return ⟨text, statements⟩

/-- The total of a goal's table of caps, as the frontend computes it, where the goal has a table:
what a check compares with the charges of its source. -/
def _root_.Zkc.Frontend.Written.ClaimedGoal.total (goal : ClaimedGoal) : Option Rat :=
  goal.caps.map (·.ratio)

/-- The axioms beyond which no theorem of a subject may rest. -/
def allowed : List String := ["propext", "Classical.choice", "Quot.sound"]

/-! ## The modules of a check in one project, built at once and judged

Lean's acceptance of a proof module is not what a check rests on: a text is arbitrary Lean, and
can turn off the kernel's check of its declarations or run a program while it is read
(`Statements.module` says how). A check writes its modules into a Lake project in its work
folder, and the project is settled as `ZkcFormalTests.SubjectProject` says: the statements and
the challenges are built and exported before any text is read, every text is read confined, and
the proof modules that the check accepts are judged by `lake comparator` on exports, each with
its challenge, which the generator writes, in one run for all of them.

A module is added before it is asked about: what a function here returns of a module (`Pending`)
is read when it is asked, and the first asking settles the project with everything that the
check added. A module added after that is an error.

A recipe judges once for all its checks: with `ZKC_SUBJECTS` naming a folder, a check writes
each pair that it accepts there instead, and leaves the judgment to the recipe's last step
(`checks/Judgment.lean`). The folder is read-only to every text, as everything outside a
project's `.lake` is. -/


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

/-- **A pair that the comparator judges**, as Lean reads its modules: the module of the
statements (the issuer's data module, with what a check states after it), which holds no word of
an author; the challenge; and the proof module. A check builds one from the issuer's publication
or by hand. -/
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
  /-- The proof module: the import of the statements and of what the text asks for, the name
  space with the names that a text may use, the text, and what is proved after it. It asks for
  no axioms: a module that is accepted is judged by its published theorems, and a control appends
  `requests`. -/
  proof : String
  /-- The theorems of the proof module, in its order. -/
  proved : List String
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
  /-- The issuer's challenge and the names of its theorems, for a pair made from a publication:
  the challenge is then this text, and the judgment is of these names. -/
  issued : Option (String × List Lean.Name) := none
  /-- The modules that the proof module imports beside the statements and that hold no word of an
  author (an issuer's views and fee facts): they go wherever the proof module goes. -/
  support : List (Lean.Name × String) := []

/-- The pair of what the issuer publishes with an author's text in the issuer's frame: the data
module, the issuer's challenge, and the proof module. -/
def Module.ofPublication (p : Publication) (text : String := "") (proved : List String := [])
    (consumers : List Consumer := []) : Module :=
  { space := p.space, statementsName := p.dataName, statements := p.data, stated := p.stated
    proof := p.proof (text ++ "\n" ++ String.join (consumers.map (·.text))), proved := proved ++ consumers.map (·.name)
    textLine := p.textLine, textLines := (text.splitOn "\n").length
    consumers, refusals := p.refusals, issued := some (p.challenge, p.published)
    support := [(p.viewsName, p.views), (p.feesName, p.fees)] }

/-- The challenge of a pair, as `lake comparator` takes one: a module that imports the module
of the statements and states each published theorem over its proposition, and each consumer
as the check wrote its statement, with no proof. It is the trusted side with the statements;
the proof module is the solution. A consumer is stated in the name space and under the names
that the proof module opens, so that its statement is read as it is there. -/
def Module.challenge (m : Module) : String :=
  if let some (challenge, _) := m.issued then
    if m.consumers.isEmpty then challenge else
      -- the issuer's imports with the consumers', the issuer's line, then the consumers' statements
      let (imports, line) := (challenge.splitOn "\n").partition (·.startsWith "import ")
      let more := (statementOpenImports ++ m.consumers.flatMap (·.imports)).eraseDups.map (s!"import {·}")
      "\n".intercalate ((imports ++ more).eraseDups ++ line) ++
        s!"\nopen Zkc.Core\nnamespace {m.space}\n" ++ statementOpens ++
        String.join (m.consumers.map (·.stated)) ++ s!"end {m.space}\n"
  else
  let scope := if m.consumers.isEmpty then [] else statementOpenImports
  s!"import {m.statementsName}\n" ++
    String.join ((scope ++ m.consumers.flatMap (·.imports)).eraseDups.map (s!"import {·}\n")) ++
    String.join (m.published.map fun (theorem_, proposition) =>
      s!"theorem {theorem_} : {proposition} := by sorry\n") ++
    (if m.consumers.isEmpty then "" else
      s!"\nopen Zkc.Core\nnamespace {m.space}\n" ++ statementOpens ++ String.join (m.consumers.map (·.stated)) ++
        s!"end {m.space}\n")

/-- The theorems of a pair that the judgment is of: the published ones and the consumers,
under their full names (a name is its components, as in `publicationPairs`). -/
def Module.judged (m : Module) : List Lean.Name :=
  if let some (_, names) := m.issued then names ++ m.consumers.map fun c => .str m.space.toName c.name else
  m.published.map (·.1) ++ m.consumers.map fun c => .str m.space.toName c.name

/-- Requests for the axioms of the theorems of the proof module, by their full names: what a
control appends to the proof module, to read from Lean's reports which theorems are left
unproved. -/
def Module.requests (m : Module) : String :=
  String.join (m.proved.map fun theorem_ => s!"#print axioms {m.space}.{theorem_}\n")


open ZkcFormalTests in
/-- The project of a check, in its work folder. -/
def projectOf (work : System.FilePath) : System.FilePath := work / "project"

/-- The label of the judgment of the proof modules that a check accepts. -/
def acceptedLabel : String := "Accepted"

/-- The pairs that a folder holds for one judgment, as they were noted: for each, its challenge,
its proof module and the theorems that it is judged by. -/
def accepted (folder : System.FilePath) : IO (List (Lean.Name × Lean.Name) × List Lean.Name) := do
  let registry := folder / "accepted.txt"
  unless ← registry.pathExists do return ([], [])
  let mut pairs := []
  let mut theorems := []
  for line in (← IO.FS.readFile registry).splitOn "\n" do
    match line.splitOn "\t" with
    | [challenge, solution, published] =>
      unless pairs.contains (challenge.toName, solution.toName) do
        pairs := pairs ++ [(challenge.toName, solution.toName)]
        theorems := theorems ++ ((published.splitOn " ").filter (· != "")).map String.toName
    | _ => pure ()
  return (pairs, theorems)

/-- The check's project settled: the judgment of the pairs that the check noted is expected of
it first, and then it is built. -/
def settle (work : System.FilePath) : IO Unit := do
  let project := projectOf work
  unless ← SubjectProject.isSettled project do
    let (pairs, theorems) ← accepted project
    unless pairs.isEmpty do
      SubjectProject.expect project acceptedLabel pairs theorems allowed
  SubjectProject.settle project

/-- What Lean said of a module of a check, and whether it built the module: read when it is
asked. -/
abbrev Pending := IO (Bool × String)

/-- What a pending result gives. -/
def finishLean (pending : Pending) : IO (Bool × String) := pending

/-- Lean's result on a module of the check's project. -/
def leanOn (work : System.FilePath) (module : Lean.Name) : Pending := do
  settle work
  SubjectProject.result (projectOf work) module

/-- A module of one source, added to the check's project under the name `name`. With
`text := false` the module holds no text of an author and imports no module that does: it is
built with the statements, before any text is read, so that what Lean says of it is what is
so. -/
def startLakeLean (work : System.FilePath) (name source : String) (text := true) : IO Pending := do
  discard <| SubjectProject.add (projectOf work) name.toName source (if text then .module else .statements)
  return leanOn work name.toName

/-- Compare the named values in the issued statements with the frontend run on the original
source and selectors. The same values must be the fields of the package used for admission. -/
def startSourceComparison (work : System.FilePath) (name : String) (module : Module)
    (source : String) (goals : List String) : IO Pending := do
  let observation ← IO.ofExcept (WrittenSource.consumer source goals)
  startLakeLean work name
    (s!"import {module.statementsName}\nimport Zkc.Tests.Frontend.PrintedPackageSupport\n" ++
      "import ZkcFormalTests.WrittenBinding\n\n" ++
      s!"namespace {module.space}\n" ++
      "example : subjectPackage.stored = stored := rfl\n" ++
      "example : subjectPackage.association = association := rfl\n" ++
      "example : subjectPackage.installed = installed := rfl\n" ++
      s!"#eval Zkc.Tests.Frontend.PrintedPackageSupport.expectGoalClaims {literal source} " ++
      s!"{reprStr goals} ⟨[], [], [], [], []⟩ stored association\n" ++ observation ++ s!"end {module.space}\n")
    (text := false)

/-- `expectUnprovedIn`, of a module that the check added. -/
def expectUnproved (title name : String) (theorems : List String) (pending : Pending)
    (expected : List String) : IO Unit := do
  let (ok, output) ← pending
  expectUnprovedIn title name theorems ok output expected

/-- `expectPlacesIn`, of a module that the check added. -/
def expectPlaces (title : String) (pending : Pending) (places : List String) : IO Unit := do
  expectPlacesIn title (← pending).2 places

/-- A module of statements in the check's project. -/
structure Stated where
  /-- The name space of its theorems, and their names. -/
  space : String
  theorems : List String
  /-- Its module. -/
  module : Lean.Name
  /-- Lean's result on it. -/
  lean : Pending

/-- The module of the statements of `module`, added. Two pairs with the same statements share
the module; two different modules of statements cannot have one name. -/
def addStated (work : System.FilePath) (module : Module) : IO Stated := do
  let project := projectOf work
  let file := project / SubjectProject.fileOf module.statementsName
  if ← file.pathExists then
    unless (← IO.FS.readFile file) == module.statements do
      throw (IO.userError (s!"two modules of statements are named {module.statementsName}: a module " ++
        "whose statements are not its subject's names its own (`Subject.module`, `statements`)"))
  else
    discard <| SubjectProject.add project module.statementsName module.statements .statements
  return { space := module.space, theorems := module.stated, module := module.statementsName,
           lean := leanOn work module.statementsName }

/-- The statements are accepted: Lean ends without an error, and each theorem of the module
rests on the allowed axioms at most. The module holds no text and is built before any text is
read, so what Lean reports of it is what is so; and the judgment takes the statements as given,
so this is where they are checked. -/
def Stated.accepted (stated : Stated) (name : String) : IO Unit := do
  let (ok, output) ← stated.lean
  try acceptedOutput stated.space ok output stated.theorems allowed
  catch refusal => throw (IO.userError s!"{name}, the module of the statements: {refusal}")

/-- Lean's output on a proof module with the positions inside the author's text given by the
lines of the text: `text:<line>:<column>`. A position before or after the text keeps the line
of the module. -/
def atText (source : System.FilePath) (module : Module) (output : String) : String :=
  let mark := s!"{source}:"
  match output.splitOn mark with
  | [] => output
  | first :: rest =>
    first ++ String.join (rest.map fun piece =>
      let digits := piece.toList.takeWhile Char.isDigit
      let line := (String.ofList digits).toNat!
      if !digits.isEmpty && module.textLine ≤ line && line < module.textLine + module.textLines then
        s!"text:{line + 1 - module.textLine}" ++ String.ofList (piece.toList.drop digits.length)
      else mark ++ piece)

/-- The modules that a proof module imports beside its statements, added to a project. A name
holds one text in a project. -/
def addSupport (project : System.FilePath) (module : Module) : IO Unit := do
  for (name, text) in module.support do
    let file := project / SubjectProject.fileOf name
    if ← file.pathExists then
      unless (← IO.FS.readFile file) == text do
        throw (IO.userError s!"two modules of a project are named {name} and are not the same")
    else discard <| SubjectProject.add project name text .statements

/-- A proof module of `module`, added under the name `name`: Lean's result on it, with the
positions of the text. `text` is the proof module as it is built (a control appends its
requests for axioms). -/
def addProof (work : System.FilePath) (name : String) (module : Module)
    (text : String := module.proof) : IO Pending := do
  addSupport (projectOf work) module
  let file ← SubjectProject.add (projectOf work) name.toName text
  return do
    let (ok, output) ← leanOn work name.toName
    return (ok, atText file module output)

/-- The challenge of a proof module named `name`, added: `<name>.Challenge`. -/
def addChallenge (work : System.FilePath) (name : String) (module : Module) : IO Lean.Name := do
  let challenge : Lean.Name := .str name.toName "Challenge"
  discard <| SubjectProject.add (projectOf work) challenge module.challenge .challenge
  return challenge

/-- A proof module that the check accepts, noted for the judgment with its challenge: in the
check's project, or, with `ZKC_SUBJECTS` naming a folder, in that folder, for the recipe's one
judgment of all its checks. -/
def noteAccepted (work : System.FilePath) (name : String) (module : Module) : IO Unit := do
  if module.judged.isEmpty then
    throw (IO.userError s!"{name}: the module names no published theorem to judge")
  let challenge : Lean.Name := .str name.toName "Challenge"
  let line := s!"{challenge}\t{name}\t{" ".intercalate (module.judged.map toString)}\n"
  let note (folder : System.FilePath) : IO Unit := do
    let handle ← IO.FS.Handle.mk (folder / "accepted.txt") .append
    handle.putStr line
  match ← IO.getEnv "ZKC_SUBJECTS" with
  | none =>
    discard <| addChallenge work name module
    note (projectOf work)
  | some shared =>
    let shared : System.FilePath := shared
    for (module, text, kind) in [(module.statementsName, module.statements, SubjectProject.Kind.statements),
        (challenge, module.challenge, .challenge), (name.toName, module.proof, .module)] ++
        module.support.map (fun (support, text) => (support, text, .statements)) do
      let file := shared / SubjectProject.fileOf module
      if ← file.pathExists then
        unless (← IO.FS.readFile file) == text do
          throw (IO.userError s!"two checks of the recipe have a module {module} that is not the same")
      else discard <| SubjectProject.add shared module text kind
    note shared

/-- The judgment of the proof modules that the check accepts, all in one run of
`lake comparator`. Under a recipe that judges for its checks (`ZKC_SUBJECTS`) the check does
not judge. -/
def judged (work : System.FilePath) : IO (SubjectProject.Verdict × String) := do
  if (← IO.getEnv "ZKC_SUBJECTS").isSome then
    return (.accepted, "the pairs are judged by the recipe")
  settle work
  SubjectProject.judge (projectOf work) acceptedLabel

/-- What Lean and the judgment gave on a proof module: Lean's result on it, and, where Lean
accepted it and it was judged alone, the verdict and what the comparator printed. -/
structure Outside where
  lean : Bool × String
  verified : Option (SubjectProject.Verdict × String) := none

/-- A proof module with its statements, added to be judged alone: Lean on both, and then, where
Lean accepts them, `lake comparator` on this one pair. For a control that the judgment must
refuse; a module that a check accepts is judged with the others (`startModule`). -/
def readOutside (work : System.FilePath) (name : String) (module : Module) : IO (IO Outside) := do
  let stated ← addStated work module
  let proved ← addProof work name module
  let challenge ← addChallenge work name module
  let label := s!"{name}Alone"
  SubjectProject.expect (projectOf work) label [(challenge, name.toName)] module.judged allowed
  return do
    let statements ← stated.lean
    unless statements.1 do
      throw (IO.userError s!"{name}: Lean refused the module of the statements\n{statements.2}")
    let lean ← proved
    unless lean.1 do return { lean }
    return { lean, verified := some (← SubjectProject.judge (projectOf work) label) }

/-- Lean accepts a proof module with nothing left to `sorry`. -/
def acceptedByLean (name : String) (lean : Bool × String) : IO Unit :=
  acceptedOutput name lean.1 lean.2 []

/-- The judgment of the check's accepted modules accepts them. What the comparator says of a
refusal is given whole. -/
def acceptedByJudgment (work : System.FilePath) (name : String) : IO Unit := do
  match ← judged work with
  | (.accepted, _) => pure ()
  | (.refused, said) =>
    throw (IO.userError s!"{name}: Lean accepted the module, and the judgment refuses the check's modules\n{said}")
  | (.failed, said) =>
    throw (IO.userError s!"{name}: the check's modules were not judged\n{said}")

/-- The two modules of `module`, added to be accepted: the statements by Lean, with their
theorems on the allowed axioms, and the proof module by Lean and by the judgment. The result is
Lean's output on the proof module. -/
def startModule (work : System.FilePath) (name : String) (module : Module) : IO Pending := do
  unless module.refusals.isEmpty do
    throw (IO.userError s!"{name}: the publication left goals out: {module.refusals}")
  let stated ← addStated work module
  let proved ← addProof work name module
  noteAccepted work name module
  return do
    stated.accepted name
    let lean ← proved
    acceptedByLean name lean
    acceptedByJudgment work name
    return lean

/-- The two modules of a module that Lean must refuse in its proof module, added: the
statements, which are accepted, and the proof module with the requests for the axioms of its
theorems. The result is Lean's on the proof module. For a control that is not of a subject
(`Control` is). -/
def startRefused (work : System.FilePath) (name : String) (module : Module) : IO Pending := do
  let stated ← addStated work module
  let proved ← addProof work name module (module.proof ++ module.requests)
  return do
    stated.accepted name
    proved

/-- What the judgment said of a module that Lean accepts and that it must refuse: each of
`places`, of which there is one at least, since the comparator ends in the same way on a pair
that it refuses and on an export that it cannot read. -/
def Outside.refused (outside : Outside) (title name : String) (places : List String) : IO Unit := do
  acceptedByLean name outside.lean
  if places.isEmpty then
    throw (IO.userError s!"{title}: a control of the judgment names what the comparator says of it")
  match outside.verified with
  | some (.refused, said) =>
    unless places.all (fun place => said.contains place) do
      throw (IO.userError s!"{title}: refused by the judgment for another reason\n{said}")
  | some (.failed, said) => throw (IO.userError s!"{title}: the module was not judged\n{said}")
  | _ => throw (IO.userError s!"{title}: the module was accepted by the judgment")

/-- A control of the judgment, added: Lean accepts the two modules, and `lake comparator`
refuses the proof module, saying each of `places`. The result judges it when asked. -/
def refusedOutside (work : System.FilePath) (title name : String) (module : Module)
    (places : List String) : IO (IO Unit) := do
  let outside ← readOutside work name module
  return do (← outside).refused title name places

end ZkcFormalTests.WrittenSubject
