import Lean.Data.Json
import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport
import ZkcFormalTests.SubjectProject

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
  let statements : Statements := ⟨claims, claims.functionsBeforeRoot⟩
  return ⟨text, statements⟩

/-- The text of a subject's proofs: the text, the theorems that it proves, what it imports
beside what every module of statements imports, and what the check writes after the closing
theorems (a consumer of the published theorems). -/
structure Proof where
  text : String
  theorems : List String
  imports : List String := []
  after : List Consumer := []

/-- The two modules of a subject, as the generator assembles them: the module of the statements
and the proof module, in the name space `name`. A goal of the subject that the generator
refuses fails the assembly. A control gives the text that it altered, and
`statements` names the module
of the statements where it is not `<name>.Stated`. -/
def Subject.module (s : Subject) (name : String) (proof : Proof) (text : String := proof.text)
    (statements : Option Lean.Name := none) : IO Module := do
  let written : ProofText := { text, theorems := proof.theorems, imports := proof.imports }
  let issued ← IO.ofExcept (s.statements.module name written (after := proof.after)
    (statements := statements))
  -- a subject asks for each of its goals: one that is not issued fails the subject
  unless issued.refusals.isEmpty do
    throw (IO.userError s!"{name}: not every goal is issued: {"; ".intercalate issued.refusals}")
  return issued

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

/-- A proof module of `module`, added under the name `name`: Lean's result on it, with the
positions of the text. `text` is the proof module as it is built (a control appends its
requests for axioms). -/
def addProof (work : System.FilePath) (name : String) (module : Module)
    (text : String := module.proof) : IO Pending := do
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
  if module.published.isEmpty then
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
        (challenge, module.challenge, .challenge), (name.toName, module.proof, .module)] do
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

/-- Several pairs as one source: the imports of all of them, and then for each pair its
statements, its proof module and the requests for the axioms of the proof module's theorems.
For a module of a check that must hold two programs at once, so that what is generated for both
is in scope together. Such a module is judged by what Lean says of it. -/
def asOne (modules : List Module) : String :=
  let imports := (modules.flatMap fun m => m.statedImports ++ m.proofImports).eraseDups
  let body (source : String) : String :=
    "\n".intercalate ((source.splitOn "\n").filter fun line => !line.startsWith "import ")
  String.join (imports.map (s!"import {·}\n")) ++
    String.join (modules.map fun m => body m.statements ++ body m.proof ++ m.requests)

/-- Where a control is refused. -/
inductive Refusal where
  /-- By Lean, in the proof module: the statements are accepted. -/
  | text
  /-- By Lean, in the module of the statements: what is generated before the text does not
  hold of the altered source, and the proof module is not read. -/
  | generated
  /-- By the judgment: Lean accepts both modules. -/
  | outside
  deriving DecidableEq, Repr

/-- A control: the subject altered, in a module that must be refused. -/
structure Control where
  /-- What the control changes, for a message. -/
  title : String
  /-- The name of its module. The name space of its declarations is the subject's. -/
  name : String
  /-- The subject, with its source altered where the control alters the source. -/
  subject : Subject
  /-- The text of the proofs, altered where the control alters the text. -/
  text : String

  /-- Where it is refused. -/
  refusal : Refusal := .text
  /-- The theorems that are left unproved, themselves or by what they use, and no other: of the
  theorems of the module that Lean refuses (the proof module, or the module of the statements
  of a control that is refused there). Nothing is unproved in a control that the judgment
  refuses. -/
  unproved : List String := []
  /-- The texts of the places at which the module is refused: each occurs in Lean's output, or
  in what the comparator says. -/
  places : List String := []
  /-- The module is refused at those places and at no other: its errors are as many. -/
  only : Bool := false
  /-- Texts with the number of times that each occurs in Lean's output: a refusal that two
  proofs of one module both meet is counted, since one text twice among the places says only
  that it occurs. -/
  occurrences : List (String × Nat) := []

/-- What the run of a control gave: which module was refused or accepted, with its theorems,
and what was said of it. -/
structure Ran where
  refusal : Refusal
  theorems : List String
  outside : Outside

/-- A control whose modules the check added. -/
structure Running where
  control : Control
  space : String
  ran : IO Ran

/-- The modules of a control, added. The name space is the subject's (`space`). A control
whose statements are those of the subject, character for character (it alters only the text),
imports the subject's module of statements; another has a module of statements of its own,
`<control>.Stated`. A control that Lean must refuse has the requests for the axioms of its
theorems appended, from which the unproved ones are read. -/
def Control.start (work : System.FilePath) (space : String) (proof : Proof) (honest : Module)
    (honestStated : Stated) (control : Control) : IO Running := do
  let plain ← control.subject.module space proof control.text
  let own := plain.statements != honest.statements
  let module ← if own then
      control.subject.module space proof control.text
        (statements := some (.str control.name.toName "Stated"))
    else pure plain
  let stated ← if own then addStated work module else pure honestStated
  if control.refusal == .outside then
    let outside ← readOutside work control.name module
    return ⟨control, space, do
      let statements ← stated.lean
      unless statements.1 do
        return { refusal := .generated, theorems := module.stated, outside := { lean := statements } }
      return { refusal := .outside, theorems := [], outside := ← outside }⟩
  let proved ← addProof work control.name module (module.proof ++ module.requests)
  return ⟨control, space, do
    let statements ← stated.lean
    unless statements.1 do
      return { refusal := .generated, theorems := module.stated, outside := { lean := statements } }
    return { refusal := .text, theorems := module.proved, outside := { lean := ← proved } }⟩

/-- A control judged: it was refused where it says, the theorems left unproved are those that
it names, and it was refused at the places that it names. -/
def Running.finish (running : Running) : IO Unit := do
  let control := running.control
  let ran ← running.ran
  let (ok, output) := ran.outside.lean
  unless ran.refusal == control.refusal do
    throw (IO.userError s!"{control.title}: the control is one refused in `{repr control.refusal}`, and was read as `{repr ran.refusal}`\n{output}")
  if control.refusal == .outside then
    return ← ran.outside.refused control.title running.space control.places
  expectUnprovedIn control.title running.space ran.theorems ok output control.unproved
  if control.only then expectPlacesIn control.title output control.places
  for place in control.places do
    unless output.contains place do
      throw (IO.userError s!"{control.title}: not refused at `{place}`\n{output}")
  for (place, times) in control.occurrences do
    unless (output.splitOn place).length == times + 1 do
      throw (IO.userError s!"{control.title}: `{place}` does not occur {times} times\n{output}")

/-- A subject whose modules the check added: its two modules, the module in which Lean reads
the source again, and its controls. -/
structure Checking where
  name : String
  work : System.FilePath
  /-- Lean on the two modules of the subject: the statements accepted, and the proof module. -/
  honest : Pending
  comparison : Pending
  controls : List Running

/-- The modules of a subject, added: the module of the statements, the proof module, which is
judged, each control, and the comparison of the package with the frontend. -/
def start (work : System.FilePath) (name : String) (subject : Subject) (proof : Proof)
    (controls : List Control := []) : IO Checking := do
  let module ← subject.module name proof
  let stated ← addStated work module
  let proved ← addProof work name module
  noteAccepted work name module
  let honest : Pending := do
    stated.accepted name
    let lean ← proved
    acceptedByLean name lean
    return lean
  let comparison ← startLakeLean work s!"{name}Source"
    (comparisonModule s!"{name}Source" subject.text (subject.goals.map (·.goal)) subject.package)
    (text := false)
  return ⟨name, work, honest, comparison, ← controls.mapM (·.start work name proof module stated)⟩

/-- A subject judged: Lean accepts the module of its statements, with every theorem on the
allowed axioms; Lean accepts its proof module, and the judgment accepts it; Lean accepts the
module in which it reads the source again; each control is refused as it says. What Lean said is
read first, of every module, and the judgments after it, since a judgment costs the more. The
result is Lean's output on the proof module. -/
def Checking.finish (checking : Checking) : IO (Bool × String) := do
  let (ok, output) ← checking.honest
  let (sourceOk, sourceOutput) ← checking.comparison
  acceptedOutput s!"{checking.name}Source" sourceOk sourceOutput []
  let (outside, inside) := checking.controls.partition (·.control.refusal == .outside)
  for control in inside do
    control.finish
  acceptedByJudgment checking.work checking.name
  for control in outside do
    control.finish
  return (ok, output)

/-- A subject checked: `start`, then `finish`. -/
def check (work : System.FilePath) (name : String) (subject : Subject) (proof : Proof)
    (controls : List Control := []) : IO (Bool × String) := do
  (← start work name subject proof controls).finish

end ZkcFormalTests.WrittenSubject
