import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport

/-!
A subject of a written soundness goal, as a check states it.

A subject is a source, the text of its proofs, what the check asserts of what the frontend
read of the source, and its controls. The checks of the subjects (`lean/formal/checks/*Charge.lean`)
give these as data and share what is here: how a source is read and what is asserted of the
reading (`Reading`, `read`), how the proof module is assembled (`Subject.module`), and how a
control is stated and judged (`Control`).

A control is a module that Lean must refuse: the subject with its source or its text altered,
or under a description of the model that the control gives. It names the theorems that are
then left unproved, and the texts of the places at which Lean refuses the module; with `only`
the module is refused at those places and at no other. A text is altered with `replaceOnce`
(`PrintedPackageSupport`), which fails when the place that it alters is gone.
-/

namespace Zkc.Tests.Frontend.WrittenSubject
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
scheme, and the class of models that the generator chose for the statements. A relation with
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
  /-- The class of models that the generator chooses for the statements. -/
  model : ModelText := standardModelText

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
  let chosen := statements.chosenModel
  unless chosen.model == reading.model.model && chosen.hypotheses == reading.model.hypotheses do
    throw (IO.userError s!"the statements are about another class of models: {chosen.model}")
  return ⟨text, statements⟩

/-- The text of a subject's proofs: the text, the theorems that it proves, what it imports
beside what every module of statements imports, and what the check writes after the closing
theorems (a consumer of the published theorems). -/
structure Proof where
  text : String
  theorems : List String
  imports : List String := []
  after : ProofText := {}

/-- The proof module of a subject, as the generator assembles it: the package of the claims
and what is generated around a text. A control gives the text that it altered, and a
description of the model where its claim is about another class. -/
def Subject.module (s : Subject) (name : String) (proof : Proof) (text : String := proof.text)
    (model : Option ModelText := none) : IO Module :=
  let written : ProofText := { text, theorems := proof.theorems, imports := proof.imports }
  IO.ofExcept (match model with
    | some model => s.statements.module name written (after := proof.after) (model := model)
    | none => s.statements.module name written (after := proof.after))

/-- The axioms beyond which no theorem of a subject may rest. -/
def allowed : List String := ["propext", "Classical.choice", "Quot.sound"]

/-! ## A module read outside the file

Lean's acceptance of a proof module is not what a check rests on: a text can turn off the
kernel's check of its declarations (`Statements.module` says how). A module that publishes
theorems is therefore compiled to an object, with the module that the generator writes without
the text (its reference), and both are read by a program outside the file
(`lean/formal/Zkc/Tools/Formal/VerifyPublication.lean`): the kernel replays the proof module's
declarations, the published theorems are of the reference's propositions, and their axioms are
read from the replayed proofs. -/

/-- What Lean and the program outside the file gave on a module: Lean's result on the proof
module, and, where Lean accepted it, whether the program outside accepted it and what it
printed. -/
structure Outside where
  lean : Bool × String
  verified : Option (Bool × String) := none

/-- Lean on a module and on its reference, each compiled to an object, and then the program
outside the file on the two objects. The two sources have one module name and stand in two
directories, each its own folder: a module is elaborated in a sandbox in which it can write
only there (`runLakeLean`), since a text is code that runs while Lean elaborates it. A reference
that Lean refuses is an error of the generator. The object of the proof module is what that run
left in the module's folder; the program reads it in the same sandbox, in a folder of its
own. -/
def readOutside (work : System.FilePath) (name : String) (module : Module)
    (axioms : List String := allowed) : IO Outside := do
  let place (part source : String) : IO (System.FilePath × System.FilePath × System.FilePath) := do
    let root ← IO.FS.realPath (← do IO.FS.createDirAll (work / s!"{name}.{part}"); pure (work / s!"{name}.{part}"))
    let path := root / s!"{name}.lean"
    IO.FS.writeFile path source
    return (root, path, path.withExtension "olean")
  let (candidateRoot, candidateSource, candidate) ← place "candidate" module.text
  let (referenceRoot, referenceSource, reference) ← place "reference" module.reference
  -- where Lake has the imports of the proof module's header, which the generator wrote: asked
  -- before the text runs, and kept outside the folder that the text can write
  let setup ← IO.Process.output {
    cmd := "lake"
    args := #["-q", "setup-file", candidateSource.toString]
    env := #[("TMPDIR", some referenceRoot.toString)] }
  unless setup.exitCode == 0 do
    throw (IO.userError s!"{name}: no setup for the imports of the proof module\n{setup.stderr}")
  let setupPath := referenceRoot / "setup.json"
  IO.FS.writeFile setupPath setup.stdout
  -- the proof module, with the author's text, is compiled as every module of a check is: in
  -- a sandbox in which only its own folder can be written (`runLakeLean`). A text can then
  -- not change the program that reads its object, the reference, the setup or the imports.
  let lean ← runLakeLean candidateSource #["-R", candidateRoot.toString, "-o", candidate.toString]
  unless lean.1 do return { lean }
  let referenceLean ← runLakeLean referenceSource #["-R", referenceRoot.toString, "-o", reference.toString]
  unless referenceLean.1 do
    throw (IO.userError s!"{name}: Lean refused the module without the text\n{referenceLean.2}")
  -- the object of the proof module is whatever the run of Lean on the text left in its folder,
  -- and the program maps it into memory as an object without checking its format: it reads the
  -- object in the sandbox too, in a folder of its own, so that a malformed object can change
  -- no file. The verdict is still the program's.
  let readingRoot ← IO.FS.realPath (← do
    IO.FS.createDirAll (work / s!"{name}.reading"); pure (work / s!"{name}.reading"))
  let out ← confined readingRoot
    (#["lake", "env", "lean", "--run", "Zkc/Tools/Formal/VerifyPublication.lean",
      setupPath.toString, reference.toString, candidate.toString, ",".intercalate axioms] ++
      (module.published.map fun (theorem_, proposition) => s!"{theorem_}={proposition}").toArray)
  return { lean, verified := some (out.exitCode == 0, out.stdout ++ out.stderr) }

/-- Lean on a proof module, as a task, with the module read outside the file: a module that
Lean accepts and the program outside refuses is an error here, with what that program said. The
result is Lean's on the module. The module has to publish theorems: one that publishes nothing
is an error, so that a module whose list was lost is not accepted unread. A module that is
meant to publish nothing (a control, the module of a ceiling) is started with
`startLakeLean`. -/
def startModule (work : System.FilePath) (name : String) (module : Module)
    (axioms : List String := allowed) : IO (Task (Except IO.Error (Bool × String))) := do
  if module.published.isEmpty || module.reference.isEmpty then
    throw (IO.userError s!"{name}: the module names no published theorem to read outside the file")
  IO.asTask do
    let outside ← readOutside work name module axioms
    if let some (false, said) := outside.verified then
      throw (IO.userError s!"{name}: Lean accepted the module, and outside the file it is refused\n{said}")
    return outside.lean

/-- A control of the reading outside the file: Lean accepts the module, with every theorem on
the allowed axioms as its output has them, and the program outside the file refuses it, saying
each of `places`. -/
def refusedOutside (work : System.FilePath) (title name : String) (module : Module)
    (places : List String) : IO Unit := do
  let outside ← readOutside work name module
  acceptedOutput name outside.lean.1 outside.lean.2 module.theorems allowed
  match outside.verified with
  | some (false, said) =>
    unless places.all (fun place => said.contains place) do
      throw (IO.userError s!"{title}: refused outside the file for another reason\n{said}")
  | _ => throw (IO.userError s!"{title}: the module was accepted outside the file")

/-- A control: a module that Lean must refuse. -/
structure Control where
  /-- What the control changes, for a message. -/
  title : String
  /-- The name of its module. -/
  name : String
  /-- The subject, with its source altered where the control alters the source. -/
  subject : Subject
  /-- The text of the proofs, altered where the control alters the text. -/
  text : String
  /-- The description of the model, where the control states a claim about another class. -/
  model : Option ModelText := none
  /-- The theorems that are left unproved, themselves or by what they use, and no other: of the
  theorems of the control's own module. A theorem that the control's module does not state (a
  cap of a draw that its source does not charge) is not among them. -/
  unproved : List String
  /-- The texts of the places at which Lean refuses the module: each occurs in its output. -/
  places : List String := []
  /-- The module is refused at those places and at no other: its errors are as many. -/
  only : Bool := false
  /-- Texts with the number of times that each occurs in Lean's output: a refusal that two
  proofs of one module both meet is counted, since one text twice among the places says only
  that it occurs. -/
  occurrences : List (String × Nat) := []

/-- A control whose module Lean is reading. -/
structure Running where
  control : Control
  theorems : List String
  task : Task (Except IO.Error (Bool × String))

/-- Lean on the module of a control, as a task. -/
def Control.start (work : System.FilePath) (proof : Proof) (control : Control) : IO Running := do
  let module ← control.subject.module control.name proof control.text control.model
  return ⟨control, module.theorems, ← startLakeLean work control.name module.text⟩

/-- A control judged: Lean refused the module, the theorems left unproved are those that the
control names, and it was refused at the places that the control names. -/
def Running.finish (running : Running) : IO Unit := do
  let control := running.control
  expectUnproved control.title control.name running.theorems running.task control.unproved
  let (_, output) ← finishLean running.task
  if control.only then expectPlaces control.title running.task control.places
  for place in control.places do
    unless output.contains place do
      throw (IO.userError s!"{control.title}: not refused at `{place}`\n{output}")
  for (place, times) in control.occurrences do
    unless (output.splitOn place).length == times + 1 do
      throw (IO.userError s!"{control.title}: `{place}` does not occur {times} times\n{output}")

/-- A subject whose modules Lean is reading: its proof module, the module in which Lean reads
the source again, and its controls. -/
structure Checking where
  name : String
  module : Module
  honest : Task (Except IO.Error (Bool × String))
  comparison : Task (Except IO.Error (Bool × String))
  controls : List Running

/-- Lean on the modules of a subject, at once: the proof module, the comparison of the package
with the frontend, and each control. -/
def start (work : System.FilePath) (name : String) (subject : Subject) (proof : Proof)
    (controls : List Control := []) : IO Checking := do
  let module ← subject.module name proof
  let honest ← startModule work name module
  let comparison ← startLakeLean work s!"{name}Source"
    (comparisonModule s!"{name}Source" subject.text (subject.goals.map (·.goal)) subject.package)
  return ⟨name, module, honest, comparison, ← controls.mapM (·.start work proof)⟩

/-- A subject judged: Lean accepts its proof module, with every theorem on the allowed axioms,
the module is accepted outside the file (`startModule`), and Lean accepts the module in which
it reads the source again; each control is refused as it says. The
result is Lean's output on the proof module. -/
def Checking.finish (checking : Checking) : IO (Bool × String) := do
  let (ok, output) ← finishLean checking.honest
  acceptedOutput checking.name ok output checking.module.theorems allowed
  let (sourceOk, sourceOutput) ← finishLean checking.comparison
  acceptedOutput s!"{checking.name}Source" sourceOk sourceOutput []
  for control in checking.controls do
    control.finish
  return (ok, output)

/-- A subject checked: `start`, then `finish`. -/
def check (work : System.FilePath) (name : String) (subject : Subject) (proof : Proof)
    (controls : List Control := []) : IO (Bool × String) := do
  (← start work name subject proof controls).finish

end Zkc.Tests.Frontend.WrittenSubject
