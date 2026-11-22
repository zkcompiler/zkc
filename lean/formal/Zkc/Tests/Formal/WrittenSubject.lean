import Lean.Data.Json
import Zkc.Frontend.Written.Statement
import Zkc.Tests.Frontend.SourceClause
import Zkc.Tests.Frontend.PrintedPackageSupport

/-!
A subject of a written soundness goal, as a check states it.

A subject is a source, the text of its proofs, what the check asserts of what the frontend
read of the source, and its controls. The checks of the subjects (`lean/formal/checks/*Charge.lean`)
give these as data and share what is here: how a source is read and what is asserted of the
reading (`Reading`, `read`), how the two modules of a subject are assembled (`Subject.module`),
how they are compiled and the proof module read outside the file (`compileStated`,
`proveOutside`), and how a control is stated and judged (`Control`).

A control is the subject with its source or its text altered, or under a description of the
model that the control gives, in a module that must be refused: by Lean in the text, by Lean in
what is generated before the text, or outside the file where Lean accepts it. It names the
theorems that are then left unproved and the texts of the places at which it is refused; with
`only` the module is refused at those places and at no other. A text is altered with
`replaceOnce` (`PrintedPackageSupport`), which fails when the place that it alters is gone.
-/

namespace Zkc.Tests.Formal.WrittenSubject
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

/-- The two modules of a subject, as the generator assembles them: the module of the statements
and the proof module, in the name space `name`. A control gives the text that it altered, and a
description of the model where its claim is about another class. -/
def Subject.module (s : Subject) (name : String) (proof : Proof) (text : String := proof.text)
    (model : Option ModelText := none) : IO Module :=
  let written : ProofText := { text, theorems := proof.theorems, imports := proof.imports }
  IO.ofExcept (match model with
    | some model => s.statements.module name written (after := proof.after) (model := model)
    | none => s.statements.module name written (after := proof.after))

/-- The axioms beyond which no theorem of a subject may rest. -/
def allowed : List String := ["propext", "Classical.choice", "Quot.sound"]

/-! ## The two modules compiled, and the proof module read outside the file

Lean's acceptance of a proof module is not what a check rests on: a text can turn off the
kernel's check of its declarations (`Statements.module` says how). The module of the statements
is compiled first, where no text is. The proof module is compiled against that object, and its
own object is read by a program outside the file
(`lean/formal/Zkc/Tools/Formal/VerifyPublication.lean`): the kernel replays the proof module's
declarations on its imports, the published theorems are of propositions that the module of the
statements declares, and the axioms are read from the replayed proofs.

Where what is written: the statements in a folder of their own (`<name>.stated`); what the
check gives to the compilation and to the reading of a proof module, its setup and the manifest
of what it publishes, in another (`<name>.given`); the proof module with its object in a third
(`<name>`), which is all that the run of Lean on the text can write; and the program reads in a
fourth (`<name>.reading`). -/

/-- A folder of a check, made, by its real path. -/
def folderAt (path : System.FilePath) : IO System.FilePath := do
  IO.FS.createDirAll path
  IO.FS.realPath path

/-- What Lake names for the imports `modules`: the setup of a module with that header, as Lake
prints it, asked before any text runs. -/
def lakeSetup (folder : System.FilePath) (modules : List String) : IO Lean.Json := do
  let header := folder / "Header.lean"
  IO.FS.writeFile header (String.join (modules.map (s!"import {·}\n")))
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["-q", "setup-file", header.toString]
    env := #[("TMPDIR", some folder.toString)] }
  unless out.exitCode == 0 do
    throw (IO.userError s!"no setup for the imports {modules}\n{out.stderr}")
  IO.ofExcept (Lean.Json.parse out.stdout)

/-- A module of statements, compiled. -/
structure Stated where
  /-- The name space of its theorems, and their names. -/
  space : String
  theorems : List String
  /-- What Lake names for its imports. -/
  setup : Lean.Json
  /-- Its object, in a folder that no run of Lean on a text can write. -/
  object : System.FilePath
  /-- Lean's result on it. -/
  lean : Bool × String

/-- Lean on the module of the statements of `module`, compiled to an object in the folder
`<name>.stated`. -/
def compileStated (work : System.FilePath) (name : String) (module : Module) : IO Stated := do
  let folder ← folderAt (work / s!"{name}.stated")
  let setup ← lakeSetup folder module.statedImports
  let setupPath := folder / "setup.json"
  IO.FS.writeFile setupPath (setup.setObjVal! "name" (toString module.statementsName)).compress
  let source := folder / "Stated.lean"
  IO.FS.writeFile source module.statements
  let object := source.withExtension "olean"
  let lean ← runSetupLean setupPath source object
  return { space := module.space, theorems := module.stated, setup, object, lean }

/-- The statements are accepted: Lean ends without an error, and each theorem of the module
rests on the allowed axioms at most. The module holds no text, so what Lean reports of it is
what is so. -/
def Stated.accepted (stated : Stated) (name : String) : IO Unit := do
  try acceptedOutput stated.space stated.lean.1 stated.lean.2 stated.theorems allowed
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

/-- A proof module compiled: Lean's result on it, the setup that it was compiled with, its
object, and where the check keeps what it gives to the reading. -/
structure Proved where
  lean : Bool × String
  given : System.FilePath
  setup : System.FilePath
  object : System.FilePath

/-- Lean on a proof module of `module`, compiled to an object against the compiled statements.
`text` is the proof module as it is compiled (a control appends its requests for axioms). The
setup names, for the module of the statements, the object that the check compiled; it and the
statements stand outside the folder `<name>`, which is all that the run can write. -/
def compileProof (work : System.FilePath) (name : String) (module : Module) (stated : Stated)
    (text : String := module.proof) : IO Proved := do
  let given ← folderAt (work / s!"{name}.given")
  let setup ← if module.proofImports.isEmpty then pure stated.setup
    else lakeSetup given (module.statedImports ++ module.proofImports)
  let arts ← IO.ofExcept (setup.getObjVal? "importArts")
  let arts := arts.setObjVal! (toString module.statementsName)
    (.arr #[.arr #[.str stated.object.toString]])
  let setupPath := given / "setup.json"
  IO.FS.writeFile setupPath ((setup.setObjVal! "name" name).setObjVal! "importArts" arts).compress
  let source := (← folderAt (work / name)) / s!"{name}.lean"
  IO.FS.writeFile source text
  let object := source.withExtension "olean"
  let (ok, output) ← runSetupLean setupPath source object
  return { lean := (ok, atText source module output), given, setup := setupPath, object }

/-- The components of a name. -/
def components : Lean.Name → List String
  | .str rest part => components rest ++ [part]
  | .num rest part => components rest ++ [toString part]
  | .anonymous => []

/-- What a check asks the program outside the file of a proof module: the module of the
statements, the allowed axioms, the published pairs and every theorem that the proof module has
to have, names as lists of components. -/
def manifest (module : Module) (axioms : List String) : Lean.Json :=
  let name (parts : List String) : Lean.Json := .arr (parts.map Lean.Json.str).toArray
  .mkObj [
    ("statements", name (components module.statementsName)),
    ("allowed", .arr (axioms.map fun axiom_ => name (axiom_.splitOn ".")).toArray),
    ("pairs", .arr (module.published.map fun (theorem_, proposition) =>
      .arr #[name (components theorem_), name (components proposition)]).toArray),
    ("theorems", .arr (module.proved.map fun theorem_ =>
      name (module.space :: theorem_.splitOn ".")).toArray)]

/-- The program that reads a proof module outside the file, as the formal package builds it
(`zkc-verify-publication`, from `Zkc/Tools/Formal/VerifyPublication.lean`), by its path from the
package's folder, in which a check runs. A check does not build it: the sandbox in which it
runs can write nothing of the package. -/
def program : String := ".lake/build/bin/zkc-verify-publication"

/-- What Lean and the program outside the file gave on a proof module: Lean's result on it,
and, where Lean accepted it, whether the program outside accepted it and what it printed. -/
structure Outside where
  lean : Bool × String
  verified : Option (Bool × String) := none

/-- Lean on a proof module, against the compiled statements, and then the program outside the
file on its object. The object is whatever the run of Lean on the text left in the module's
folder, and the program maps it into memory as an object without checking its format: it reads
the object in the sandbox too, in a folder of its own, so that a malformed object can change no
file. The verdict is the program's. -/
def proveOutside (work : System.FilePath) (name : String) (module : Module) (stated : Stated)
    (axioms : List String := allowed) : IO Outside := do
  unless stated.lean.1 do
    throw (IO.userError s!"{name}: Lean refused the module of the statements\n{stated.lean.2}")
  let proved ← compileProof work name module stated
  unless proved.lean.1 do return { lean := proved.lean }
  let manifestPath := proved.given / "manifest.json"
  IO.FS.writeFile manifestPath (manifest module axioms).compress
  let out ← confined (← folderAt (work / s!"{name}.reading"))
    #["lake", "env", program, proved.setup.toString, manifestPath.toString, proved.object.toString]
  return { lean := proved.lean, verified := some (out.exitCode == 0, out.stdout ++ out.stderr) }

/-- The two modules compiled, one after the other, and the proof module read outside. -/
def readOutside (work : System.FilePath) (name : String) (module : Module)
    (axioms : List String := allowed) : IO Outside := do
  proveOutside work name module (← compileStated work name module) axioms

/-- What a task gives, continued by `next` when it has ended; an error of the task is the
error of the result. -/
def andThen {α β : Type} (task : Task (Except IO.Error α)) (next : α → IO β) :
    IO (Task (Except IO.Error β)) :=
  IO.bindTask task fun
    | .ok value => IO.asTask (next value)
    | .error error => pure (Task.pure (.error error))

/-- Lean on the module of the statements of `module`, as a task. -/
def startStated (work : System.FilePath) (name : String) (module : Module) :
    IO (Task (Except IO.Error Stated)) :=
  IO.asTask (compileStated work name module)

/-- A module is accepted: Lean accepts the proof module with nothing left to `sorry`, and the
program outside the file accepts its object. A module that Lean accepts and that program
refuses is an error here, with what the program said. -/
def Outside.accepted (outside : Outside) (name : String) : IO Unit := do
  acceptedOutput name outside.lean.1 outside.lean.2 []
  match outside.verified with
  | some (true, _) => pure ()
  | some (false, said) =>
    throw (IO.userError s!"{name}: Lean accepted the module, and outside the file it is refused\n{said}")
  | none => throw (IO.userError s!"{name}: the module was not read outside the file")

/-- The two modules of `module`, as a task that ends when both are accepted: the statements by
Lean, with their theorems on the allowed axioms, and the proof module by Lean and outside the
file. The result is Lean's output on the proof module. The module has to publish theorems: one
that publishes nothing is an error, so that a module whose list was lost is not accepted
unread. -/
def startModule (work : System.FilePath) (name : String) (module : Module)
    (axioms : List String := allowed) : IO (Task (Except IO.Error (Bool × String))) := do
  if module.published.isEmpty then
    throw (IO.userError s!"{name}: the module names no published theorem to read outside the file")
  andThen (← startStated work name module) fun stated => do
    stated.accepted name
    let outside ← proveOutside work name module stated axioms
    outside.accepted name
    return outside.lean

/-- The two modules of a module that Lean must refuse in its proof module, as a task: the
statements, which are accepted, and the proof module with the requests for the axioms of its
theorems. The result is Lean's on the proof module. For a control that is not of a subject
(`Control` is). -/
def startRefused (work : System.FilePath) (name : String) (module : Module) :
    IO (Task (Except IO.Error (Bool × String))) := do
  andThen (← startStated work name module) fun stated => do
    stated.accepted name
    return (← compileProof work name module stated (module.proof ++ module.requests)).lean

/-- What the program outside the file said of a module that Lean accepts and that it must
refuse: each of `places`. -/
def Outside.refused (outside : Outside) (title name : String) (places : List String) : IO Unit := do
  acceptedOutput name outside.lean.1 outside.lean.2 []
  match outside.verified with
  | some (false, said) =>
    unless places.all (fun place => said.contains place) do
      throw (IO.userError s!"{title}: refused outside the file for another reason\n{said}")
  | _ => throw (IO.userError s!"{title}: the module was accepted outside the file")

/-- A control of the reading outside the file: Lean accepts the two modules, and the program
outside the file refuses the proof module, saying each of `places`. -/
def refusedOutside (work : System.FilePath) (title name : String) (module : Module)
    (places : List String) : IO Unit := do
  (← readOutside work name module).refused title name places

/-- Several pairs as one source: the imports of all of them, and then for each pair its
statements, its proof module and the requests for the axioms of the proof module's theorems.
For a module of a check that must hold two programs at once, so that what is generated for both
is in scope together. Such a module is judged by what Lean says of it; it is not read outside
the file. -/
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
  hold of the altered source or model, and the proof module is not read. -/
  | generated
  /-- Outside the file: Lean accepts both modules. -/
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
  /-- The description of the model, where the control states a claim about another class. -/
  model : Option ModelText := none
  /-- Where it is refused. -/
  refusal : Refusal := .text
  /-- The theorems that are left unproved, themselves or by what they use, and no other: of the
  theorems of the module that Lean refuses (the proof module, or the module of the statements
  of a control that is refused there). Nothing is unproved in a control that is refused outside
  the file. -/
  unproved : List String := []
  /-- The texts of the places at which the module is refused: each occurs in Lean's output, or
  in what the program outside the file says. -/
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

/-- A control whose modules Lean is reading. -/
structure Running where
  control : Control
  space : String
  task : Task (Except IO.Error Ran)

/-- The modules of a control, started. The name space is the subject's (`space`). A control
whose statements are those of the subject, character for character (it alters only the text),
is compiled against the subject's object; another has its own statements compiled. A control
that Lean must refuse has the requests for the axioms of its theorems appended, from which the
unproved ones are read. -/
def Control.start (work : System.FilePath) (space : String) (proof : Proof) (honest : Module)
    (honestStated : Task (Except IO.Error Stated)) (control : Control) : IO Running := do
  let module ← control.subject.module space proof control.text control.model
  let stated ← if module.statements == honest.statements then pure honestStated
    else startStated work control.name module
  let task ← andThen stated fun stated => do
    unless stated.lean.1 do
      return { refusal := .generated, theorems := module.stated, outside := { lean := stated.lean } : Ran }
    if control.refusal == .outside then
      return { refusal := .outside, theorems := [], outside := ← proveOutside work control.name module stated }
    let proved ← compileProof work control.name module stated (module.proof ++ module.requests)
    return { refusal := .text, theorems := module.proved, outside := { lean := proved.lean } }
  return ⟨control, space, task⟩

/-- A control judged: it was refused where it says, the theorems left unproved are those that
it names, and it was refused at the places that it names. -/
def Running.finish (running : Running) : IO Unit := do
  let control := running.control
  let ran ← IO.ofExcept running.task.get
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

/-- A subject whose modules Lean is reading: its two modules, the module in which Lean reads
the source again, and its controls. -/
structure Checking where
  name : String
  honest : Task (Except IO.Error (Bool × String))
  comparison : Task (Except IO.Error (Bool × String))
  controls : List Running

/-- Lean on the modules of a subject: the module of the statements, then, at once, the proof
module, which is read outside the file, and each control; and the comparison of the package
with the frontend. -/
def start (work : System.FilePath) (name : String) (subject : Subject) (proof : Proof)
    (controls : List Control := []) : IO Checking := do
  let module ← subject.module name proof
  if module.published.isEmpty then
    throw (IO.userError s!"{name}: the module names no published theorem to read outside the file")
  let stated ← startStated work name module
  let honest ← andThen stated fun stated => do
    stated.accepted name
    let outside ← proveOutside work name module stated
    outside.accepted name
    return outside.lean
  let comparison ← startLakeLean work s!"{name}Source"
    (comparisonModule s!"{name}Source" subject.text (subject.goals.map (·.goal)) subject.package)
  return ⟨name, honest, comparison, ← controls.mapM (·.start work name proof module stated)⟩

/-- A subject judged: Lean accepts the module of its statements, with every theorem on the
allowed axioms; Lean accepts its proof module, and the module is accepted outside the file;
Lean accepts the module in which it reads the source again; each control is refused as it
says. The result is Lean's output on the proof module. -/
def Checking.finish (checking : Checking) : IO (Bool × String) := do
  let (ok, output) ← finishLean checking.honest
  let (sourceOk, sourceOutput) ← finishLean checking.comparison
  acceptedOutput s!"{checking.name}Source" sourceOk sourceOutput []
  for control in checking.controls do
    control.finish
  return (ok, output)

/-- A subject checked: `start`, then `finish`. -/
def check (work : System.FilePath) (name : String) (subject : Subject) (proof : Proof)
    (controls : List Control := []) : IO (Bool × String) := do
  (← start work name subject proof controls).finish

end Zkc.Tests.Formal.WrittenSubject
