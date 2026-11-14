import Zkc.Core.Package
import Zkc.Core.Concrete
import Zkc.Core.Unelaborate
import Zkc.Core.Serialize
import Zkc.Core.Pipeline
import Zkc.Core.Admissible
import Zkc.Core.Copies
import Zkc.Core.Retarget
import Zkc.Core.Construction
import Zkc.Tools.Core.PrintLinked

/-! The compiled tool: read, admit, construct, project, print.

Every step between reading and printing is one of the definitions that the theorems of
this package speak of, compiled. The executable links neither Lean's elaborator nor its
JSON library.

Two commands are checked. `admit` is `Zkc.Core.admit` on the package as a program as written,
and `compile` is `Zkc.Core.compile`: admission, the construction of the declared scheme on the
admitted package with admission after each step, and projection. Neither assembles a check of
its own, so a check that admission gains is a check that the tool makes. With `--vocabulary`
the package is stated to have the rows and the literal data of the vocabulary. With `--phases`
the gates of admission are also timed one by one; those times are measurements and decide
nothing.

The commands under `step` apply one definition to a package that elaborates. They admit
nothing, and what they print is not a compiled program: they exist to print the fixtures that
the kernel compares with its own evaluation of the same definitions, and to look at one step.
-/

open Zkc Zkc.Core Zkc.Source

@[noinline] def timed {α : Type} (label : String) (compute : Unit → Except String α) : IO α := do
  let start ← IO.monoNanosNow
  let result ← pure (compute ())
  let stop ← IO.monoNanosNow
  IO.eprintln s!"{label}: {(stop - start) / 1000} us"
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

mutual
  /-- The number of instructions of a region, nested regions included. -/
  def regionCount {dialect : Dialect} : {Γ out : List dialect.Ty} → Region dialect Γ out → Nat
    | _, _, .ret _ => 0
    | _, _, .stop _ => 0
    | _, _, .letOp _ _ bodies next => 1 + regionsCount bodies + regionCount next
    | _, _, .bind body next => regionCount body + regionCount next

  def regionsCount {dialect : Dialect} :
      {signatures : List (List dialect.Ty × List dialect.Ty)} → Regions dialect signatures → Nat
    | _, .nil => 0
    | _, .cons body tail => regionCount body + regionsCount tail
end

/-- The number of instructions of the normal forms of the functions of a program. -/
def functionsNormalSize {typeTable : TypeTable} {operations : List OperationSignature} :
    {functions : List FunctionHeader} → Functions typeTable operations functions → Nat
  | _, .nil => 0
  | _, .snoc earlier definition _ =>
      functionsNormalSize earlier + regionCount definition.normal.body
  | _, .opaque earlier _ _ => functionsNormalSize earlier

/-- The number of instructions of the normal forms of the protocols of a program. -/
def protocolsNormalSize {typeTable : TypeTable} {operations : List OperationSignature}
    {functions : List FunctionHeader} :
    {protocols : List ProtocolHeader} → Protocols typeTable operations functions protocols → Nat
  | _, .nil => 0
  | _, .snoc earlier definition _ =>
      protocolsNormalSize earlier + regionCount definition.normal.body

/-- The number of instructions of the normal form of every body of a package. -/
def normalSize (typed : Typed) : Nat :=
  functionsNormalSize typed.program.functions + protocolsNormalSize typed.program.protocols

/-- The raw package of the protocols a step produced, with the tables and functions of
the typed package. Names do not leave the module. -/
def unelaborateStepped (typed : Typed)
    (stepped : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions) :
    Raw.Package :=
  ⟨typed.types.map CatalogueRow.strip, typed.records, typed.variants,
    typed.table.map Operation.strip,
    unelaborateFunctions typed.functions.length typed.program.functions [],
    unelaborateProtocols typed.functions.length stepped.headers.length stepped.protocols [], none⟩

def describeRefusal (refusal : StepRefusal) : String := s!"refused by the step: {repr refusal}"

/-- Where the protocols of a result come from, oldest first, for a small result. -/
def reportOrigins (origins : List Origin) : IO Unit := do
  IO.eprintln s!"protocols after the step: {origins.length}"
  if origins.length ≤ 16 then
    for origin in origins.reverse do
      let roles := match origin.roles with
        | some roles => s!"prover {roles.prover}, verifier {roles.verifier}"
        | none => "unchanged"
      IO.eprintln s!"  definition {origin.definition}: {roles}{if origin.entry then ", entry" else ""}"

/-! ## Expansion and projection -/

def refused {α : Type} (step : String) (result : Except PipelineRefusal α) : Except String α :=
  result.mapError fun refusal => s!"refused by {step}: {repr refusal}"

/-- The name of a site of a protocol: its recorded name, or its numbers. -/
def siteName (names : Option Raw.Names) (site : Point) : String :=
  match names.bind fun names => (names.sites[site.definition]?).bind (·[site.number]?) with
  | some name => name
  | none => s!"p{site.definition}.s{site.number}"

/-- The name of a site of an expanded entry: the names of the applications it was reached
through and its own, in order. -/
def originName (names : Option Raw.Names) (origin : SiteOrigin) : String :=
  "/".intercalate ((origin.applications ++ [origin.site]).map (siteName names))

/-- The package of an expanded entry: the functions of the package and the one protocol,
whose sites are named by where they come from. -/
def expandedPackage (typed : Typed) (protocol : Raw.Protocol) (origins : List SiteOrigin) :
    Raw.Package :=
  let entry := typed.protocols.length - 1
  let names : Option Raw.Names := typed.names.map fun names =>
    { functions := names.functions, protocols := (names.protocols[entry]?).toList,
      roles := (names.roles[entry]?).toList, sites := [origins.map (originName typed.names)] }
  ⟨typed.types.map CatalogueRow.strip, typed.records, typed.variants,
    typed.table.map Operation.strip,
    unelaborateFunctions typed.functions.length typed.program.functions [], [protocol], names⟩

/-- Time a computation that has no refusal of its own. -/
@[noinline] def measured {α : Type} (label : String) (compute : Unit → α) : IO α := do
  let start ← IO.monoNanosNow
  let result ← pure (compute ())
  let stop ← IO.monoNanosNow
  IO.eprintln s!"{label}: {(stop - start) / 1000} us"
  pure result

/-- What is stated beside a package that the tool is given. On the command line a producer
can state that the rows and the literal data are the vocabulary's; the keys of sites and which
functions can stop are stated by a producer that has them, through `Zkc.Core.admit`. -/
def claimsOf (vocabulary : Bool) : Admission.Claims :=
  if vocabulary then { rows := some Vocabulary.table, literals := some Vocabulary.table } else {}

def describeAdmission (refusals : List Admission.Refusal) : String :=
  "\n".intercalate (refusals.map fun refusal => s!"  {repr refusal}")

def describeCompilation : CompileRefusal → String
  | .admission refusals => s!"not admitted as written:\n{describeAdmission refusals}"
  | .construction .stepped => "not constructed: the package is not a program as written"
  | .construction (.step refusal) => s!"not constructed: refused by the step: {repr refusal}"
  | .construction (.derived refusals) =>
      s!"not constructed: what the Fiat–Shamir step returns is not admitted:\n{describeAdmission refusals}"
  | .construction (.serialized refusals) =>
      s!"not constructed: what the serialize step returns is not admitted:\n{describeAdmission refusals}"
  | .projection refusal => s!"not projected: {repr refusal}"

/-- The gates of admission one by one, each with its time. A measurement: the verdict is
`Zkc.Core.admit`'s. -/
def reportPhases (raw : Raw.Package) : IO Unit := do
  match ← measured "phase: elaborate" fun _ => elaborate raw with
  | .error _ => IO.eprintln "phases: the package does not elaborate"
  | .ok typed =>
      let size ← measured "phase: normal form" fun _ => normalSize typed
      let admissible ← measured "phase: normal form and check of facts" fun _ =>
        typed.program.admissible
      let coherent ← measured "phase: check of copies" fun _ => typed.program.protocols.coherent
      IO.eprintln s!"phases: normal form of {size} instructions; facts {admissible}; copies {coherent}"

/-! ## Printing a linked package -/

/-- One `key=value` setting of the printer. -/
def setting (options : PrintLinked.Options) (text : String) : Except String PrintLinked.Options :=
  match text.splitOn "=" with
  | ["piece", value] => .ok { options with piece := value.toNat! }
  | ["share", value] => .ok { options with share := value == "true" }
  | ["literals", value] => .ok { options with literals := value == "true" }
  | ["kernel-proofs", value] => .ok { options with kernelProofs := value == "true" }
  | ["skips", value] => .ok { options with skips := value == "true" }
  | ["written", value] => .ok { options with written := value == "true" }
  | ["parts", value] => .ok { options with parts := value.toNat! }
  | ["linked-definitions", value] => .ok { options with linkedDefinitions := value == "true" }
  | _ => .error s!"unknown setting {text}"

def sourceHeader (imports : List String) (namespaceName : String) : String :=
  "\n".intercalate (imports.map fun name => s!"import {name}") ++
    "\n\n/-! Printed by `core-tool literal`. Nothing here is trusted beyond the raw definitions:\n" ++
    "the kernel type-checks every typed term and decides every fact that links it to them. -/\n" ++
    "\nset_option autoImplicit false\nset_option maxRecDepth 1000000\n" ++
    "open Zkc.Source Zkc.Core Zkc.Core.Raw\n" ++ s!"namespace {namespaceName}\n\n"

def writeSource (linked : Bool) (path : System.FilePath) (imports : List String)
    (namespaceName : String) (declarations : Array String) : IO Nat := do
  let handle ← IO.FS.Handle.mk path .write
  handle.putStr (sourceHeader imports namespaceName)
  let mut bytes := 0
  for declaration in declarations do
    let declaration := if linked then declaration
      else declaration.replace "linked_def " "noncomputable def "
    handle.putStr declaration
    handle.putStr "\n\n"
    bytes := bytes + declaration.utf8ByteSize + 2
  handle.putStr s!"end {namespaceName}\n"
  pure bytes

/-- Write the Lean source of a linked package: with no parts one file, otherwise a
prelude, one file per part, and the file that assembles them. A part holds units, each of
which needs only the prelude, so the parts can be checked at the same time; they are
balanced by the size of their source. -/
def writeLinked (source : PrintLinked.Source) (options : PrintLinked.Options) (directory module : String) :
    IO Unit := do
  let base := ["Zkc.Core.Link", "Zkc.Tests.Core.Reflexivity"]
  let definitions := source.functions ++ source.protocols
  let units := definitions.flatMap (·.units)
  let closing := definitions.flatMap (·.closing)
  let root : System.FilePath := directory
  let write := writeSource options.linkedDefinitions
  if options.parts == 0 then
    let all := source.prelude ++ units.flatMap id ++ closing ++ source.assembly
    let bytes ← write (root / s!"{module}.lean") base module all
    IO.eprintln s!"source: {bytes} bytes in one file, {all.size} declarations"
  else
    IO.FS.createDirAll (root / module)
    let mut bytes ← write (root / module / "Prelude.lean") base module source.prelude
    let mut declarations := source.prelude.size
    let size (unit : Array String) : Nat := unit.foldl (fun sum text => sum + text.utf8ByteSize) 0
    let total := units.foldl (fun sum unit => sum + size unit) 0
    let mut part := 0
    let mut current : Array String := #[]
    let mut seen := 0
    let mut names : List String := []
    for unit in units do
      current := current ++ unit
      seen := seen + size unit
      if seen * options.parts ≥ (part + 1) * total then
        bytes := bytes + (← write (root / module / s!"Part{part}.lean")
          [s!"{module}.Prelude"] module current)
        declarations := declarations + current.size
        names := names ++ [s!"{module}.Part{part}"]
        part := part + 1
        current := #[]
    if !current.isEmpty then
      bytes := bytes + (← write (root / module / s!"Part{part}.lean")
        [s!"{module}.Prelude"] module current)
      declarations := declarations + current.size
      names := names ++ [s!"{module}.Part{part}"]
    bytes := bytes + (← write (root / s!"{module}.lean") (s!"{module}.Prelude" :: names) module
      (closing ++ source.assembly))
    IO.eprintln s!"source: {bytes} bytes in {names.length + 2} files, {declarations + closing.size + source.assembly.size} declarations"

def readTyped (path : String) : IO Typed := do
  let source ← IO.FS.readFile path
  let raw ← timed "parse" fun _ => Raw.parsePackage source
  timed "elaborate" fun _ =>
    (elaborateWritten raw).mapError fun refusal => s!"refused package: {repr refusal}"

def readDeclaration (path : String) : IO Raw.Declaration := do
  let source ← IO.FS.readFile path
  match Raw.parseDeclaration source with
  | .ok declaration => pure declaration
  | .error message => throw (IO.userError message)

def printStepped (typed : Typed)
    (stepped : Stepped typed.typeTable (typed.table.map (·.signature)) typed.functions) :
    IO Unit := do
  reportOrigins stepped.origins
  let back ← timed "unelaborate" fun _ => pure (unelaborateStepped typed stepped)
  let text ← timed "print" fun _ => pure (Raw.printPackage back).render
  IO.println text

/-- The checked commands, on a package read from a file. -/
def checked (command : String) (path : String) (declaration : Option String)
    (vocabulary phases : Bool) : IO UInt32 := do
  let source ← IO.FS.readFile path
  let raw ← timed "parse" fun _ => Raw.parsePackage source
  let claims := claimsOf vocabulary
  match command with
  | "admit" =>
      let result ← measured "admission" fun _ => admit raw claims
      if phases then reportPhases raw
      match result with
      | .ok admitted =>
          IO.println s!"admitted as written: {admitted.typed.functions.length} functions, {admitted.typed.protocols.length} protocols{if vocabulary then "; rows and literal data of the vocabulary" else ""}"
          pure 0
      | .error refusals =>
          IO.println s!"not admitted as written:\n{describeAdmission refusals}"
          pure 1
  | _ =>
      let declaration ← declaration.mapM readDeclaration
      let result ← measured "compilation" fun _ => compile raw claims declaration
      if phases then reportPhases raw
      match result with
      | .ok roles =>
          let text ← measured "print" fun _ => (Raw.printRolePrograms roles).render
          IO.println text
          pure 0
      | .error refusal =>
          IO.eprintln (describeCompilation refusal)
          pure 1

/-- One definition applied to a package that elaborates. Nothing is admitted. -/
def step (arguments : List String) : IO UInt32 := do
  match arguments with
  | [command, path, declaration] =>
      let typed ← readTyped path
      let declaration ← readDeclaration declaration
      match command with
      | "fiat-shamir" =>
          let constructed ← timed "fiat-shamir" fun _ =>
            (fiatShamir typed declaration).mapError describeRefusal
          printStepped typed constructed
          pure 0
      | "serialize" =>
          let constructed ← timed "fiat-shamir" fun _ =>
            (fiatShamir typed declaration).mapError describeRefusal
          let serialized ← timed "serialize" fun _ =>
            (serializeProtocols declaration constructed.identities constructed.protocols).mapError describeRefusal
          printStepped typed serialized
          pure 0
      | "serialize-authored" =>
          -- Serialize alone, for a program whose construction is authored.
          let serialized ← timed "serialize" fun _ =>
            (serializeProtocols declaration Identities.written typed.program.protocols).mapError describeRefusal
          printStepped typed serialized
          pure 0
      | other => throw (IO.userError s!"unknown step {other}")
  | [command, path] =>
      let source ← IO.FS.readFile path
      let raw ← timed "parse" fun _ => Raw.parsePackage source
      match command with
      | "elaborate-written" =>
          -- Elaboration alone, of a program as written: its sites are numbered without gaps.
          let typed ← timed "elaborate" fun _ =>
            (elaborateWritten raw).mapError fun refusal => s!"refused package: {repr refusal}"
          IO.println s!"elaborates as written, not admitted: {typed.functions.length} functions, {typed.protocols.length} protocols"
          pure 0
      | "elaborate" =>
          -- Elaboration alone, of what a step produced: its sites need not be numbered
          -- without gaps.
          let typed ← timed "elaborate" fun _ =>
            (elaborate raw).mapError fun refusal => s!"refused package: {repr refusal}"
          IO.println s!"elaborates, not admitted: {typed.functions.length} functions, {typed.protocols.length} protocols"
          pure 0
      | "roundtrip" =>
          let typed ← timed "elaborate" fun _ =>
            (elaborate raw).mapError fun refusal => s!"refused package: {repr refusal}"
          let back ← timed "unelaborate" fun _ => pure (unelaborate typed)
          let text ← timed "print" fun _ => pure (Raw.printPackage back).render
          IO.println text
          pure 0
      | "copies" =>
          -- Every protocol twice, each `apply` naming the callee's copy for the same key.
          let typed ← timed "elaborate" fun _ =>
            (elaborateWritten raw).mapError fun refusal => s!"refused package: {repr refusal}"
          let copied ← timed "copy" fun _ =>
            (copyProtocols [0, 1] typed.program.protocols).mapError fun refusal =>
              s!"refused by the step: {repr refusal}"
          let back ← timed "unelaborate" fun _ => pure
            (⟨typed.types.map CatalogueRow.strip, typed.records, typed.variants,
              typed.table.map Operation.strip,
              unelaborateFunctions typed.functions.length typed.program.functions [],
              unelaborateProtocols typed.functions.length copied.new.length copied.protocols [],
              none⟩ : Raw.Package)
          let text ← timed "print" fun _ => pure (Raw.printPackage back).render
          IO.println text
          pure 0
      | "expand" =>
          -- The entry without applications, as a package with one protocol.
          let typed ← timed "elaborate" fun _ =>
            (elaborateWritten raw).mapError fun refusal => s!"refused package: {repr refusal}"
          let ⟨_, nested⟩ ← timed "expand" fun _ => refused "expansion" typed.expandEntryNested
          let flat ← timed "flatten" fun _ => pure nested.flatten
          let violation ← timed "residual conditions" fun _ =>
            pure (flat.definition.violation typed.typeTable)
          if let some violation := violation then
            throw (IO.userError s!"the expanded entry violates {repr violation}")
          let protocol ← timed "unelaborate" fun _ => pure (flat.raw typed.functions.length)
          let text ← timed "print" fun _ => pure
            (Raw.printPackage (expandedPackage typed protocol flat.origins)).render
          IO.println text
          pure 0
      | "expand-nested" =>
          -- The entry with each application replaced by a nested block; no residual check.
          let typed ← timed "elaborate" fun _ =>
            (elaborateWritten raw).mapError fun refusal => s!"refused package: {repr refusal}"
          let ⟨_, nested⟩ ← timed "expand" fun _ => refused "expansion" typed.expandEntryNested
          let protocol ← timed "unelaborate" fun _ => pure (nested.raw typed.functions.length)
          let text ← timed "print" fun _ => pure
            (Raw.printPackage (expandedPackage typed protocol nested.origins)).render
          IO.println text
          pure 0
      | "project" =>
          -- The role programs of the expanded entry.
          let typed ← timed "elaborate" fun _ =>
            (elaborateWritten raw).mapError fun refusal => s!"refused package: {repr refusal}"
          let ⟨header, nested⟩ ← timed "expand" fun _ => refused "expansion" typed.expandEntryNested
          let flat ← timed "flatten" fun _ => pure nested.flatten
          let roles ← timed "project" fun _ =>
            refused "projection" (projectRoles typed.functions.length flat header.roles [])
          let text ← timed "print" fun _ => pure (Raw.printRolePrograms roles).render
          IO.println text
          pure 0
      | "calls" =>
          -- The role programs of every protocol, with applications kept as calls.
          let typed ← timed "elaborate" fun _ =>
            (elaborateWritten raw).mapError fun refusal => s!"refused package: {repr refusal}"
          let roles ← timed "project" fun _ => refused "projection" typed.calledRoles
          let text ← timed "print" fun _ => pure (Raw.printRolePrograms roles).render
          IO.println text
          pure 0
      | other => throw (IO.userError s!"unknown step {other}")
  | _ => throw (IO.userError "step: expected a step, a package and, for a step of a scheme, a declaration")

def usage : IO UInt32 := do
  IO.eprintln "usage: core-tool admit <package.json> [--vocabulary] [--phases]"
  IO.eprintln "       core-tool compile <package.json> [<declaration.json>] [--vocabulary] [--phases]"
  IO.eprintln "       core-tool step (elaborate-written | elaborate | roundtrip | copies | expand | expand-nested | project | calls) <package.json>"
  IO.eprintln "       core-tool step (fiat-shamir | serialize | serialize-authored) <package.json> <declaration.json>"
  IO.eprintln "       core-tool literal <package.json> <directory> <Module> [setting=value ...]"
  IO.eprintln "       core-tool selftest"
  IO.eprintln "admit and compile are Zkc.Core.admit and Zkc.Core.compile. A step applies one"
  IO.eprintln "definition to a package that elaborates and admits nothing."
  pure 2

def main (arguments : List String) : IO UInt32 := do
  let vocabulary := arguments.contains "--vocabulary"
  let phases := arguments.contains "--phases"
  match arguments.filter fun argument => argument != "--vocabulary" && argument != "--phases" with
  | ["selftest"] =>
      -- The constants of the concrete data: SHA-256 vectors and the group G1.
      let mut failed := false
      for (name, holds) in Concrete.selfTest () do
        IO.println s!"{name}: {if holds then "holds" else "FAILS"}"
        failed := failed || !holds
      pure (if failed then 1 else 0)
  | "literal" :: path :: directory :: module :: settings =>
      let options ← match settings.foldlM setting {} with
        | .ok options => pure options
        | .error message => throw (IO.userError message)
      let text ← IO.FS.readFile path
      let raw ← timed "parse" fun _ => Raw.parsePackage text
      let typed ← timed "elaborate" fun _ =>
        ((if options.written then elaborateWritten raw else elaborate raw)).mapError fun refusal =>
          s!"refused package: {repr refusal}"
      let source ← timed "print" fun _ => pure (PrintLinked.printPackage options typed raw)
      writeLinked source options directory module
      pure 0
  | "step" :: rest => step rest
  | ["admit", path] => checked "admit" path none vocabulary phases
  | ["compile", path] => checked "compile" path none vocabulary phases
  | ["compile", path, declaration] => checked "compile" path (some declaration) vocabulary phases
  | _ => usage
