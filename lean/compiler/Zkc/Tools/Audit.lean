import Lean

/-!
# The audit of the libraries

A library is audited in an environment that imports it from the built `.olean` files, at the
level that keeps every declaration and every proof, private ones included. A library proper is
imported by its root module. A library of tests has no module that imports all of its modules:
it is imported by the modules of its files that are built. For every constant declared in a
module of a library:

- the axioms it depends on are among `propext`, `Classical.choice` and `Quot.sound`; in
  particular no proof uses `sorryAx`. The constants that the audited ones use are visited once
  for the whole run (`dependencies`), and a forbidden axiom is traced back to every audited
  constant that reaches it;
- it carries no `@[extern]` and no `@[implemented_by]`. The executable code that Lean itself
  makes for a `partial` definition is not a finding; the number of `partial` definitions of each
  library (the recursive ones, a `where` helper of one included: Lean compiles a `partial`
  definition that does not recur as an ordinary one) is reported, so that a new one is a
  visible difference;
- the kernel accepts it (`replayLibrary`). Reading a constant from a built file says nothing of
  whether the kernel checked it: a theorem elaborated under `set_option debug.skipKernelTC` is
  stored with whatever proof the elaborator built. So the declarations of a library are replayed
  through the kernel (`Lean.Kernel.Environment.replay`), module after module, on an environment
  that imports only the modules outside the library that the library imports. The kernel does
  not check unsafe declarations, and the replay skips them and the code of `partial`
  definitions, as Lean's own replay does. The modules outside the library are taken as built,
  and the audit prints which they are: Lean's libraries, modules of the libraries that the
  audits replay, and modules that no audit replays (the tools that a library of tests imports
  are such). A library can be left out of the replay, with the
  reason (`Library.withoutReplay`): the frontend is, since it is the unproved part of the
  compiler and no theorem of the project rests on it.

The rules on imports hold for a library proper and are read from the headers of the modules: a
module of the library imports only modules of the library itself and of the prefixes that the
library allows (`imports`), and no module of the library imports a module of the tests or of the
tools (`Zkc.Tests`, `Zkc.Tools`). Every `.lean` file under the directory of a library proper is a
module that its root module imports, directly or not. Every `.lean` file under the directory of
a library of tests is a module of the environment that the audit loads, so that no file of the
tests is left unbuilt and unaudited.

`run` audits the libraries, then the controls (`controls`): modules under
`Zkc.Tools.Audit.Controls` that the audit must refuse, each by one rule. The exit code is 0 only
when the libraries pass and every control is refused by its rule; every finding is one line that
names the constant or the module and the rule.
-/

set_option autoImplicit false

namespace Zkc.Tools.Audit

open Lean

/-- The kinds of library. -/
inductive Kind where
  /-- A library proper: its root module imports every module of the library. -/
  | library
  /-- A library of tests: its modules are the files under its directory. -/
  | tests
  deriving BEq, Inhabited

/-- A library to audit. -/
structure Library where
  /-- The name of the library in the report. -/
  name : String
  /-- The root module: a module of the library is the root or a module under it. -/
  root : Name
  kind : Kind := .library
  /-- For a library proper, the prefixes of the modules outside the library that its modules may
  import; `none` when they may import any module that is not of the tests or of the tools. -/
  imports : Option (Array Name) := none
  /-- The directory that holds the root's file and the directory of its modules, when the files
  are checked against the modules that the audit reads. -/
  directory : Option System.FilePath := none
  /-- Why the declarations of the library are not replayed through the kernel, when they are
  not. -/
  withoutReplay : Option String := none

/-- Whether a module is of a library. -/
def Library.contains (library : Library) (module : Name) : Bool :=
  library.root.isPrefixOf module

/-- The prefixes of the modules that no module of a library imports: the tests and the tools. -/
def testsAndTools : Array Name := #[`Zkc.Tests, `Zkc.Tools]

/-- The prefixes outside the core that a module of the core may import: Lean's prelude and its
standard library. -/
def coreImports : Array Name := #[`Init, `Std]

/-- The modules that no audit replays through the kernel: the frontend and the tools. -/
def neverReplayed : Array Name := #[`Zkc.Frontend, `Zkc.Tools]

/-- The axioms that a constant of a library may depend on. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The kinds of finding. -/
inductive Rule where
  | axiom_
  | extern
  | implementedBy
  | kernel
  | importOfTestsOrTools
  | importOutside
  | fileNotImported
  | fileNotLoaded
  | moduleMissing
  deriving BEq, Inhabited

/-- What a rule requires, as a phrase. -/
def Rule.describe : Rule → String
  | .axiom_ => "no axiom beyond propext, Classical.choice and Quot.sound"
  | .extern => "no `@[extern]`"
  | .implementedBy => "no `@[implemented_by]`"
  | .kernel => "the kernel accepts every declaration when it is replayed"
  | .importOfTestsOrTools => "no import of a module of the tests or of the tools"
  | .importOutside => "imports only of the library and of the prefixes that it allows"
  | .fileNotImported => "every file of a library is imported by its root"
  | .fileNotLoaded => "every file of a library of tests is in the audit's environment"
  | .moduleMissing => "a library has a file"

/-- One finding: the constant or the module it is about, its rule, and the line it prints. -/
structure Finding where
  subject : Name
  rule : Rule
  line : String
  deriving Inhabited

/-- What an audit found, and what it did for each library. -/
structure Report where
  findings : Array Finding := #[]
  /-- For each library, as lines: its `partial` definitions, and what was replayed through the
  kernel and what was taken as built. -/
  lines : Array String := #[]
  /-- The constants declared in the audited modules, and the constants that they reach. -/
  declarations : Nat := 0
  reached : Nat := 0
  /-- The axioms that the audited constants reach. -/
  axioms : Array Name := #[]

/-- The report with one more finding. -/
def Report.add (report : Report) (subject : Name) (rule : Rule) (line : String) : Report :=
  { report with findings := report.findings.push { subject, rule, line } }

/-- Whether a constant is the code that Lean makes for a `partial` definition: the unsafe
recursive definition beside an opaque constant. A definition by well-founded recursion has such
code too, beside a definition that is not opaque. -/
def isPartialDefinition (env : Environment) (info : ConstantInfo) : Bool :=
  match info.isPartial, Compiler.isUnsafeRecName? info.name with
  | true, some base => (env.find? base matches some (.opaqueInfo _))
  | _, _ => false

/-- The modules of an environment that are of a library, each with its index, in the order of
the environment: a module comes after the modules it imports. -/
def modulesOf (env : Environment) (library : Library) : Array (Nat × Name) :=
  (env.header.moduleNames.zipIdx.filter fun (module, _) => library.contains module).map
    fun (module, index) => (index, module)

/-- The modules that a module imports, directly or not, and the module itself. -/
def importClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let indices : Std.HashMap Name Nat := env.header.moduleNames.zipIdx.foldl
    (fun indices (module, index) => indices.insert module index) {}
  let mut found : NameSet := ({} : NameSet).insert root
  let mut stack := #[root]
  while true do
    let some module := stack.back? | break
    stack := stack.pop
    let some index := indices[module]? | continue
    for imported in env.header.moduleData[index]!.imports do
      unless found.contains imported.module do
        found := found.insert imported.module
        stack := stack.push imported.module
  return found

/-- The constants that a constant uses directly: what `#print axioms` reads of it. -/
def usedConstants (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo _ | .quotInfo _ => #[]
  | .defnInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .thmInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .opaqueInfo value => value.type.getUsedConstants ++ value.value.getUsedConstants
  | .ctorInfo value => value.type.getUsedConstants
  | .recInfo value => value.type.getUsedConstants
  | .inductInfo value => value.type.getUsedConstants ++ value.ctors.toArray

/-- Every constant that the given ones reach, each visited once: the axioms among them, and for
each constant the constants that use it. -/
def dependencies (env : Environment) (starts : Array Name) :
    Array Name × Std.HashMap Name (Array Name) × Nat := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut users : Std.HashMap Name (Array Name) := {}
  let mut axioms : Array Name := #[]
  let mut stack := starts
  for start in starts do visited := visited.insert start
  while true do
    let some name := stack.back? | break
    stack := stack.pop
    let some info := env.find? name | continue
    if info matches .axiomInfo _ then axioms := axioms.push name
    for used in usedConstants info do
      users := users.alter used fun
        | some found => some (found.push name)
        | none => some #[name]
      unless visited.contains used do
        visited := visited.insert used
        stack := stack.push used
  return (axioms, users, visited.size)

/-- The constants that reach an axiom: the axiom itself and every constant that uses one that
reaches it. -/
def reaching (users : Std.HashMap Name (Array Name)) (axiom_ : Name) : Std.HashSet Name := Id.run do
  let mut found : Std.HashSet Name := ({} : Std.HashSet Name).insert axiom_
  let mut stack := #[axiom_]
  while true do
    let some name := stack.back? | break
    stack := stack.pop
    for user in users.getD name #[] do
      unless found.contains user do
        found := found.insert user
        stack := stack.push user
  return found

/-- The `.lean` files under a directory, each as the name of its module relative to `base`. -/
partial def leanFiles (base directory : System.FilePath) : IO (Array Name) := do
  let mut found := #[]
  for entry in (← directory.readDir).qsort (·.fileName < ·.fileName) do
    if ← entry.path.isDir then
      found := found ++ (← leanFiles base entry.path)
    else if entry.path.extension == some "lean" then
      let relative := (entry.path.withExtension "").toString.drop (base.toString.length + 1)
      found := found.push ((relative.toString.splitOn "/").foldl Name.mkStr .anonymous)
  return found

/-- The modules of the `.lean` files of a library under a directory: the file of its root, and
the files under the directory of its root. -/
def libraryFiles (directory : System.FilePath) (root : Name) : IO (Array Name) := do
  let rootFile := (root.components.foldl (fun path part => path / part.toString) directory).addExtension "lean"
  let rootDirectory := rootFile.withExtension ""
  let mut files := #[]
  if ← rootFile.pathExists then files := files.push root
  if ← rootDirectory.isDir then files := files ++ (← leanFiles directory rootDirectory)
  return files

/-- A duration in milliseconds, in seconds. -/
def seconds (milliseconds : Nat) : String :=
  s!"{milliseconds / 1000}.{(milliseconds % 1000) / 100} s"

/-- The replay of the declarations of a library through the kernel, module after module, on an
environment that imports only the modules outside the library that the library imports: the
finding of the first module whose declarations the kernel refuses, after which the replay of the
library stops, and what was replayed and what was taken as built, as lines. -/
def replayLibrary (env : Environment) (library : Library) (arts : NameMap ImportArtifacts) :
    IO (Option Finding × Array String) := do
  let modules := modulesOf env library
  let mut outside : Array Name := #[]
  let mut seen : NameSet := {}
  for (index, _) in modules do
    for imported in env.header.moduleData[index]!.imports do
      unless library.contains imported.module || seen.contains imported.module do
        seen := seen.insert imported.module
        outside := outside.push imported.module
  let start ← IO.monoMsNow
  let base ← importModules (outside.map fun module => { module }) {} (loadExts := false)
    (level := .private) (arts := arts)
  -- a declaration that is already in the environment of the replay would not be checked again
  if let some module := base.header.moduleNames.find? library.contains then
    return (some { subject := module, rule := .kernel
                   line := s!"{module}: the modules outside {library.root} that the library imports import it, so the declarations of {library.root} are not replayed" },
      #[s!"{library.name}: not replayed through the kernel"])
  let mut kernel := base.toKernelEnv
  let mut replayed := 0
  let mut skipped := 0
  for (index, module) in modules do
    let data := env.header.moduleData[index]!
    let mut constants : Std.HashMap Name ConstantInfo := {}
    for name in data.constNames, info in data.constants do
      constants := constants.insert name info
      if info.isUnsafe || info.isPartial then skipped := skipped + 1 else replayed := replayed + 1
    try
      kernel ← kernel.replay constants
    catch error =>
      let message := (toString error).replace "\n" " "
      return (some { subject := module, rule := .kernel
                     line := s!"{module}: the kernel refuses a declaration when it is replayed: {message}; the modules of {library.root} after it are not replayed" },
        #[s!"{library.name}: the replay through the kernel stopped at {module}"])
  -- what the replay took as built: Lean's libraries, the modules of the libraries that an audit
  -- replays, and the modules that no audit replays
  let isNeverReplayed (module : Name) := neverReplayed.any (·.isPrefixOf module)
  let mut fromLean : Array Name := #[]
  for module in base.header.moduleNames do
    unless (`Zkc).isPrefixOf module || fromLean.contains module.getRoot do
      fromLean := fromLean.push module.getRoot
  let replayedElsewhere := (base.header.moduleNames.filter fun module =>
    (`Zkc).isPrefixOf module && !isNeverReplayed module).size
  let notReplayed := base.header.moduleNames.filter isNeverReplayed
  let mut built := [s!"Lean's libraries {", ".intercalate (fromLean.toList.map toString)}"]
  if replayedElsewhere > 0 then
    built := built ++ [s!"{replayedElsewhere} modules of the libraries that the audits replay"]
  unless notReplayed.isEmpty do
    built := built ++ [s!"{", ".intercalate (notReplayed.toList.map toString)}, which no audit replays"]
  return (none, #[
    s!"{library.name}: replayed through the kernel: {replayed} declarations of {modules.size} modules, in {seconds ((← IO.monoMsNow) - start)}; not replayed: {skipped} unsafe declarations and code of `partial` definitions, which the kernel does not check",
    s!"  taken as built: {"; ".intercalate built}"])

/-- The audit of libraries in an environment that imports them. `arts` are the built files of
the modules, for the environments of the replay. -/
def audit (env : Environment) (libraries : Array Library) (arts : NameMap ImportArtifacts) :
    IO Report := do
  let mut report : Report := {}
  let moduleNames := env.header.moduleNames
  -- the constants of the audited modules, and their libraries
  let mut audited : Std.HashSet Name := {}
  let mut constants : Array Name := #[]
  for library in libraries do
    let mut partials := 0
    for (index, _) in modulesOf env library do
      let data := env.header.moduleData[index]!
      for info in data.constants do
        let name := info.name
        audited := audited.insert name
        constants := constants.push name
        if isPartialDefinition env info then partials := partials + 1
        if isExtern env name then
          report := report.add name .extern s!"{name}: carries `@[extern]`"
        if let some implementation := Compiler.getImplementedBy? env name then
          -- the executable code of a `partial` definition is Lean's own
          unless implementation == Compiler.mkUnsafeRecName name do
            report := report.add name .implementedBy
              s!"{name}: carries `@[implemented_by {implementation}]`"
    report := { report with lines := report.lines.push s!"{library.name}: {partials} partial definitions" }
    -- the kernel
    match library.withoutReplay with
    | some reason =>
      report := { report with lines := report.lines.push s!"{library.name}: not replayed through the kernel: {reason}" }
    | none =>
      let (finding, lines) ← replayLibrary env library arts
      if let some finding := finding then report := { report with findings := report.findings.push finding }
      report := { report with lines := report.lines ++ lines }
  -- the axioms
  let (axioms, users, reached) := dependencies env constants
  report := { report with declarations := constants.size, reached, axioms }
  for axiom_ in axioms do
    if allowedAxioms.contains axiom_ then continue
    for name in (reaching users axiom_).toArray.qsort (·.toString < ·.toString) do
      unless audited.contains name do continue
      let line := if name == axiom_ then
          s!"{name}: is an axiom other than propext, Classical.choice and Quot.sound"
        else s!"{name}: depends on the axiom {axiom_}, which is not propext, Classical.choice or Quot.sound"
      report := report.add name .axiom_ line
  -- the imports of a library proper
  for library in libraries do
    unless library.kind == .library do continue
    for (index, module) in modulesOf env library do
      for imported in env.header.moduleData[index]!.imports do
        let target := imported.module
        if library.contains target then continue
        if testsAndTools.any (·.isPrefixOf target) then
          report := report.add module .importOfTestsOrTools
            s!"{module}: imports {target}, a module of the tests or of the tools"
        else if let some allowed := library.imports then
          unless allowed.any (·.isPrefixOf target) do
            report := report.add module .importOutside
              s!"{module}: imports {target}, which is not of {library.root} or of {", ".intercalate (allowed.toList.map toString)}"
  -- the files of each library: imported by the root of a library proper, in the environment for
  -- a library of tests
  for library in libraries do
    let some directory := library.directory | continue
    let files ← libraryFiles directory library.root
    if files.isEmpty then
      report := report.add library.root .moduleMissing
        s!"{library.root}: no file of the library is under {directory}"
    match library.kind with
    | .library =>
      let imported := importClosure env library.root
      for module in files do
        unless imported.contains module do
          report := report.add module .fileNotImported
            s!"{module}: its file is under {directory} and {library.root} does not import it"
    | .tests =>
      for module in files do
        unless moduleNames.contains module do
          report := report.add module .fileNotLoaded
            s!"{module}: its file is under {directory} and the audit's environment does not have it"
  return report

/-- A control: a module that the audit must refuse, by one rule. -/
structure Control where
  /-- What the control is, in the report. -/
  description : String
  /-- The control, audited as a library. -/
  library : Library
  /-- The rule that must refuse it. -/
  rule : Rule
  /-- Whether a finding by the rule is the one that refuses the control. -/
  isRefusal : Finding → Bool

/-- Whether the audit of the controls refuses a control by its rule. -/
def Control.refusedIn (control : Control) (report : Report) : Bool :=
  report.findings.any fun finding => finding.rule == control.rule && control.isRefusal finding

/-- Why a control is not replayed: it is a control of another rule. -/
def anotherRule : Option String := some "a control of another rule"

/-- The controls, whose files are in the directory of the compiler's package. A control that is
refused by its rule may be refused by others as well. -/
def controls (directory : System.FilePath) : Array Control := #[
  { description := "a theorem proved from an axiom"
    library := { name := "axiom", root := `Zkc.Tools.Audit.Controls.Axiom
                 imports := some coreImports, withoutReplay := anotherRule }
    rule := .axiom_
    -- the module system may keep the theorem under a private name
    isRefusal := fun finding => finding.subject matches .str _ "fromAxiom" },
  { description := "an `@[extern]` definition"
    library := { name := "extern", root := `Zkc.Tools.Audit.Controls.Extern
                 imports := some coreImports, withoutReplay := anotherRule }
    rule := .extern
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.externalAdd },
  { description := "an `@[implemented_by]` definition"
    library := { name := "implemented by", root := `Zkc.Tools.Audit.Controls.ImplementedBy
                 imports := some coreImports, withoutReplay := anotherRule }
    rule := .implementedBy
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.slowSucc },
  { description := "a theorem of `False` that the kernel never checked"
    library := { name := "unchecked", root := `Zkc.Tools.Audit.Controls.Unchecked }
    rule := .kernel
    isRefusal := fun finding =>
      finding.subject == `Zkc.Tools.Audit.Controls.Unchecked &&
        (finding.line.splitOn "'Zkc.Tools.Audit.Controls.unchecked'").length > 1 },
  { description := "an import of a module of the tests"
    library := { name := "import of the tests", root := `Zkc.Tools.Audit.Controls.Import
                 imports := some coreImports, withoutReplay := anotherRule }
    rule := .importOfTestsOrTools
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.Import },
  { description := "an import of Lean under the core's rule"
    library := { name := "import of Lean", root := `Zkc.Tools.Audit.Controls.ImportOutside
                 imports := some coreImports, withoutReplay := anotherRule }
    rule := .importOutside
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.ImportOutside },
  { description := "a file that the root does not import"
    library := { name := "unreached", root := `Zkc.Tools.Audit.Controls.Unreached
                 imports := some coreImports, directory, withoutReplay := anotherRule }
    rule := .fileNotImported
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.Unreached.Apart },
  { description := "a file of a library of tests that the audit does not load"
    library := { name := "unloaded", root := `Zkc.Tools.Audit.Controls.Unreached, kind := .tests
                 directory, withoutReplay := anotherRule }
    rule := .fileNotLoaded
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.Unreached.Apart },
  { description := "a library without a file"
    library := { name := "absent", root := `Zkc.Tools.Audit.Controls.Absent
                 directory, withoutReplay := anotherRule }
    rule := .moduleMissing
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.Absent }]

/-- The built files of the modules under `Zkc` in the entries of a search path, by module. Lean
finds a module by the first entry that has a directory of the module's first component, and
every package of the repository keeps its modules under `Zkc`: so the modules of the packages of
a workspace are given to the import by their files. -/
def zkcArtifacts (searchPath : SearchPath) : IO (NameMap ImportArtifacts) := do
  let mut arts : NameMap ImportArtifacts := {}
  for entry in searchPath do
    let root := entry / "Zkc"
    unless ← root.isDir do continue
    for file in ← root.walkDir do
      unless file.extension == some "olean" do continue
      let relative := (file.withExtension "").toString.drop (entry.toString.length + 1)
      let module := (relative.toString.splitOn "/").foldl Name.mkStr .anonymous
      if arts.contains module then continue
      let mut parts := #[file]
      for level in ["olean.server", "olean.private"] do
        let path := file.withExtension level
        if ← path.pathExists then parts := parts.push path
      let ir := #[file.withExtension "ir.sig", file.withExtension "ir"]
      let irParts := if ← ir.allM (·.pathExists) then ir else #[]
      arts := arts.insert module (.ofArrays #[parts, irParts])
  return arts

/-- The modules that the audit imports for a library: the root of a library proper, and the
modules of the files of a library of tests that are built. -/
def modulesToLoad (library : Library) (arts : NameMap ImportArtifacts) : IO (Array Name) := do
  match library.kind, library.directory with
  | .library, _ => return #[library.root]
  | .tests, some directory => return (← libraryFiles directory library.root).filter arts.contains
  | .tests, none => return #[]

/-- The directory of the package of the running executable, which Lake builds as
`<package>/.lake/build/bin/<name>`. -/
def packageDirectory : IO System.FilePath := do
  let path ← IO.appPath
  match path.parent >>= (·.parent) >>= (·.parent) >>= (·.parent) with
  | some directory =>
    unless ← (directory / "lakefile.toml").pathExists do
      throw (IO.userError s!"{path} is not in the build directory of a package")
    return directory
  | none => throw (IO.userError s!"{path} is not in the build directory of a package")

/-- Audits libraries whose files are in the package of the running executable, and the
controls, whose files are in the compiler's package (`compilerDirectory`, from the directory of
the running executable's package); prints the findings, what was done for each library, the
counts and the controls. The exit code is 0 only when the libraries pass and the audit refuses
every control by its rule. -/
def run (libraries : System.FilePath → Array Library)
    (compilerDirectory : System.FilePath → System.FilePath := id) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let arts ← zkcArtifacts (← searchPathRef.get)
  let directory ← packageDirectory
  let libraries := libraries directory
  let mut modules : Array Import := #[]
  for library in libraries do
    for module in ← modulesToLoad library arts do
      modules := modules.push { module }
  let env ← importModules modules {} (loadExts := false) (level := .private) (arts := arts)
  let report ← audit env libraries arts
  for finding in report.findings do IO.println finding.line
  for line in report.lines do IO.println line
  IO.println s!"{report.declarations} declarations, which reach {report.reached} constants and the axioms {", ".intercalate (report.axioms.toList.map toString)}"
  -- the controls: the environment has the modules of their roots that are built
  let controls := controls (compilerDirectory directory)
  let mut controlModules : Array Import := #[]
  for control in controls do
    let module := control.library.root
    if arts.contains module && !controlModules.any (·.module == module) then
      controlModules := controlModules.push { module }
  let controlEnv ← importModules controlModules {} (loadExts := false) (level := .private) (arts := arts)
  let controlReport ← audit controlEnv (controls.map (·.library)) arts
  let mut refused := 0
  for control in controls do
    let found := control.refusedIn controlReport
    if found then refused := refused + 1
    IO.println s!"control, {control.description}: {if found then "refused" else "NOT refused"} by the rule: {control.rule.describe}"
  IO.println s!"audit: {report.findings.size} findings in {libraries.size} libraries; {refused} of the {controls.size} controls are refused"
  return if report.findings.isEmpty && refused == controls.size then 0 else 1

end Zkc.Tools.Audit
