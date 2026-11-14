import Lean

/-!
# The audit of the libraries

A library is audited in an environment that imports its root module from the built `.olean`
files, at the level that keeps every declaration and every proof, private ones included. For
every constant declared in a module of the library:

- the axioms it depends on are among `propext`, `Classical.choice` and `Quot.sound`; in
  particular no proof uses `sorryAx`. The constants that the audited ones use are visited once
  for the whole run (`dependencies`), and a forbidden axiom is traced back to every audited
  constant that reaches it;
- it carries no `@[extern]` and no `@[implemented_by]`. The executable code that Lean itself
  makes for a `partial` definition is not a finding; the number of `partial` definitions of each
  library (the recursive ones, a `where` helper of one included: Lean compiles a `partial`
  definition that does not recur as an ordinary one) is reported, so that a new one is a
  visible difference.

The rules on imports are read from the headers of the modules: a module of a library imports
only modules of the library itself and of the prefixes that the library allows (`imports`), and
no module of a library imports a module of the tests or of the tools (`Zkc.Tests`, `Zkc.Tools`).
Every `.lean` file under the directory of a library is a module that its root module imports.

`run` audits the libraries, then audits the controls (`Zkc.Tools.Audit.Controls`): a module that
states an axiom and proves a theorem from it, and a module of a library that imports a module of
the tests. The audit must find both. The exit code is 0 only when the libraries pass and the
controls are found; every finding is one line that names the constant or the module and the
rule.
-/

set_option autoImplicit false

namespace Zkc.Tools.Audit

open Lean

/-- A library to audit. -/
structure Library where
  /-- The name of the library in the report. -/
  name : String
  /-- The root module: a module of the library is the root or a module under it. -/
  root : Name
  /-- The prefixes of the modules outside the library that its modules may import; `none` when
  they may import any module that is not of the tests or of the tools. -/
  imports : Option (Array Name)
  /-- The directory that holds the root's file and the directory of its modules, when the files
  are checked against the modules that the root imports. -/
  directory : Option System.FilePath := none

/-- Whether a module is of a library. -/
def Library.contains (library : Library) (module : Name) : Bool :=
  library.root.isPrefixOf module

/-- The prefixes of the modules that no module of a library imports: the tests and the tools. -/
def testsAndTools : Array Name := #[`Zkc.Tests, `Zkc.Tools]

/-- The axioms that a constant of a library may depend on. -/
def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- The kinds of finding. -/
inductive Rule where
  | axiom_
  | extern
  | implementedBy
  | importOfTestsOrTools
  | importOutside
  | fileNotImported
  | moduleMissing
  deriving BEq, Inhabited

/-- One finding: the constant or the module it is about, its rule, and the line it prints. -/
structure Finding where
  subject : Name
  rule : Rule
  line : String
  deriving Inhabited

/-- What an audit found, and the number of `partial` definitions of each library. -/
structure Report where
  findings : Array Finding := #[]
  partials : Array (String × Nat) := #[]
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

/-- The modules of an environment that are of a library, each with its index. -/
def modulesOf (env : Environment) (library : Library) : Array (Nat × Name) :=
  (env.header.moduleNames.zipIdx.filter fun (module, _) => library.contains module).map
    fun (module, index) => (index, module)

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

/-- The audit of libraries in an environment that imports them. -/
def audit (env : Environment) (libraries : Array Library) : IO Report := do
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
    report := { report with partials := report.partials.push (library.name, partials) }
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
  -- the imports
  for library in libraries do
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
  -- the files of each library against the modules that its root imports
  for library in libraries do
    let some directory := library.directory | continue
    let rootFile := (library.root.components.foldl (fun path part => path / part.toString) directory).addExtension "lean"
    let rootDirectory := rootFile.withExtension ""
    let mut files := #[]
    if ← rootFile.pathExists then files := files.push library.root
    if ← rootDirectory.isDir then files := files ++ (← leanFiles directory rootDirectory)
    if files.isEmpty then
      report := report.add library.root .moduleMissing
        s!"{library.root}: no file of the library is under {directory}"
    for module in files do
      unless moduleNames.contains module do
        report := report.add module .fileNotImported
          s!"{module}: its file is under {directory} and {library.root} does not import it"
  return report

/-- The library of the controls: modules that the audit must refuse. -/
def controls : Library :=
  { name := "controls", root := `Zkc.Tools.Audit.Controls, imports := some #[`Init] }

/-- The modules of the controls. -/
def controlModules : Array Name :=
  #[`Zkc.Tools.Audit.Controls.Axiom, `Zkc.Tools.Audit.Controls.Import]

/-- Whether a name is the theorem of the control of axioms, which the module system may keep under
a private name. -/
def isControlTheorem : Name → Bool
  | .str _ "fromAxiom" => true
  | _ => false

/-- The findings that the audit of the controls must make: the theorem proved from an axiom, which
is private to its module, and the import of a module of the tests. -/
def controlCaught (report : Report) : Array (String × Bool) :=
  #[("the theorem proved from an axiom", report.findings.any fun finding =>
      finding.rule == .axiom_ && isControlTheorem finding.subject),
    ("the import of a module of the tests", report.findings.any fun finding =>
      finding.rule == .importOfTestsOrTools && finding.subject == `Zkc.Tools.Audit.Controls.Import)]

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
controls; prints the findings, the counts and the controls. The exit code is 0 only when the
libraries pass and the audit refuses both controls. -/
def run (libraries : System.FilePath → Array Library) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let arts ← zkcArtifacts (← searchPathRef.get)
  let directory ← packageDirectory
  let libraries := libraries directory
  let env ← importModules (libraries.map fun library => { module := library.root }) {}
    (loadExts := false) (level := .private) (arts := arts)
  let report ← audit env libraries
  for finding in report.findings do IO.println finding.line
  for (name, count) in report.partials do IO.println s!"{name}: {count} partial definitions"
  IO.println s!"{report.declarations} declarations, which reach {report.reached} constants and the axioms {", ".intercalate (report.axioms.toList.map toString)}"
  let controlEnv ← importModules (controlModules.map fun module => { module }) {}
    (loadExts := false) (level := .private) (arts := arts)
  let controlReport ← audit controlEnv #[controls]
  let caught := controlCaught controlReport
  for (what, found) in caught do
    IO.println s!"control, {what}: {if found then "refused" else "NOT refused"}"
  let passed := report.findings.isEmpty && caught.all (·.2)
  IO.println s!"audit: {report.findings.size} findings in {libraries.size} libraries; the controls are {if caught.all (·.2) then "refused" else "NOT refused"}"
  return if passed then 0 else 1

end Zkc.Tools.Audit
