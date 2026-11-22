import Zkc.Tools.Audit.CompilerHelpers

/-!
# The audit of the libraries

A library is audited in an environment that imports it from the built `.olean` files, at the
level that keeps every declaration and every proof, private ones included. A library proper is
imported by its root module. A library of tests has no module that imports all of its modules:
it is imported by the modules of its files that are built. For every constant declared in a
module of a library:

- the axioms it depends on are permitted by the policy of its package; in
  particular no proof uses `sorryAx`. The constants that the audited ones use are visited once
  for the whole run (`dependencies`), and a forbidden axiom is traced back to every audited
  constant that reaches it;
- it carries no `@[extern]` or arbitrary `@[implemented_by]`. Lean's recursive implementations
  retain their existing exception. Constructor-index native implementations are recognized by
  their complete logical and native bodies (`CompilerHelpers`), not their names alone. The
  numbers of recursive implementations and recognized constructor indices are reported for each
  library, separately from `partial` definitions (the recursive ones, including `where` helpers).
  Their execution relies on the pinned compiler/runtime; kernel replay checks the logical
  definitions, not the native code;
- the kernel accepts it (`replay`). Reading a constant from a built file says nothing of
  whether the kernel checked it: a theorem elaborated under `set_option debug.skipKernelTC` is
  stored with whatever proof the elaborator built. So the declarations of the libraries are
  replayed through the kernel (`Lean.Kernel.Environment.replay`), module after module in the
  order of their imports, together with every module that they import, directly or not, that is
  not of Lean's libraries (`leanLibraries`): the replay starts from an environment that imports
  only modules of Lean's libraries, so that a library is checked relative to Lean's libraries
  alone, and a tool that a library of tests imports is replayed with it. The kernel does
  not check unsafe declarations, and the replay skips them and the code of `partial`
  definitions, as Lean's own replay does. A library can be left out of the replay, with the
  reason (`Library.withoutReplay`), as the controls below are; a replayed module that imports a
  module of a library left out is a finding.

The rules on imports hold for a library proper and are read from the headers of the modules: a
module of the library imports only modules of the library itself and of the prefixes that the
library allows (`imports`), and no module of the library imports a module of the tests or of the
tools (the prefixes that the policy names: `Zkc.Tests` and `Zkc.Tools`, and those of the
policy's own package). Every `.lean` file under the directory of a library proper is a
module that its root module imports, directly or not. Every `.lean` file under the directory of
a library of tests is a module of the environment that the audit loads, so that no file of the
tests is left unbuilt and unaudited.

The rule of layers holds for a library that lists its modules for any dialect (`generic`) and
its modules about one dialect or about the vocabulary (`concrete`): a module for any dialect
imports no module about one dialect or about the vocabulary, directly or through other modules.
A violation is found with the shortest path of imports from the module to one such module; a
module that the lists name and the audit's environment does not have is a finding too, and so is
a module that both lists name. The core
gives the two lists of the audit (`coreGeneric`, `coreConcrete`).

`run` audits the libraries, accepts the generated-helper fixture, then checks the negative
controls (`controls`): modules under `Zkc.Tools.Audit.Controls` that the audit must refuse,
each audited alone and by one rule. The exit code is 0 only when the libraries and generated
fixture pass and every negative control is refused by its rule; every finding is one line that
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
  not. A replayed module that imports a module of the library is then a finding. -/
  withoutReplay : Option String := none
  /-- The modules for any dialect, which the rule of layers holds of. -/
  generic : Array Name := #[]
  /-- The modules about one dialect or about the vocabulary, which no module for any dialect
  imports, directly or not. -/
  concrete : Array Name := #[]

/-- Whether a module is of a library. -/
def Library.contains (library : Library) (module : Name) : Bool :=
  library.root.isPrefixOf module

/-- What the modules under a prefix are. -/
inductive Part where
  | library
  | tests
  | tools
  deriving DecidableEq

/-- The prefixes of the modules of the compiler package, each with what its modules are. -/
def compilerParts : Array (Name × Part) :=
  #[(`Zkc.Tests, .tests), (`Zkc.Tools, .tools), (`Zkc, .library)]

/-- The prefixes outside the core that a module of the core may import: Lean's prelude and its
standard library. -/
def coreImports : Array Name := #[`Init, `Std]

/-- The prefixes outside the vocabulary that a module of the vocabulary may import: those of the
core, and the core. -/
def vocabularyImports : Array Name := coreImports.push `Zkc.Core

/-- The modules of the core for any dialect: every declaration of each is for any dialect and
any semantics, and none imports, directly or not, a module of `coreConcrete`. They are the
processes, the program for any dialect (names, contexts, terms and the term in steps, the program
by names for any operations, refusals, elaboration, erasure and places), the meanings for any
dialect (the fold, the term in steps, requirements, places and the validity of values), the
evidence layer, the value form, and the analysis with its soundness (the count of every loop that
a run reaches, of the term and of the term in steps, included). Every module of the core whose
declarations are for any dialect is listed: none is left out. -/
def coreGeneric : Array Name := #[
  `Zkc.Core.Evidence.Claim, `Zkc.Core.Evidence.Relation,
  `Zkc.Core.Evidence.Stepped, `Zkc.Core.Evidence.Subject,
  `Zkc.Core.Evidence.Summary, `Zkc.Core.Facts.Body.AnalysisSound,
  `Zkc.Core.Facts.Body.AttemptSound, `Zkc.Core.Facts.Body.BlockSound,
  `Zkc.Core.Facts.Body.BoundsOwnership, `Zkc.Core.Facts.Body.CasesSound,
  `Zkc.Core.Facts.Body.ChooseSound, `Zkc.Core.Facts.Body.ComparisonSound,
  `Zkc.Core.Facts.Body.EnteringSound, `Zkc.Core.Facts.Body.GuardSound,
  `Zkc.Core.Facts.Body.InvariantsSound, `Zkc.Core.Facts.Body.LoopSound,
  `Zkc.Core.Facts.Body.OperationSound, `Zkc.Core.Facts.Body.Skeleton,
  `Zkc.Core.Facts.Body.SkeletonLaws, `Zkc.Core.Facts.Body.Statements,
  `Zkc.Core.Facts.Body.StepSound, `Zkc.Core.Facts.Body.Traversal,
  `Zkc.Core.Facts.Body.ValueLaws, `Zkc.Core.Facts.Body.Verdicts,
  `Zkc.Core.Facts.Body.Walk, `Zkc.Core.Facts.Body.WalkSound,
  `Zkc.Core.Facts.Contracts.AnnotationLaws, `Zkc.Core.Facts.Contracts.Annotations,
  `Zkc.Core.Facts.Contracts.Elaboration, `Zkc.Core.Facts.Contracts.Expressions,
  `Zkc.Core.Facts.Contracts.TypeLaws, `Zkc.Core.Facts.Contracts.Typing,
  `Zkc.Core.Facts.Domains.Interface, `Zkc.Core.Facts.Domains.Product,
  `Zkc.Core.Facts.Domains.Rules, `Zkc.Core.Facts.Knowledge.BufferedFacts,
  `Zkc.Core.Facts.Knowledge.BufferedFactsLaws, `Zkc.Core.Facts.Knowledge.Carried,
  `Zkc.Core.Facts.Knowledge.Decisions, `Zkc.Core.Facts.Knowledge.Forms,
  `Zkc.Core.Facts.Knowledge.Inference, `Zkc.Core.Facts.Knowledge.Join,
  `Zkc.Core.Facts.Knowledge.Known, `Zkc.Core.Facts.Knowledge.KnownLaws,
  `Zkc.Core.Facts.Knowledge.Learning, `Zkc.Core.Facts.Knowledge.Loop,
  `Zkc.Core.Facts.Knowledge.Meaning, `Zkc.Core.Facts.Knowledge.Offsets,
  `Zkc.Core.Facts.Knowledge.Soundness, `Zkc.Core.Facts.Knowledge.Transfer,
  `Zkc.Core.Facts.Loops, `Zkc.Core.Facts.OpFacts,
  `Zkc.Core.Facts.Range, `Zkc.Core.Facts.SteppedLoops,
  `Zkc.Core.Meaning.Fold, `Zkc.Core.Meaning.Place,
  `Zkc.Core.Meaning.Requirement, `Zkc.Core.Meaning.Stepped,
  `Zkc.Core.Meaning.ValidValues, `Zkc.Core.Process.Handler,
  `Zkc.Core.Process.Process, `Zkc.Core.Process.Same,
  `Zkc.Core.Program.Annotations, `Zkc.Core.Program.BitTree,
  `Zkc.Core.Program.Conditions,
  `Zkc.Core.Program.Context, `Zkc.Core.Program.Elaborate,
  `Zkc.Core.Program.Erase, `Zkc.Core.Program.Identity,
  `Zkc.Core.Program.Library, `Zkc.Core.Program.Linear,
  `Zkc.Core.Program.Lists, `Zkc.Core.Program.Place,
  `Zkc.Core.Program.Refusal, `Zkc.Core.Program.Requirement,
  `Zkc.Core.Program.Stepped, `Zkc.Core.Program.Syntax,
  `Zkc.Core.Program.Term, `Zkc.Core.Value.Expressions]

/-- The modules of the core about one dialect or about the vocabulary from which the others
follow: the vocabulary, the types and records over it, the operations of the three dialects by
names and the program by names of them, the dialects, the rules of the function dialect and
projection, the events and the semantics of the three dialects, what the function dialect tells
the analysis, and the declaration of a scheme, which deploys a protocol. Every other module of
the core about one dialect or about the vocabulary imports one of them, directly or not, so that
the rule of layers reaches it. -/
def coreConcrete : Array Name := #[
  `Zkc.Core.Program.Vocabulary, `Zkc.Core.Program.Located, `Zkc.Core.Program.Record,
  `Zkc.Core.Program.Shape, `Zkc.Core.Program.NamedProgram, `Zkc.Core.Program.Dialects,
  `Zkc.Core.Program.LocalRules, `Zkc.Core.Program.Project,
  `Zkc.Core.Meaning.Events, `Zkc.Core.Meaning.Local, `Zkc.Core.Meaning.Protocol,
  `Zkc.Core.Meaning.Role,
  `Zkc.Core.Facts.Local,
  `Zkc.Core.Scheme.Declaration]

/-- The first components of the modules of Lean's own libraries: the only modules that the replay
through the kernel takes as built. -/
def leanLibraries : Array Name := #[`Init, `Std, `Lean, `Lake]

/-- Whether a module is of Lean's own libraries. -/
def isOfLean (module : Name) : Bool :=
  leanLibraries.contains module.getRoot

/-- The axioms that a constant of a library may depend on. -/
def allowedAxioms : Array Name := #[``propext, ``Quot.sound]

/-- A package may import pinned libraries as prebuilt dependencies of kernel replay.
Their constants still participate in the transitive axiom audit. -/
structure Policy where
  axioms : Array Name := allowedAxioms
  packages : Array Name := #[]
  /-- The prefixes of the modules of the repository's packages that an audit under this policy
  can meet, each with what its modules are. The two rules below read this one table. -/
  parts : Array (Name × Part) := compilerParts

/-- The roots of the repository's modules. A library taken as built imports no module under
them. -/
def Policy.project (policy : Policy) : Array Name :=
  policy.parts.foldl (init := #[]) fun roots (under, _) =>
    if roots.contains under.getRoot then roots else roots.push under.getRoot

/-- The prefixes of the modules of tests and of tools, which no module of a library imports. -/
def Policy.testsAndTools (policy : Policy) : Array Name :=
  (policy.parts.filter (·.2 != .library)).map (·.1)

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
  | layers
  deriving BEq, Inhabited

/-- What a rule requires, as a phrase. -/
def Rule.describe : Rule → String
  | .axiom_ => "no axiom outside the package policy"
  | .extern => "no `@[extern]`"
  | .implementedBy => "no unrecognized `@[implemented_by]`"
  | .kernel => "the kernel accepts every declaration when it is replayed"
  | .importOfTestsOrTools => "no import of a module of the tests or of the tools"
  | .importOutside => "imports only of the library and of the prefixes that it allows"
  | .fileNotImported => "every file of a library is imported by its root"
  | .fileNotLoaded => "every file of a library of tests is in the audit's environment"
  | .moduleMissing => "a library has a file"
  | .layers =>
    "a module for any dialect imports, directly or not, no module about one dialect or about the vocabulary"

/-- One finding: the constant or the module it is about, its rule, and the line it prints. -/
structure Finding where
  subject : Name
  rule : Rule
  line : String
  deriving Inhabited

/-- What an audit found, and what it did for each library. -/
structure Report where
  findings : Array Finding := #[]
  /-- For each library: its partial definitions, native implementation categories, what was
  replayed through the kernel and what was taken as built. -/
  lines : Array String := #[]
  /-- The constants declared in the audited modules, and the constants that they reach. -/
  declarations : Nat := 0
  /-- Structurally recognized constructor-index native replacements, counted separately from
  recursive implementations. These rely on the pinned compiler/runtime for execution. -/
  constructorIndices : Nat := 0
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

/-- The modules that some modules import, directly or not, and the modules themselves. -/
def importClosure (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let indices : Std.HashMap Name Nat := env.header.moduleNames.zipIdx.foldl
    (fun indices (module, index) => indices.insert module index) {}
  let mut found : NameSet := roots.foldl (·.insert ·) {}
  let mut stack := roots
  while true do
    let some module := stack.back? | break
    stack := stack.pop
    let some index := indices[module]? | continue
    for imported in env.header.moduleData[index]!.imports do
      unless found.contains imported.module do
        found := found.insert imported.module
        stack := stack.push imported.module
  return found

/-- A shortest path of imports from a module to one of some modules, the module first and the one
that it reaches last, when it imports one of them, directly or not. -/
def importPath (env : Environment) (start : Name) (targets : Array Name) :
    Option (Array Name) := Id.run do
  let indices : Std.HashMap Name Nat := env.header.moduleNames.zipIdx.foldl
    (fun indices (module, index) => indices.insert module index) {}
  -- each module reached, with the module that imports it on a shortest path
  let mut reachedFrom : Std.HashMap Name Name := {}
  let mut queue := #[start]
  let mut position := 0
  while position < queue.size do
    let module := queue[position]!
    position := position + 1
    let some index := indices[module]? | continue
    for imported in env.header.moduleData[index]!.imports do
      let target := imported.module
      if target == start || reachedFrom.contains target then continue
      reachedFrom := reachedFrom.insert target module
      if targets.contains target then
        let mut path := #[target]
        let mut current := target
        while current != start do
          let some importer := reachedFrom[current]? | break
          path := path.push importer
          current := importer
        return some path.reverse
      queue := queue.push target
  return none

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

/-- The replay through the kernel of the declarations of the libraries that are not left out of
it, together with every module that they import, directly or not, that is not of Lean's
libraries: module after module, in the order of the environment, on an environment that imports
only the modules of Lean's libraries that the replayed modules import. A module of a library left
out of the replay is not replayed, and a replayed module that imports one is a finding, after
which nothing is replayed: the environment of the replay would hold what that module imports.
Returns the finding of the first module whose declarations the kernel refuses, after which the
replay stops, and what was replayed and what was taken as built, as lines. -/
def replay (env : Environment) (libraries : Array Library)
    (packages project : Array Name) :
    IO (Option Finding × Array String) := do
  let replayed := libraries.filter (·.withoutReplay.isNone)
  if replayed.isEmpty then return (none, #[])
  let leftOut (module : Name) : Option Library :=
    libraries.find? fun library => library.withoutReplay.isSome && library.contains module
  let moduleNames := env.header.moduleNames
  let closure := importClosure env
    (moduleNames.filter fun module => replayed.any (·.contains module))
  let packageImports := moduleNames.filter fun m => closure.contains m && packages.contains m.getRoot
  let upstream := if packageImports.isEmpty then ({} : NameSet) else importClosure env packageImports
  -- Importing even one pinned module loads its entire dependency graph into the
  -- starting kernel environment. Reject a back edge before importing that base.
  if let some localModule := moduleNames.find? (fun m =>
      upstream.contains m && (project.contains m.getRoot || libraries.any (·.contains m))) then
    return (some { subject := localModule, rule := .kernel,
                   line := s!"a prebuilt library imports project module {localModule}" }, #[])
  let built (m : Name) := isOfLean m || upstream.contains m
  let modules := (moduleNames.zipIdx.filter fun (module, _) =>
      closure.contains module && !built module && (leftOut module).isNone).map
    fun (module, index) => (index, module)
  let mut base : Array Name := #[]
  for (index, module) in modules do
    for imported in env.header.moduleData[index]!.imports do
      let target := imported.module
      if let some library := leftOut target then
        return (some { subject := module, rule := .kernel
                       line := s!"{module}: imports {target}, of {library.root}, which is not replayed through the kernel, so no declaration is replayed" },
          #["the replay through the kernel did not start"])
      if built target && !base.contains target then base := base.push target
  let start ← IO.monoMsNow
  let environment ← importModules (base.map fun module => { module }) {} (loadExts := false)
    (level := .private)
  let mut kernel := environment.toKernelEnv
  -- the declarations and the modules replayed: of each library, and of each prefix of the modules
  -- that the libraries import
  let mut groups : Array (String × Nat × Nat) := replayed.map (·.name, 0, 0)
  let mut skipped := 0
  for (index, module) in modules do
    let data := env.header.moduleData[index]!
    let mut constants : Std.HashMap Name ConstantInfo := {}
    let mut checked := 0
    for name in data.constNames, info in data.constants do
      constants := constants.insert name info
      if info.isUnsafe || info.isPartial then skipped := skipped + 1 else checked := checked + 1
    try
      kernel ← kernel.replay constants
    catch error =>
      let message := (toString error).replace "\n" " "
      return (some { subject := module, rule := .kernel
                     line := s!"{module}: the kernel refuses a declaration when it is replayed: {message}; the modules after it are not replayed" },
        #[s!"the replay through the kernel stopped at {module}"])
    let group := match replayed.find? (·.contains module) with
      | some library => library.name
      | none => s!"the modules under {module.getPrefix} that they import"
    groups := match groups.findIdx? (·.1 == group) with
      | some position => groups.modify position fun (label, declarations, count) =>
        (label, declarations + checked, count + 1)
      | none => groups.push (group, checked, 1)
  let fromLean := environment.header.moduleNames.foldl (init := #[]) fun roots module =>
    if roots.contains module.getRoot then roots else roots.push module.getRoot
  let counts := groups.map fun (label, declarations, count) =>
    s!"  {label}: {declarations} declarations of {count} module{if count == 1 then "" else "s"}"
  return (none,
    #[s!"replayed through the kernel, module after module in the order of their imports, in {seconds ((← IO.monoMsNow) - start)}:"] ++
    counts ++
    #[s!"  not replayed: {skipped} unsafe declarations and code of `partial` definitions, which the kernel does not check",
      s!"  taken as built: libraries {", ".intercalate (fromLean.toList.map toString)}"])

/-- The audit of libraries in an environment that imports them. -/
def audit (env : Environment) (libraries : Array Library) (policy : Policy := {}) :
    IO Report := do
  let mut report : Report := {}
  let moduleNames := env.header.moduleNames
  -- the constants of the audited modules, and their libraries
  let mut audited : Std.HashSet Name := {}
  let mut constants : Array Name := #[]
  for library in libraries do
    let mut partials := 0
    let mut recursiveImplementations := 0
    let mut constructorIndices := 0
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
          -- Preserve Lean's recursive implementation policy, and recognize the new generated
          -- constructor indices by both bodies rather than by their names alone.
          if implementation == Compiler.mkUnsafeRecName name then
            recursiveImplementations := recursiveImplementations + 1
          else if ← isConstructorIndexImplementation env name implementation then
            constructorIndices := constructorIndices + 1
          else
            report := report.add name .implementedBy
              s!"{name}: carries `@[implemented_by {implementation}]`"
    report := { report with
      constructorIndices := report.constructorIndices + constructorIndices
      lines := report.lines.push s!"{library.name}: {partials} partial definitions; {recursiveImplementations} recursive native implementations; {constructorIndices} recognized constructor-index native implementations" }
    if let some reason := library.withoutReplay then
      report := { report with lines := report.lines.push s!"{library.name}: not replayed through the kernel: {reason}" }
  -- the kernel
  let (finding, lines) ← replay env libraries policy.packages policy.project
  if let some finding := finding then report := { report with findings := report.findings.push finding }
  report := { report with lines := report.lines ++ lines }
  -- the axioms
  let (axioms, users, reached) := dependencies env constants
  report := { report with declarations := constants.size, reached, axioms }
  for axiom_ in axioms do
    if policy.axioms.contains axiom_ then continue
    for name in (reaching users axiom_).toArray.qsort (·.toString < ·.toString) do
      unless audited.contains name do continue
      let line := if name == axiom_ then
          s!"{name}: is outside the package axiom policy"
        else s!"{name}: depends on the axiom {axiom_}, which is outside the package policy"
      report := report.add name .axiom_ line
  -- the imports of a library proper
  for library in libraries do
    unless library.kind == .library do continue
    for (index, module) in modulesOf env library do
      for imported in env.header.moduleData[index]!.imports do
        let target := imported.module
        if library.contains target then continue
        if policy.testsAndTools.any (·.isPrefixOf target) then
          report := report.add module .importOfTestsOrTools
            s!"{module}: imports {target}, a module of the tests or of the tools"
        else if let some allowed := library.imports then
          unless allowed.any (·.isPrefixOf target) do
            report := report.add module .importOutside
              s!"{module}: imports {target}, which is not of {library.root} or of {", ".intercalate (allowed.toList.map toString)}"
  -- the layers: no module for any dialect imports, directly or not, a module about one dialect or
  -- about the vocabulary; every module of the lists is in the environment, and in one list only
  for library in libraries do
    for (kind, listed) in #[("for any dialect", library.generic),
        ("about one dialect or about the vocabulary", library.concrete)] do
      for module in listed do
        unless moduleNames.contains module do
          report := report.add module .layers
            s!"{module}: the rule of layers lists it as a module {kind}, and the audit's environment does not have it"
    for module in library.generic do
      if library.concrete.contains module then
        report := report.add module .layers
          s!"{module}: the rule of layers lists it both as a module for any dialect and as a module about one dialect or about the vocabulary"
        continue
      let some path := importPath env module library.concrete | continue
      report := report.add module .layers
        s!"{module}: a module for any dialect, imports {path.back!}, a module about one dialect or about the vocabulary, by {" → ".intercalate (path.toList.map toString)}"
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
      let imported := importClosure env #[library.root]
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

/-- Whether a finding is the kernel's refusal of the theorem of `False` that it never checked
(`Controls/Unchecked.lean`). -/
def refusesUnchecked (finding : Finding) : Bool :=
  finding.subject == `Zkc.Tools.Audit.Controls.Unchecked &&
    (finding.line.splitOn "'Zkc.Tools.Audit.Controls.unchecked'").length > 1

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
  { description := "a private `@[extern]` definition"
    library := { name := "private extern", root := `Zkc.Tools.Audit.Controls.Extern
                 imports := some coreImports, withoutReplay := anotherRule }
    rule := .extern
    isRefusal := fun finding => finding.subject matches .str _ "privateExternalAdd" },
  { description := "a private `@[implemented_by]` definition"
    library := { name := "private implemented by", root := `Zkc.Tools.Audit.Controls.ImplementedBy
                 imports := some coreImports, withoutReplay := anotherRule }
    rule := .implementedBy
    isRefusal := fun finding => finding.subject matches .str _ "privateSlowSucc" },
  { description := "a counterfeit constructor index: WrongLogic"
    library := { name := "counterfeit constructor index", root := `Zkc.Tools.Audit.Controls.ConstructorIndex
                 imports := some coreImports, withoutReplay := anotherRule }
    rule := .implementedBy
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.WrongLogic.ctorIdx },
  { description := "a counterfeit constructor index: WrongNative"
    library := { name := "counterfeit constructor index", root := `Zkc.Tools.Audit.Controls.ConstructorIndex
                 imports := some coreImports, withoutReplay := anotherRule }
    rule := .implementedBy
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.WrongNative.ctorIdx },
  { description := "a counterfeit constructor index: WrongTarget"
    library := { name := "counterfeit constructor index", root := `Zkc.Tools.Audit.Controls.ConstructorIndex
                 imports := some coreImports, withoutReplay := anotherRule }
    rule := .implementedBy
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.WrongTarget.ctorIdx },
  { description := "a theorem of `False` that the kernel never checked"
    library := { name := "unchecked", root := `Zkc.Tools.Audit.Controls.Unchecked }
    rule := .kernel
    isRefusal := refusesUnchecked },
  { description := "a theorem that uses a theorem of another module that the kernel never checked"
    -- a library of tests, whose imports are not ruled: it imports the control above
    library := { name := "uses unchecked", root := `Zkc.Tools.Audit.Controls.UsesUnchecked
                 kind := .tests }
    rule := .kernel
    -- its replay goes through the module that it imports
    isRefusal := refusesUnchecked },
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
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.Absent },
  { description := "a module for any dialect that imports the vocabulary through another module"
    library := { name := "layers", root := `Zkc.Tools.Audit.Controls.Layers
                 generic := #[`Zkc.Tools.Audit.Controls.Layers]
                 concrete := #[`Zkc.Core.Program.Vocabulary], withoutReplay := anotherRule }
    rule := .layers
    -- the path of imports goes through the module that the control imports
    isRefusal := fun finding => finding.subject == `Zkc.Tools.Audit.Controls.Layers &&
      (finding.line.splitOn "Zkc.Core.Program.Located").length > 1 }]

/-- Whether a module is built: the search path has its object. A module root belongs to one
package of the repository, so Lean finds every module of a workspace by its name. -/
def built (module : Name) : IO Bool := do
  -- the search path gives where the object of a module would be, whether or not it is there
  match ← (← searchPathRef.get).findWithExt "olean" module with
  | some file => file.pathExists
  | none => return false

/-- The modules that the audit imports for a library: the root of a library proper, and the
modules of the files of a library of tests that are built. -/
def modulesToLoad (library : Library) : IO (Array Name) := do
  match library.kind, library.directory with
  | .library, _ => return #[library.root]
  | .tests, some directory => (← libraryFiles directory library.root).filterM built
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
counts and the controls. The exit code is 0 only when the libraries and generated-helper
fixture pass and the audit refuses every negative control by its rule. -/
def run (libraries : System.FilePath → Array Library)
    (compilerDirectory : System.FilePath → System.FilePath := id) (policy : Policy := {}) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let directory ← packageDirectory
  let libraries := libraries directory
  let mut modules : Array Import := #[]
  for library in libraries do
    for module in ← modulesToLoad library do
      modules := modules.push { module }
  let env ← importModules modules {} (loadExts := false) (level := .private)
  let report ← audit env libraries policy
  for finding in report.findings do IO.println finding.line
  for line in report.lines do IO.println line
  IO.println s!"{report.declarations} declarations, which reach {report.reached} constants and the axioms {", ".intercalate (report.axioms.toList.map toString)}"
  -- the controls: the environment has the modules of their roots that are built
  let controls := controls (compilerDirectory directory)
  let mut controlModules : Array Import := #[]
  for control in controls do
    let module := control.library.root
    if (← built module) && !controlModules.any (·.module == module) then
      controlModules := controlModules.push { module }
  controlModules := controlModules.push { module := `Zkc.Tools.Audit.Controls.Generated }
  let controlEnv ← importModules controlModules {} (loadExts := false) (level := .private)
  let generated ← audit controlEnv #[{
    name := "generated helpers", root := `Zkc.Tools.Audit.Controls.Generated,
    imports := some coreImports }]
  let generatedAccepted := generated.findings.isEmpty && generated.constructorIndices == 8
  IO.println s!"control, generated helpers (public, private, empty, indexed, mutual, nested, polymorphic): {if generatedAccepted then "accepted" else "NOT accepted"}; {generated.constructorIndices} recognized constructor indices"
  for finding in generated.findings do IO.println finding.line
  let mut refused := 0
  for control in controls do
    -- each control is audited alone, so that only its own findings refuse it
    let found := control.refusedIn (← audit controlEnv #[control.library] policy)
    if found then refused := refused + 1
    IO.println s!"control, {control.description}: {if found then "refused" else "NOT refused"} by the rule: {control.rule.describe}"
  IO.println s!"audit: {report.findings.size} findings in {libraries.size} libraries; {refused} of the {controls.size} controls are refused"
  return if report.findings.isEmpty && generatedAccepted && refused == controls.size then 0 else 1

end Zkc.Tools.Audit
