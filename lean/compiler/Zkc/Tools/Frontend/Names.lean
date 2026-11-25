import Zkc.Frontend
import Zkc.Tools.Frontend.Bench

/-!
# The commands of `zkc-check`

`names` resolves the files and their imports. `resolutions` lists the resolved paths,
`instances` reports instantiated declarations, and `types` checks bodies and emits packages.
`bench` measures those compiler phases. Library directories are searched in command-line order.
-/

namespace Zkc.Tools.Frontend.Names

open Zkc.Frontend
open Zkc.Frontend.Syntax

/-- Reads and parses one source file. -/
def readInput (path : String) : IO SourceInput := do
  let source ← IO.FS.readBinFile path
  return { name := path, parsed := parse path source }

/-- The loader of library modules: the first directory that has the file of the path. -/
def libraryLoader (directories : Array System.FilePath) (names : Array String) :
    IO (Option SourceInput) := do
  for directory in directories do
    let file := (names.foldl (· / ·) directory).addExtension "zkc"
    if ← file.pathExists then
      return some (← readInput file.toString)
  return none

structure Options where
  libraries : Array System.FilePath := #[]
  goals : Array String := #[]
  output : Option System.FilePath := none
  repetitions : Nat := 5
  files : Array String := #[]
  /-- `instances` prints every instance with what it holds. -/
  contents : Bool := false

/-- `[--library <dir>]… [--repeat <n>] <files>…` -/
def readOptions : List String → Options → Except String Options
  | "--library" :: directory :: rest, options =>
    readOptions rest { options with libraries := options.libraries.push directory }
  | "--goal" :: goal :: rest, options =>
    if goal.startsWith "--" then .error "--goal requires a selector"
    else readOptions rest { options with goals := options.goals.push goal }
  | "--output" :: directory :: rest, options =>
    if options.output.isSome || directory.startsWith "--" then .error "--output requires one directory"
    else readOptions rest { options with output := some directory }
  | "--contents" :: rest, options => readOptions rest { options with contents := true }
  | "--repeat" :: count :: rest, options =>
    match count.toNat? with
    | some n => readOptions rest { options with repetitions := n }
    | none => .error s!"--repeat takes a number, not `{count}`"
  | file :: rest, options =>
    if file.startsWith "--" then .error s!"unknown option `{file}`"
    else readOptions rest { options with files := options.files.push file }
  | [], options => .ok options

/-- The counts that `names` prints for a program it accepts. -/
def summary (check : NameCheck) (givenCount : Nat) : String :=
  let program := check.program
  let library := (program.files.filter (·.fromLibrary)).size
  s!"accept: {program.files.size} files ({givenCount} given, {library} from the library), {program.declarations.size} declarations, {program.imports.size} imports, {check.resolutions.size} resolved paths"

/-- `names [--library <dir>]… <files>…`: the refusals, one per line, or the summary. The exit
code is 1 when a name is refused. -/
def names (options : Options) : IO UInt32 := do
  let inputs ← options.files.mapM readInput
  let check ← checkNames inputs (libraryLoader options.libraries)
  if check.refusals.isEmpty then
    IO.println (summary check inputs.size)
    return 0
  for refusal in check.refusals do
    IO.println s!"{refusal.span.file}: {refusal.render}"
  return 1

/-- The line and column of a byte of a source, the column in characters. -/
def place (source : ByteArray) (byte : Nat) : Nat × Nat := Id.run do
  let mut line := 1
  let mut column := 1
  for index in [0:min byte source.size] do
    let b := source[index]!
    if b == 10 then
      line := line + 1
      column := 1
    else if b &&& 0xC0 != 0x80 then column := column + 1
  return (line, column)

/-- The names and `::` that start at a byte: the text of a path without its static arguments. -/
def pathTextAt (source : ByteArray) (byte : Nat) : String := Id.run do
  let mut bytes := ByteArray.empty
  for index in [byte:source.size] do
    let b := source[index]!
    let isName := (b >= 48 && b <= 57) || (b >= 65 && b <= 90) || (b >= 97 && b <= 122) ||
      b == 95 || b == 58 || b >= 0x80
    if !isName then break
    bytes := bytes.push b
  return (String.fromUTF8? bytes).getD "?"

/-- The checks left incomplete, one per line with their chains: a budget of the compiler ran out
in each. -/
def printIncomplete (incomplete : Array Diagnostic) : IO Unit :=
  for diagnostic in incomplete do
    IO.println s!"{diagnostic.span.file}: {diagnostic.render Renderer.plain}"

/-- The first word of a summary: `refuse` when something is refused, `incomplete` when nothing
is and a check is incomplete (a budget of the compiler ran out: SP10), `accept` otherwise. -/
def verdict (refused : Bool) (incomplete : Array Diagnostic) : String :=
  if refused then "refuse" else if incomplete.isEmpty then "accept" else "incomplete"

/-- The exit code of a verdict: 0 to accept, 1 to refuse, 3 for an incomplete check. -/
def exitCode (refused : Bool) (incomplete : Array Diagnostic) : UInt32 :=
  if refused then 1 else if incomplete.isEmpty then 0 else 3

/-- `resolutions [--library <dir>]… <files>…`: every entry of the table of each given file, in
the order of the text: the place, the path, and its steps. -/
def resolutions (options : Options) : IO UInt32 := do
  let inputs ← options.files.mapM readInput
  let check ← checkNames inputs (libraryLoader options.libraries)
  for refusal in check.refusals do
    IO.println s!"{refusal.span.file}: {refusal.render}"
  for index in [0:check.program.files.size] do
    let file := check.program.files[index]!
    unless options.files.contains file.name do continue
    let source ← IO.FS.readBinFile file.name
    let table := (check.resolutions.files[index]?).getD {}
    let entries := (table.toArray.qsort fun a b => a.1 < b.1)
    for (byte, resolution) in entries do
      let (line, column) := place source byte.toNat
      IO.println s!"{file.name}:{line}:{column} {pathTextAt source byte.toNat} = {renderResolution check.program resolution}"
  return if check.refusals.isEmpty then 0 else 1

/-- `instances [--library <dir>]… <files>…`: the refusals of names, or those of instances with
their chains, or a summary: the instances by kind and the default instances of each declaration
that has some. The exit code is 1 when something is refused. -/
def instances (options : Options) : IO UInt32 := do
  let inputs ← options.files.mapM readInput
  let check ← checkNames inputs (libraryLoader options.libraries)
  unless check.refusals.isEmpty do
    for refusal in check.refusals do IO.println s!"{refusal.span.file}: {refusal.render}"
    return 1
  let result := checkInstances check (inputs.map (·.name))
  for text in result.state.reports do IO.println s!"report: {text}"
  unless result.refusals.isEmpty do
    for refusal in result.refusals do IO.println s!"{refusal.span.file}: {refusal.render}"
    return 1
  printIncomplete result.incomplete
  let counts := result.countsByKind.toList.map fun (kind, count) => s!"{count} {kind}"
  IO.println s!"{verdict false result.incomplete}: {result.state.results.instanceCount} instances ({", ".intercalate counts})"
  if options.contents then
    for id in result.state.table.requestedIds do
      let entry := result.state.table.entries[id]!
      let description := match ((Static.describeInstance entry.key.declaration
          entry.key.arguments).run result.context result.state).1 with
        | .ok text => text
        | .error _ => "?"
      let content := match entry.state with
        | .done (.data content) => Instances.renderContent result.state content
        | .exhausted exhaustion => s!"nothing: it is not checked, {exhaustion.describe}"
        | _ => "failed"
      IO.println s!"instance {description} holds {content}"
  let program := check.program
  for entry in result.state.defaults do
    let name := program.nameOf entry.declaration
    match entry.none?, entry.first with
    | some reason, _ => IO.println s!"no default instance of `{name}`: {reason}"
    | none, some first => IO.println s!"default instances of `{name}`: {entry.count}, the first `{first}`"
    | none, none => IO.println s!"default instances of `{name}`: none holds its `where`"
  return exitCode false result.incomplete


/-- Type the source bodies and report admission of their emitted packages. -/
def types (options : Options) : IO UInt32 := do
  let inputs ← options.files.mapM readInput
  let check ← checkNames inputs (libraryLoader options.libraries)
  unless check.refusals.isEmpty do
    for refusal in check.refusals do IO.println s!"{refusal.span.file}: {refusal.render}"
    return 1
  let instances := checkInstances check (inputs.map (·.name))
  let result := checkTyping instances (inputs.map (·.name))
  for refusal in result.refusals do IO.println s!"{refusal.span.file}: {refusal.render}"
  printIncomplete result.incomplete
  let mut admitted := 0
  let mut waiting := 0
  let mut typedOnly := 0
  let mut failed := 0
  let mut exhausted := 0
  for report in result.packages do
    match report.outcome with
    | .admitted package =>
      admitted := admitted + 1
      IO.println s!"package {report.description}: admitted, {package.admitted.program.headers.fns.length} functions"
    | .refused source errors =>
      failed := failed + 1
      IO.println s!"package {report.description}: refused by the core: {source.describeRefusals errors}"
    | .waiting reason =>
      waiting := waiting + 1
      IO.println s!"package {report.description}: waiting for {reason}"
    | .typedOnly reason =>
      typedOnly := typedOnly + 1
      IO.println s!"package {report.description}: typed, not emitted: {reason}"
    | .defect message =>
      failed := failed + 1
      IO.println s!"package {report.description}: not emitted: {message}"
    | .exhausted exhaustion =>
      exhausted := exhausted + 1
      IO.println s!"package {report.description}: not checked: {exhaustion.describe}"
  IO.println s!"packages: {admitted} admitted, {waiting} waiting, {typedOnly} typed only, {failed} failed, {exhausted} incomplete"
  -- the sites of every protocol typed: from a core site to its event, part, name and place (EV3)
  let bodies := result.state.results.bodies.entries.toList.mergeSort (fun a b => a.key ≤ b.key)
  for entry in bodies do
    let .done (.protocol code) := entry.state | continue
    unless code.sites.isEmpty do
      IO.println s!"sites of {code.name}:"
    for number in [0:code.sites.size] do
      let site := code.sites[number]!
      let place := s!"{site.place.file}:{site.place.startLine}:{site.place.startColumn}"
      let iteration := if site.iteration.isEmpty then ""
        else s!", iteration {".".intercalate (site.iteration.toList.map toString)}"
      IO.println s!"  {number}: event {site.event}, {site.part}{(site.name.map (s!", {·}")).getD ""}{iteration}, {place}"
    unless code.specificationArguments.isEmpty do
      IO.println s!"specification arguments of {code.name}:"
    for argument in code.specificationArguments do
      IO.println s!"  site {argument.site}, port {argument.port}: `{argument.text}`, a `{argument.type}`"
  -- the obligations that the laws typed leave (SP10)
  for obligation in result.state.results.obligations do
    IO.println s!"obligation: the law `{obligation.law}` of `{obligation.module}` ({obligation.place.file}:{obligation.place.startLine})"
  return exitCode (!result.refusals.isEmpty || failed > 0) result.incomplete

/-- Measure the phases up to package admission. -/
def bench (options : Options) : IO UInt32 := do
  IO.println s!"machine: {← Bench.machine}"
  IO.println s!"toolchain: Lean {Lean.versionString}"
  let (inputs, parseMeasure) ← Bench.measure options.repetitions
    (fun i => options.files.mapM fun (path : String) => do
      let source ← IO.FS.readBinFile path
      -- the name differs between runs so that no run reuses another's result
      pure ({ name := if i == 0 then path else s!"{path}#{i}", parsed := parse path source } : SourceInput))
    (fun inputs => if inputs.isEmpty then IO.println "no input" else pure ())
  let lines ← options.files.foldlM (init := 0) fun count (path : String) => do
    return count + Bench.countLines (← IO.FS.readBinFile path)
  IO.println s!"files: {options.files.size} given, {lines} lines"
  IO.println (Bench.report "read and parse" parseMeasure)
  -- the library is read once; assembly is then measured on sources in memory
  let library ← IO.mkRef ({} : Std.HashMap String (Option SourceInput))
  let load (names : Array String) : IO (Option SourceInput) := do
    let key := pathText names
    if let some cached := (← library.get)[key]? then return cached
    let input ← libraryLoader options.libraries names
    library.modify (·.insert key input)
    return input
  discard <| assemble inputs load
  let (assembly, assembleMeasure) ← Bench.measure options.repetitions
    (fun i => assemble (if i == 999999999 then #[] else inputs) load)
    (fun assembly => if assembly.program.files.isEmpty then IO.println "no file" else pure ())
  IO.println s!"program: {assembly.program.files.size} files, {assembly.program.declarations.size} declarations, {assembly.program.imports.size} imports"
  IO.println (Bench.report "assemble" assembleMeasure)
  let assembled := ({ Driver.Session.start with inputNames := inputs.map (·.name) } : Driver.Session).run
    (Driver.assemble assembly)
  let (named, resolveMeasure) ← Bench.measure options.repetitions
    (fun i => pure ((if i == 999999999 then default else assembled).run Driver.resolve))
    (fun session => if session.state.env.modules.resolutions.size == 0 then IO.println "nothing resolved" else pure ())
  let check : NameCheck := ⟨named⟩
  IO.println s!"resolved paths: {check.resolutions.size}, refusals: {check.refusals.size}"
  IO.println (Bench.report "resolve" resolveMeasure)
  let (instances, instanceMeasure) ← Bench.measure options.repetitions
    (fun i => pure (checkRoots (if i == 999999999 then default else check)))
    (fun result => if result.state.table.requestedIds.isEmpty then IO.println "no instance" else pure ())
  IO.println s!"instances of the roots: {instances.state.results.instanceCount}, refusals: {instances.refusals.size}"
  IO.println (Bench.report "instantiate" instanceMeasure)
  -- the typing of bodies with the default instances, then with the emission of the packages and
  -- their admission
  let (bodies, typeMeasure) ← Bench.measure options.repetitions
    (fun i => pure (typeBodiesOf (if i == 999999999 then default else instances)))
    (fun result => if result.state.results.bodies.entries.isEmpty then IO.println "no body" else pure ())
  let typed := bodies.state
  let typedCount := typed.results.finished.size
  let defaults := typed.results.defaults.foldl (· + ·.count) 0
  IO.println s!"bodies: {typed.results.bodies.entries.size} instances, {typedCount} typed, {defaults} default instances, rows: {typed.results.rows.size}, refusals: {typed.log.entries.size - instances.state.log.entries.size}"
  IO.println (Bench.report "type" typeMeasure)
  let (checked, emitMeasure) ← Bench.measure options.repetitions
    (fun i => pure (checkTyping (typeBodiesOf (if i == 999999999 then default else instances))))
    (fun result => if result.packages.isEmpty then IO.println "no package" else pure ())
  let admitted := (checked.packages.filter fun report => report.outcome matches .admitted _).size
  IO.println s!"packages: {checked.packages.size}, {admitted} admitted by the core"
  IO.println (Bench.report "type, emit and admit" emitMeasure)
  IO.println s!"process peak resident {Bench.mebibytes (← Bench.statusField "VmHWM")} MiB"
  return 0

end Zkc.Tools.Frontend.Names
