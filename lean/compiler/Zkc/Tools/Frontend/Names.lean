import Zkc.Frontend
import Zkc.Core.Package
import Zkc.Tools.Frontend.Bench

/-!
# The commands of `zkc-check`

`names` assembles a program from the given files and the library modules they reach, and
resolves every written name; `instances` forms the instances of its roots; `types` types the
bodies and emits a package of the core per root, and constructs the schemes; `prove` and
`verify` run the prover's and the verifier's programs of a constructed scheme. `bench` measures the phases of the same run. A library directory
holds module files by path: `zkc::a::b` is `<dir>/zkc/a/b.zkc`; several directories are read in
the order given.
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
  repetitions : Nat := 5
  files : Array String := #[]
  /-- `instances` prints every instance with what it holds. -/
  contents : Bool := false
  /-- `types` writes each emitted package as JSON into this directory. -/
  packages : Option System.FilePath := none
  /-- `run`: the root, the function of its package, and the inputs as JSON. -/
  root : Option String := none
  function : Option String := none
  inputs : Option String := none
  /-- `run` of a protocol: the roles that run, against the messages given, and the seed. -/
  roles : Array String := #[]
  messages : Option String := none
  seed : Nat := 1
  /-- `run` and `measure`: the inputs as JSON in a file. -/
  inputsFile : Option String := none
  /-- `measure`: no run of the roles. -/
  noRun : Bool := false
  /-- `prove` and `verify`: the scheme, the statement and the witness as JSON, and the proof in
  hexadecimal. -/
  scheme : Option String := none
  statement : Option String := none
  witness : Option String := none
  proof : Option String := none
  /-- `trees`: the reading of each protocol root against the run of its package, under this
  many seeds. -/
  runs : Bool := false
  seeds : Nat := 16
  /-- `trees`: only count the trees and nodes that the run holds. -/
  count : Bool := false

/-- `[--library <dir>]… [--repeat <n>] <files>…` -/
def readOptions : List String → Options → Except String Options
  | "--library" :: directory :: rest, options =>
    readOptions rest { options with libraries := options.libraries.push directory }
  | "--contents" :: rest, options => readOptions rest { options with contents := true }
  | "--packages" :: directory :: rest, options =>
    readOptions rest { options with packages := some directory }
  | "--root" :: root :: rest, options => readOptions rest { options with root := some root }
  | "--function" :: function :: rest, options =>
    readOptions rest { options with function := some function }
  | "--inputs" :: inputs :: rest, options => readOptions rest { options with inputs := some inputs }
  | "--inputs-file" :: path :: rest, options => readOptions rest { options with inputsFile := some path }
  | "--no-run" :: rest, options => readOptions rest { options with noRun := true }
  | "--scheme" :: scheme :: rest, options => readOptions rest { options with scheme := some scheme }
  | "--statement" :: statement :: rest, options =>
    readOptions rest { options with statement := some statement }
  | "--witness" :: witness :: rest, options => readOptions rest { options with witness := some witness }
  | "--proof" :: proof :: rest, options => readOptions rest { options with proof := some proof }
  | "--role" :: role :: rest, options => readOptions rest { options with roles := options.roles.push role }
  | "--messages" :: messages :: rest, options =>
    readOptions rest { options with messages := some messages }
  | "--seed" :: seed :: rest, options =>
    match seed.toNat? with
    | some n => readOptions rest { options with seed := n }
    | none => .error s!"--seed takes a number, not `{seed}`"
  | "--runs" :: rest, options => readOptions rest { options with runs := true }
  | "--count" :: rest, options => readOptions rest { options with count := true }
  | "--seeds" :: count :: rest, options =>
    match count.toNat? with
    | some n => readOptions rest { options with seeds := n }
    | none => .error s!"--seeds takes a number, not `{count}`"
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
  IO.println s!"{verdict false result.incomplete}: {result.state.table.entries.size} instances ({", ".intercalate counts})"
  if options.contents then
    for entry in result.state.table.entries do
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

/-- A file name for a package: the root without what a file name cannot hold. -/
def packageFileName (index : Nat) (description : String) : String :=
  let safe := description.map fun c => if c.isAlphanum || c == '_' || c == '-' then c else '_'
  s!"{index}-{safe}.json"

/-- A constructed scheme as `types` prints it: the prover and the verifier, the statement and
the witness, the proof identity, and what the core makes of the constructed program. -/
def describeConstructed (description : String) (scheme : Constructed) : String :=
  let ports (numbers : Array Nat) : String :=
    if numbers.isEmpty then "none" else ", ".intercalate (numbers.toList.map fun port => scheme.ports.getD port "?")
  let admission := "admitted at each step"
  let projected := match scheme.projected with
    | .ok count => s!"projected to {count} role programs"
    | .error message => s!"not projected: {message}"
  s!"{description}: constructed; prover {scheme.roles.getD scheme.prover "?"}, verifier {scheme.roles.getD scheme.verifier "?"}; statement {ports scheme.statement}; witness {ports scheme.witness}; proof identity {Zkc.Core.Concrete.hex scheme.identity}; {scheme.stepped.headers.length} protocols after the steps; the constructed program {admission}; {projected}"

/-- `types [--library <dir>]… [--packages <dir>] <files>…`: the refusals of names, of instances
and of the typing of bodies with their chains; then, per root that is a function or a protocol,
what became of its package: admitted by the core, refused by it, or waiting for a form that is
not typed yet, with the reason; and the sites of every protocol typed, from a core site to its
event, part, name, iteration (in a loop whose iterations are in sequence) and place, and its
specification arguments (the site, the port, the expression and its type), which are typed and
not emitted; then the obligations of the laws, and every scheme: constructed (with its prover
and verifier, statement, witness and proof identity, and what the core makes of the constructed
program), or waiting with the reason. With `--packages` every emitted package is written there as
JSON, the tables of sites and specification arguments in `sites.json`, and for a constructed
scheme `S` its package, its declaration and its constructed program in `scheme-S.json`,
`scheme-S.declaration.json` and `scheme-S.constructed.json`. Only a complete root or scheme is
written: one the run holds, when the run reported no error and left no check incomplete. Without
`--root` and `--scheme` every complete one is written and the others are listed with why; with
them, those named are written, and the request fails when one of them is not complete. An error
or an incomplete check anywhere writes nothing. The exit code is 1 when something is refused, by
the frontend or by the core, a constructed program is not admitted, or a named root or scheme is
not complete. -/
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
  if let some directory := options.packages then IO.FS.createDirAll directory
  -- what is written: the roots and the schemes that are complete; with `--root` or `--scheme`,
  -- those named, each complete or the request fails
  let schemes := checkSchemes result
  let selected := options.root.isSome || options.scheme.isSome
  let rootsAdmitted := schemes.session.admitRoots (if selected then some options.root.toArray else none)
  let schemesAdmitted :=
    schemes.session.admitSchemes (if selected then some options.scheme.toArray else none)
  let writable : Except (Array String)
      (Completed RootPackage × Completed Constructed × Array (String × Lack)) :=
    if selected then do
      return (← rootsAdmitted.complete, ← schemesAdmitted.complete, #[])
    else do
      let (roots, lackingRoots) ← rootsAdmitted.completeRoots
      let (constructed, lackingSchemes) ← schemesAdmitted.completeRoots
      return (roots, constructed, lackingRoots ++ lackingSchemes)
  let directory? : Option (System.FilePath × Completed RootPackage × Completed Constructed) :=
    match options.packages, writable with
    | some directory, .ok (roots, constructed, _) => some (directory, roots, constructed)
    | _, _ => none
  let mut admitted := 0
  let mut waiting := 0
  let mut typedOnly := 0
  let mut failed := 0
  let mut exhausted := 0
  let mut index := 0
  for report in result.packages do
    if let some (directory, roots, _) := directory? then
      if let some held := roots.find? report.description then
        IO.FS.writeFile (directory / packageFileName index report.description)
          ((Zkc.Core.Raw.printPackage held.package).render ++ "\n")
    match report.outcome with
    | .admitted package =>
      admitted := admitted + 1
      IO.println s!"package {report.description}: admitted, {package.functions.length} functions, {package.operations.length} rows, {package.types.length} nominal types"
    | .refused reason _ =>
      failed := failed + 1
      IO.println s!"package {report.description}: refused by the core: {reason}"
    | .unjustified functions _ =>
      failed := failed + 1
      IO.println s!"package {report.description}: elaborated; not justified: {"; ".intercalate functions.toList}"
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
    index := index + 1
  -- the sites of every protocol typed: from a core site to its event, part, name and place (EV3)
  let mut tables : Array Zkc.Json := #[]
  let bodies := result.state.results.bodies.entries.toList.mergeSort (fun a b => a.key ≤ b.key)
  for entry in bodies do
    let .done (.protocol code) := entry.state | continue
    unless code.sites.isEmpty do
      IO.println s!"sites of {code.name}:"
    let mut rows : Array Zkc.Json := #[]
    for number in [0:code.sites.size] do
      let site := code.sites[number]!
      let place := s!"{site.place.file}:{site.place.startLine}:{site.place.startColumn}"
      let iteration := if site.iteration.isEmpty then ""
        else s!", iteration {".".intercalate (site.iteration.toList.map toString)}"
      IO.println s!"  {number}: event {site.event}, {site.part}{(site.name.map (s!", {·}")).getD ""}{iteration}, {place}"
      rows := rows.push (.arr #[.num number, .num site.event, .str site.part,
        (site.name.map Zkc.Json.str).getD .null, .arr (site.iteration.map Zkc.Json.num),
        .str site.place.file, .num site.place.startLine.toNat, .num site.place.startColumn.toNat])
    unless code.specificationArguments.isEmpty do
      IO.println s!"specification arguments of {code.name}:"
    let mut arguments : Array Zkc.Json := #[]
    for argument in code.specificationArguments do
      IO.println s!"  site {argument.site}, port {argument.port}: `{argument.text}`, a `{argument.type}`"
      arguments := arguments.push (.arr #[.num argument.site, .str argument.port, .str argument.text,
        .str argument.type])
    if rows.isEmpty && arguments.isEmpty then continue
    tables := tables.push (.arr #[.str code.name, .arr rows, .arr arguments])
  if let some (directory, _) := directory? then
    unless tables.isEmpty do
      IO.FS.writeFile (directory / "sites.json") ((Zkc.Json.arr tables).render ++ "\n")
  -- the obligations that the laws typed leave (SP10)
  for obligation in result.state.results.obligations do
    IO.println s!"obligation: the law `{obligation.law}` of `{obligation.module}` ({obligation.place.file}:{obligation.place.startLine})"
  -- the schemes: constructed, or waiting, or refused
  for refusal in schemes.refusals do IO.println s!"{refusal.span.file}: {refusal.render}"
  let mut schemeFailures := schemes.refusals.size
  for report in schemes.reports do
    if let some (directory, _, constructed) := directory? then
      if let some held := constructed.find? report.name then
        let write (suffix : String) (json : Zkc.Json) : IO Unit :=
          IO.FS.writeFile (directory / s!"scheme-{report.name}{suffix}.json") (json.render ++ "\n")
        write "" (Zkc.Core.Raw.printPackage held.package)
        write ".declaration" (Zkc.Core.Raw.printDeclaration held.declaration)
        write ".constructed" (Zkc.Core.Raw.printPackage held.constructed)
    match report.outcome with
    | .constructed scheme =>
      IO.println (describeConstructed report.description scheme)
      unless scheme.projected matches .ok _ do schemeFailures := schemeFailures + 1
    | .refusedByCore reason _ =>
      schemeFailures := schemeFailures + 1
      IO.println s!"{report.description}: {reason}"
    | .waiting reason => IO.println s!"{report.description}: waiting for {reason}"
    | .refused _ => pure ()
    | .defect message =>
      schemeFailures := schemeFailures + 1
      IO.println s!"{report.description}: not constructed: {message}"
    | .exhausted exhaustion =>
      IO.println s!"{report.description}: not checked: {exhaustion.describe}"
  let typed := result.state.results.finished.size
  let refused := !(result.refusals.isEmpty && failed == 0 && schemeFailures == 0)
  let incomplete := result.session.incompleteOf #["instances", "types", "defaults", "default bodies", "packages", "schemes"]
  let notChecked := if exhausted == 0 then "" else s!", {exhausted} not checked"
  if options.packages.isSome then
    match writable with
    | .error missing =>
      IO.println "no package is written:"
      for line in missing do IO.println s!"  {line}"
    | .ok (_, _, lacking) =>
      unless lacking.isEmpty do
        IO.println "not written, not complete:"
        for (root, lack) in lacking do IO.println s!"  {root}: {lack.describe}"
  IO.println s!"{verdict refused incomplete}: {typed} function instances typed, {result.packages.size} packages: {admitted} admitted, {typedOnly} typed only, {waiting} waiting{notChecked}, {failed} not admitted; {schemes.reports.size} schemes: {(schemes.reports.filter (·.outcome matches .constructed _)).size} constructed"
  let failedRequest := options.packages.isSome && selected && writable matches .error _
  return if failedRequest && !refused then 1 else exitCode refused incomplete

/-- A datum from JSON: a number, a boolean (as 0 or 1), or an array of data. -/
partial def datumOfJson : Zkc.Json → Option Zkc.Core.Concrete.Datum
  | .num value => some (.number value)
  | .bool value => some (Zkc.Core.Concrete.Datum.ofBool value)
  | .arr items => (items.toList.mapM datumOfJson).map .sequence
  | _ => none

partial def jsonOfDatum : Zkc.Core.Concrete.Datum → Zkc.Json
  | .number value => .num value
  | .sequence items => .arr (items.map jsonOfDatum).toArray

/-- The words of a stop. -/
def describeStop : PIR.Stop → String
  | .reject => "reject" | .abort => "abort" | .refused => "refused" | .exhausted => "exhausted"
  | .incomplete => "incomplete" | .undefined => "undefined"

/-- The line of a run that reached the limit on the work of reading: it is not run to its end,
and the check is incomplete, like one that runs out of a budget of the compiler. -/
def describeLimit (elements : Nat) : String :=
  s!"incomplete: a reading of a value reaches the limit of {elements} elements; the run is not checked to its end"

/-- How a run of a function ends, as a line: `returned <outputs as JSON>`, `stopped <reason>`,
`incomplete:` when a reading of a value reached the limit of the run, or `failed: <message>`. -/
def describeRun : Zkc.Core.Vocabulary.Run → String
  | .returned outputs => s!"returned {(Zkc.Json.arr (outputs.map jsonOfDatum).toArray).render}"
  | .stopped reason => s!"stopped {describeStop reason}"
  | .limit elements => describeLimit elements
  | .failed message => s!"failed: {message}"

/-- How a role of a protocol run ends, as a line, in the words of `describeRun`. -/
def describeRole : Zkc.Core.Execute.Outcome (List Zkc.Core.Concrete.Datum) → String
  | .returned outputs => s!"returned {(Zkc.Json.arr (outputs.map jsonOfDatum).toArray).render}"
  | .stopped reason => s!"stopped {describeStop reason}"
  | .limit elements => describeLimit elements
  | .failed message => s!"failed: {message}"

/-- `run [--library <dir>]… --root <root> [--function <name>] --inputs <json> <files>…`: types
the files, and runs a function of the package of a root (as `types` prints it, or the instance
it is a default instance of) on the inputs, a JSON array with one datum per input: a number, a
boolean, or an array. It prints `returned` and the outputs, `stopped` and the reason, or why the
run did not start; the exit code is 1 when it did not. A run in which a reading of a value
reaches the limit of the run is not checked to its end: it prints `incomplete:` and the limit,
and the exit code is 3, as for a check that runs out of a budget of the compiler.

For a protocol, the inputs are one datum per port that is not `spec`, and every role runs, each
printed with its outputs, its stop, the limit, or why it failed; `--role R` (repeated) runs only
those roles, each alone, against the messages that `--messages` gives as a JSON array of
`[site, datum]` (a core site of the protocol, as `types` lists them) and the coins of an honest
run; `--seed n` seeds the draws and samples. The root runs only from a completed result: no
error reported, no check incomplete, and its package admitted by the core. -/
def run (options : Options) : IO UInt32 := do
  let some root := options.root | do IO.eprintln "run needs --root"; return 2
  let some inputText := options.inputs | do IO.eprintln "run needs --inputs"; return 2
  let inputs ← match Zkc.Json.parse inputText with
    | .ok (.arr items) =>
      match items.toList.mapM datumOfJson with
      | some data => pure data
      | none => do IO.eprintln "an input is not a number, a boolean or an array"; return 2
    | _ => do IO.eprintln "--inputs is a JSON array"; return 2
  let files ← options.files.mapM readInput
  let check ← checkNames files (libraryLoader options.libraries)
  unless check.refusals.isEmpty do
    for refusal in check.refusals do IO.println s!"{refusal.span.file}: {refusal.render}"
    return 1
  let result := checkTyping (checkInstances check (files.map (·.name))) (files.map (·.name))
  unless result.refusals.isEmpty do
    for refusal in result.refusals do IO.println s!"{refusal.span.file}: {refusal.render}"
    return 1
  unless result.packages.any (namesRoot root ·.description) do
    IO.println s!"no root {root}; the roots are {result.packages.map (·.description)}"
    return 1
  let completed ← match (result.session.admitRoots (some #[root])).complete with
    | .ok completed => pure completed
    | .error missing => do IO.println s!"does not run: {"; ".intercalate missing.toList}"; return 1
  -- a protocol: every role together, or the roles named against the messages given
  if let some { protocol := some code, .. } := completed.find? root then
    let mut selected : Option (List Nat) := none
    unless options.roles.isEmpty do
      let mut roles := []
      for name in options.roles do
        match code.roles.findIdx? (· == name) with
        | some index => roles := roles ++ [index]
        | none => do IO.eprintln s!"{root} has no role {name}; its roles are {code.roles}"; return 2
      selected := some roles
    let messages ← match options.messages.map Zkc.Json.parse with
      | none => pure []
      | some (.ok (.arr items)) =>
        match items.toList.mapM fun
            | .arr #[.num site, datum] => (datumOfJson datum).map (site, ·)
            | _ => none with
        | some messages => pure messages
        | none => do IO.eprintln "--messages is a JSON array of [site, datum]"; return 2
      | some _ => do IO.eprintln "--messages is a JSON array of [site, datum]"; return 2
    match completed.runProtocol root inputs [options.seed] selected messages with
    | .error message => do IO.println s!"does not run: {message}"; return 1
    | .ok roles =>
      for role in roles do IO.println s!"{role.role}: {describeRole role.outcome}"
      return if roles.any (·.outcome matches .limit _) then 3 else 0
  let outcome := completed.runFunction root inputs options.function
  IO.println (describeRun outcome)
  return match outcome with
    | .failed _ => 1
    | .limit _ => 3
    | _ => 0

/-- Bytes from hexadecimal, two digits each. -/
def bytesOfHex (text : String) : Option (List Nat) :=
  let digit (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c.toLower && c.toLower ≤ 'f' then some (c.toLower.toNat - 'a'.toNat + 10)
    else none
  let rec pairs : List Char → Option (List Nat)
    | [] => some []
    | high :: low :: rest => do return (16 * (← digit high) + (← digit low)) :: (← pairs rest)
    | [_] => none
  pairs (text.trimAscii.toString.toList)

/-- Data from a JSON array of data, for an option. -/
def dataOfOption (what : String) (text : Option String) : Except String (List Zkc.Core.Concrete.Datum) := do
  let some text := text | throw s!"{what} is needed"
  match Zkc.Json.parse text with
  | .ok (.arr items) =>
    match items.toList.mapM datumOfJson with
    | some data => return data
    | none => throw s!"{what}: a value is not a number, a boolean or an array"
  | _ => throw s!"{what} is a JSON array, one value per port"

/-- The completed result that holds the constructed scheme of a name in the files, with the
name, or why there is none: a refusal, no scheme of the name, or a result that is not complete. -/
def completedScheme (options : Options) : IO (Except String (Completed Constructed × String)) := do
  let some name := options.scheme | return .error "--scheme is needed"
  let files ← options.files.mapM readInput
  let check ← checkNames files (libraryLoader options.libraries)
  if let some first := check.refusals[0]? then return .error s!"{first.span.file}: {first.render}"
  let result := checkTyping (checkInstances check (files.map (·.name))) (files.map (·.name))
  if let some first := result.refusals[0]? then return .error s!"{first.span.file}: {first.render}"
  let schemes := checkSchemes result
  if let some first := schemes.refusals[0]? then return .error s!"{first.span.file}: {first.render}"
  match schemes.reports.find? (·.name == name) with
  | none => return .error s!"no scheme {name}; the schemes are {schemes.reports.map (·.name)}"
  | some report =>
    match (schemes.session.admitSchemes (some #[name])).complete with
    | .ok completed => return .ok (completed, name)
    | .error missing => return .error s!"{report.description} is not complete: {"; ".intercalate missing.toList}"

/-- `prove [--library <dir>]… --scheme <name> --statement <json> --witness <json> [--seed <n>]
<files>…`: the proof of the prover's program of a constructed scheme, in hexadecimal, on one line.
The statement and the witness are JSON arrays with one datum per port, in the order of the
signature (as `types` lists them): a number, a boolean, or an array (a point of G1 is `[x, y]`,
or `[]` for the point at infinity). The seed answers the samples. When a reading of a value
reaches the limit of the run, it prints `no proof: incomplete:` and the exit code is 3. -/
def prove (options : Options) : IO UInt32 := do
  let (completed, name) ← match ← completedScheme options with
    | .ok found => pure found
    | .error message => do IO.println message; return 1
  let result : Except NoProof (List Nat) := do
    let statement ← (dataOfOption "--statement" options.statement).mapError .refused
    let witness ← (dataOfOption "--witness" options.witness).mapError .refused
    completed.prove name statement witness [options.seed]
  match result with
  | .ok proof =>
    IO.println (Zkc.Core.Concrete.hex proof)
    return 0
  | .error (.limit elements) =>
    IO.println s!"no proof: {describeLimit elements}"
    return 3
  | .error (.refused message) =>
    IO.println s!"no proof: {message}"
    return 1

/-- `verify [--library <dir>]… --scheme <name> --statement <json> --proof <hex> <files>…`: runs
the verifier's program of a constructed scheme on the statement and the proof, and prints
`accepted` when it returns, or `not accepted:` and how it ends. The exit code is 0 when
accepted; when a reading of the proof reaches the limit of the run, the proof is not checked to
its end: it prints `not checked: incomplete:` and the exit code is 3. -/
def verify (options : Options) : IO UInt32 := do
  let (completed, name) ← match ← completedScheme options with
    | .ok found => pure found
    | .error message => do IO.println message; return 1
  let result := do
    let statement ← dataOfOption "--statement" options.statement
    let some text := options.proof | throw "--proof is needed"
    let some proof := bytesOfHex text | throw "--proof is bytes in hexadecimal"
    completed.verify name statement proof
  match result with
  | .ok (.returned _) =>
    IO.println "accepted"
    return 0
  | .ok (.limit elements) =>
    IO.println s!"not checked: {describeLimit elements}"
    return 3
  | .ok outcome =>
    IO.println s!"not accepted: {describeRole outcome}"
    return 1
  | .error message =>
    IO.println s!"not run: {message}"
    return 1

/-- The operations of a local region: each instruction, and those of its nested regions. -/
partial def localOperations : Zkc.Core.Raw.LocalRegion → Nat
  | .ret _ | .stop _ => 0
  | .step instruction next => 1 + nested instruction + localOperations next
  | .block _ body next => localOperations body + localOperations next
where
  nested : Zkc.Core.Raw.LocalStep → Nat
    | .conditional _ _ _ onTrue onFalse => localOperations onTrue + localOperations onFalse
    | .«match» _ _ _ _ arms => (arms.toList.map localOperations).foldl (· + ·) 0
    | .loop _ _ _ _ body => localOperations body
    | _ => 0

/-- The operations of a protocol region: each instruction, and those of its nested regions. -/
partial def protocolOperations : Zkc.Core.Raw.ProtocolRegion → Nat
  | .ret _ | .stop _ => 0
  | .step instruction next => 1 + nested instruction + protocolOperations next
  | .block _ body next => protocolOperations body + protocolOperations next
where
  nested : Zkc.Core.Raw.ProtocolStep → Nat
    | .at _ step => localOperations.nested step
    | .repeat _ _ _ _ _ body => protocolOperations body
    | .choose _ _ _ _ _ arms => (arms.toList.map protocolOperations).foldl (· + ·) 0
    | _ => 0

/-- The operations of a package: of its functions' bodies and of its protocols' bodies. -/
def packageOperations (package : Zkc.Core.Raw.Package) : Nat × Nat :=
  let functions := package.functions.foldl (init := 0) fun total function =>
    total + (function.body.map localOperations).getD 0
  let protocols := package.protocols.foldl (init := 0) fun total protocol =>
    total + protocolOperations protocol.body
  (functions, protocols)

/-- `measure [--library <dir>]… --root <root> (--inputs <json> | --inputs-file <path>) [--repeat
<n>] [--no-run] <files>…`: the cost of a root by phase: the checks of names and instances, the
typing of the program's bodies, the emission of the root's package (its operations and its bytes
as JSON), the core's `elaborate` and its check of facts, and, for a protocol, the projection to
role programs and an honest run of all roles, for a function a run on the inputs; then the peak
resident memory of the process and one row with all of it. Each phase is timed once cold and
`--repeat` times warm. -/
def measure (options : Options) : IO UInt32 := do
  let some root := options.root | do IO.eprintln "measure needs --root"; return 2
  let inputText ← match options.inputs, options.inputsFile with
    | some text, _ => pure text
    | none, some path => IO.FS.readFile path
    | none, none => do IO.eprintln "measure needs --inputs or --inputs-file"; return 2
  let inputs ← match Zkc.Json.parse inputText with
    | .ok (.arr items) =>
      match items.toList.mapM datumOfJson with
      | some data => pure data
      | none => do IO.eprintln "an input is not a number, a boolean or an array"; return 2
    | _ => do IO.eprintln "the inputs are a JSON array"; return 2
  IO.println s!"machine: {← Bench.machine}"
  IO.println s!"toolchain: Lean {Lean.versionString}"
  let repetitions := options.repetitions
  let files ← options.files.mapM readInput
  let names := files.map (·.name)
  let loader := libraryLoader options.libraries
  let (instances, checkMeasure) ← Bench.measure repetitions
    (fun _ => do
      let check ← checkNames files loader
      pure (check, checkRoots check names))
    (fun _ => pure ())
  IO.println (Bench.report "names and instances" checkMeasure)
  let (nameCheck, instanceCheck) := instances
  unless nameCheck.refusals.isEmpty && instanceCheck.refusals.isEmpty do
    IO.println "the names or the instances are refused"
    return 1
  let (state, typeMeasure) ← Bench.measure repetitions
    (fun i => pure (typeBodiesOf (if i == 999999999 then default else instanceCheck)).state)
    (fun state => if state.log.entries.isEmpty then pure () else IO.println "a body is refused")
  IO.println (Bench.report "type the bodies" typeMeasure)
  let some rootId := (Typing.functionRoots state).find? fun candidate =>
      Static.renderInstance state candidate == root
    | IO.println s!"no root {root}"
      return 1
  let code? : Option Typing.ProtocolCode := match state.results.body? rootId with
    | some (.protocol code) => some code
    | _ => none
  let (emitted, emitMeasure) ← Bench.measure repetitions (fun _ => pure (Typing.emitPackage state rootId))
    (fun _ => pure ())
  IO.println (Bench.report "emit the package" emitMeasure)
  let .ok package := emitted
    | IO.println s!"the package of {root} is not emitted"
      return 1
  let bytes := ((Zkc.Core.Raw.printPackage package).render).utf8ByteSize
  let (functionOperations, protocolOperations) := packageOperations package
  IO.println s!"package: {package.functions.length} functions, {package.protocols.length} protocols, {functionOperations + protocolOperations} operations ({protocolOperations} of protocols), {bytes} bytes"
  let (elaborated, elaborateMeasure) ← Bench.measure repetitions (fun _ => pure (Zkc.Core.elaborate package))
    (fun _ => pure ())
  IO.println (Bench.report "elaborate" elaborateMeasure)
  let .ok typed := elaborated
    | IO.println "the core refuses the package"
      return 1
  let (unjustified, factsMeasure) ← Bench.measure repetitions
    (fun _ => pure (typed.program.functions.unjustified.length + typed.program.protocols.unjustified.length))
    (fun _ => pure ())
  IO.println (Bench.report "check of facts" factsMeasure)
  -- what is run: the root as the session admits it, from a completed result; the core's
  -- elaboration of its package is done before the run is timed
  let packaged := ({ instanceCheck.session with state } : Driver.Session).run Driver.packages
  let completed? : Except (Array String) (Completed RootPackage) :=
    (packaged.admitRoots (some #[root])).complete
  match completed? with
  | .error missing => IO.println s!"not run: {"; ".intercalate missing.toList}"
  | .ok completed =>
    if let some rootPackage := completed.find? root then
      if let .error message := rootPackage.typed.get then IO.println s!"not run: {message}"
  let mut projectText := "-"
  let mut runText := "-"
  match code? with
  | some code =>
    let (projected, projectMeasure) ← Bench.measure repetitions
      (fun _ => pure (projectRoles package typed code.roles.size)) (fun _ => pure ())
    IO.println (Bench.report "project" projectMeasure)
    if let .error message := projected then IO.println s!"projection: {message}"
    projectText := if projectMeasure.warm.isEmpty then Bench.milliseconds projectMeasure.cold
      else Bench.milliseconds (Bench.median projectMeasure.warm)
    if let (false, .ok completed) := (options.noRun, completed?) then
      let (runs, runMeasure) ← Bench.measure repetitions
        (fun _ => pure (completed.runProtocol root inputs [options.seed])) (fun _ => pure ())
      IO.println (Bench.report "run (projection included)" runMeasure)
      match runs with
      | .ok roles => for role in roles do IO.println s!"{role.role}: {describeRole role.outcome}"
      | .error message => IO.println s!"does not run: {message}"
      runText := if runMeasure.warm.isEmpty then Bench.milliseconds runMeasure.cold
        else Bench.milliseconds (Bench.median runMeasure.warm)
  | none =>
    -- a function: its package run on the inputs
    if let (false, .ok completed) := (options.noRun, completed?) then
      let (outcome, runMeasure) ← Bench.measure repetitions
        (fun _ => pure (completed.runFunction root inputs)) (fun _ => pure ())
      IO.println (Bench.report "run" runMeasure)
      IO.println (describeRun outcome)
      runText := if runMeasure.warm.isEmpty then Bench.milliseconds runMeasure.cold
        else Bench.milliseconds (Bench.median runMeasure.warm)
  let peak ← Bench.statusField "VmHWM"
  -- the row gives the median of the warm runs when there are some, otherwise the cold one
  let time (m : Bench.Measure) : String :=
    Bench.milliseconds (if m.warm.isEmpty then m.cold else Bench.median m.warm)
  IO.println s!"peak resident {Bench.mebibytes peak} MiB; functions not justified: {unjustified}"
  IO.println s!"row: {root} | {functionOperations + protocolOperations} | {protocolOperations} | {bytes} | {time typeMeasure} | {time emitMeasure} | {time elaborateMeasure} | {time factsMeasure} | {projectText} | {runText} | {Bench.mebibytes peak}"
  return 0

/-- `bench [--library <dir>]… [--repeat <n>] <files>…`: time and peak memory of reading and
parsing, assembling, resolving, instantiating, typing the bodies, and typing them with the
emission and admission of the packages, each once cold and then `repetitions` times warm. -/
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
    (fun result => if result.state.table.entries.isEmpty then IO.println "no instance" else pure ())
  IO.println s!"instances of the roots: {instances.state.table.entries.size}, refusals: {instances.refusals.size}"
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
