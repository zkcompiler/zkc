import Zkc.Tools.Program.DeclarationAudit
import Zkc.Tools.Program.ImportArtifacts

/-! Declaration records for package-owned code.

Writes one JSON line per declaration written in the source of the selected
module families, sorted by name and module, after a header line. A record
states the declaration's name, module and kind, its structural and explicit
statement hashes (`ZkcTools.Statements` in `ZkcTools.DeclarationAudit`), its axiom closure (actual stored ConstantInfo
types and bodies, opaque proofs included; imported axiom caches are never authority), its docstring, structural tags
and, for theorems, its premise telescope: every leading binder, implicit and
instance binders included, with whether it is a premise and the head constant
of the premise's proposition. Declarations that Lean generates (recursors,
matchers, equation and injectivity lemmas, auxiliary proofs) carry no source
range and are omitted; the declaration audit still covers them.

Run after building the selected packages, from the package directory:

```sh
lake env lean --run Zkc/Tools/IR/DeclarationRecords.lean [OPTION]... OUTPUT DIRECTORY...
```

The maintained Python driver builds the `declaration-records` executable and
the audited package first, then runs the executable in that package's Lake
environment. The interpreted command above remains a comparison/debugging
route. Both traverse the same stored declarations; no records are cached.

Each `DIRECTORY` is a source directory or a single `.lean` file relative to the
current directory, such as `Zkc` or `ZkcTools/JsonSupport.lean`; every module
below it is imported and selected. Executable roots, which each define `main`,
cannot be imported together and are selected by their library directories.

Options:
- `--check BASELINE`: compare the fresh records with an earlier output and fail,
  naming each added, removed or changed declaration, when they differ.
- `--registry NAME`: evaluate the registry table `NAME`, a list of identifier,
  category, schema constant and statement, and record it in the header; a
  missing table is an error.
- `--endpoints NAME`: evaluate the table of registered endpoints `NAME`, a list
  of covered endpoint, property, statement form and theorem, record it in the
  header and record every registered endpoint theorem in detail.
- `--detail NAME`: also record the pretty-printed statement and premises of the
  declaration `NAME`, its premise telescope whatever its kind, the registered
  constants (registry schemas and endpoints) it reaches through repository
  declarations, the head constant and arguments of its statement and of its
  value, every binder with the head constant of its type, the premise telescope
  of a statement that is an instance of a registered property (the head of a
  registered endpoint theorem's statement, unfolded once) (repeatable). A name that is not a declaration
  of the selected modules is refused.
- `--trace-records`: print the declaration currently being inspected and its
  elapsed time to stderr. This changes diagnostics only, not the records.

The output is deterministic for a fixed toolchain and fixed sources. Equal
statement hashes are regression evidence, not semantic preservation. -/

open Lean Meta ZkcTools.Statements

namespace DeclarationRecords

/-- Compare complete stored values, including theorem proofs. Only identical
versions may share a provider class; definitional equality/proof irrelevance
must not collapse different proofs or their axiom dependencies. -/
def sameStoredFields : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
  | .opaqueInfo a, .opaqueInfo b => a == b
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | .inductInfo a, .inductInfo b =>
    a.toConstantVal == b.toConstantVal && a.numParams == b.numParams &&
    a.numIndices == b.numIndices && a.all == b.all && a.ctors == b.ctors &&
    a.numNested == b.numNested && a.isRec == b.isRec && a.isUnsafe == b.isUnsafe &&
    a.isReflexive == b.isReflexive
  | .quotInfo a, .quotInfo b => a.toConstantVal == b.toConstantVal &&
    (match a.kind, b.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false)
  | _, _ => false

/-- Derived ConstantInfo equality uses Expr.eqv, which ignores binder
annotations. Exact provider equivalence also checks the complete expression
structure, including binder names and visibility, in types, bodies and rules. -/
def sameStored (left right : ConstantInfo) : Bool :=
  sameStoredFields left right && left.type.equal right.type &&
    (match left.value? true, right.value? true with
      | none, none => true
      | some a, some b => a.equal b
      | _, _ => false) &&
    (match left, right with
      | .recInfo a, .recInfo b => a.rules.length == b.rules.length &&
          (a.rules.zip b.rules).all (fun (x, y) => x.rhs.equal y.rhs)
      | _, _ => true)

abbrev Providers := Std.HashMap Name (Option (Name × ConstantInfo))

/-- Lean can store identical generated declarations in several modules. Admit
these only after comparing all stored fields (proof bodies included), choosing
the least module Name as a deterministic representative. Differing versions are
ambiguous even if Lean's merged map happens to prefer one. -/
def providers (env : Environment) : Providers := Id.run do
  let mut found : Providers := {}
  for index in [:env.header.modules.size] do
    let owner := env.header.modules[index]!.module
    let mut localNames : Std.HashSet Name := {}
    for info in env.header.moduleData[index]!.constants do
      if localNames.contains info.name then
        found := found.insert info.name none
        continue
      localNames := localNames.insert info.name
      let value := match found[info.name]? with
        | none => some (owner, info)
        | some none => none
        | some (some (previous, stored)) =>
          if sameStored stored info then some (if Name.lt owner previous then owner else previous, stored)
          else none
      found := found.insert info.name value
  return found

/-- Validate the merged module association against stored declarations too.
A checked identical-provider class may have several owners, but the environment
must actually select one of them when recording a module identity. -/
def resolvedOwners (env : Environment) : Std.HashSet Name := Id.run do
  let mut found : Std.HashSet Name := {}
  for index in [:env.header.modules.size] do
    for info in env.header.moduleData[index]!.constants do
      if (env.getModuleIdxFor? info.name).any (·.toNat == index) then
        found := found.insert info.name
  return found

def provider (sources : Providers) (name : Name) : IO Name := do
  match sources[name]? with
  | some (some (owner, _)) => return owner
  | some none => throw <| IO.userError s!"ambiguous stored providers for dependency: {name}"
  | none => throw <| IO.userError s!"uncovered stored dependency: {name}"

def dependencies (info : ConstantInfo) : Array Name := Id.run do
  let mut refs := info.type.getUsedConstants ++
    ((info.value? true).map Expr.getUsedConstants |>.getD #[])
  match info with
  | .inductInfo value => refs := refs ++ value.all.toArray ++ value.ctors.toArray
  | .ctorInfo value => refs := refs.push value.induct
  | .recInfo value =>
    refs := refs ++ value.all.toArray
    for rule in value.rules do refs := refs.push rule.ctor ++ rule.rhs.getUsedConstants
  | _ => pure ()
  return refs

structure Cache where
  edges : Std.HashMap Name (Array Name) := {}
  closed : Std.HashMap Name (Array Name) := {}
  displayNames : Std.HashMap String Name := {}

/-- Traverse actual resolved ConstantInfo bodies, including opaque proofs.
Never consult collectAxioms' imported extension. Only a fully traversed root is
cached; a cycle sentinel is never published as an axiom closure. If the complete
closure is empty, every visited subclosure is empty too and can safely be cached.
The edge and completed-closure caches belong to this one environment. -/
def storedAxioms (env : Environment) (sources : Providers) (owners : Std.HashSet Name)
    (owned : Std.HashMap Name ConstantInfo) (root : ConstantInfo) (cache : Cache) :
    IO (Array Name × Cache) := do
  let mut cache := cache
  let mut pending := #[root.name]
  let mut visited : Std.HashSet Name := {}
  let mut axioms : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    let _ ← provider sources name
    unless owners.contains name do
      throw <| IO.userError s!"resolved module does not store dependency: {name}"
    if let some previous := cache.displayNames[name.toString]? then
      unless previous == name do
        throw <| IO.userError s!"ambiguous rendered kernel name: {name}"
    cache := { cache with displayNames := cache.displayNames.insert name.toString name }
    visited := visited.insert name
    if let some closed := cache.closed[name]? then
      for axiomName in closed do axioms := axioms.insert axiomName
      continue
    let some info := owned[name]?.orElse (fun _ => env.find? name)
      | throw <| IO.userError s!"unresolved dependency: {name}"
    let some (some (_, stored)) := sources[name]?
      | throw <| IO.userError s!"missing checked provider: {name}"
    unless sameStored stored info do
      throw <| IO.userError s!"resolved declaration differs from stored provider: {name}"
    if info matches .axiomInfo _ then axioms := axioms.insert name
    let refs := match cache.edges[name]? with
      | some refs => refs
      | none => dependencies info
    cache := { cache with edges := cache.edges.insert name refs }
    pending := pending ++ refs
  let result := axioms.toArray
  cache := { cache with closed := cache.closed.insert root.name result }
  if result.isEmpty then
    for name in visited do cache := { cache with closed := cache.closed.insert name #[] }
  return (result, cache)


/-- Module names of every `.lean` file below `directory`. -/
partial def modulesBelow (directory : System.FilePath) : IO (Array Name) := do
  let mut found := #[]
  for entry in ← directory.readDir do
    if ← entry.path.isDir then
      found := found ++ (← modulesBelow entry.path)
    else if entry.path.extension == some "lean" then
      let relative := (entry.path.withExtension "").components
      found := found.push (relative.foldl Name.str Name.anonymous)
  return found

structure Options where
  check : Option System.FilePath := none
  registry : Option Name := none
  endpoints : Option Name := none
  details : Array Name := #[]
  positional : Array String := #[]
  traceRecords : Bool := false

partial def parse : List String → Options → Except String Options
  | [], options => .ok options
  | "--check" :: path :: rest, options => parse rest { options with check := some path }
  | "--registry" :: name :: rest, options => parse rest { options with registry := some name.toName }
  | "--endpoints" :: name :: rest, options => parse rest { options with endpoints := some name.toName }
  | "--detail" :: name :: rest, options =>
      parse rest { options with details := options.details.push name.toName }
  | "--trace-records" :: rest, options => parse rest { options with traceRecords := true }
  | argument :: rest, options =>
      if argument.startsWith "--" then .error s!"unknown or incomplete option: {argument}"
      else parse rest { options with positional := options.positional.push argument }

def tags (env : Environment) (name : Name) (info : ConstantInfo) : Array String := Id.run do
  let mut found := #[]
  if isPrivateName name then found := found.push "private"
  if isClass env name then found := found.push "class"
  else if isStructure env name then found := found.push "structure"
  if Meta.isInstanceCore env name then found := found.push "instance"
  if propositionValued info then found := found.push "proposition-valued"
  return found

def premiseJson (premise : Premise) : Json :=
  Json.mkObj <| [("binder", Json.str (binderName premise.binder)), ("premise", Json.bool premise.proof)] ++
    match premise.head with
    | some head => [("head", Json.str head.toString)]
    | none => []

/-- Module roots of this repository's packages. The walk for registered
constants descends only through declarations of these modules. -/
def repositoryRoots : List Name :=
  [`Zkc.Program, `Zkc.IR, `Zkc.Protocol, `Zkc.Verification, `Zkc.Adapters,
    `Zkc.Applications, `Zkc.Tools, `Zkc.Tests]

/-- The registered constants a declaration reaches through the types and
bodies of repository declarations, itself included. Upstream declarations are
recorded when reached but not descended into. -/
def reached (env : Environment) (registered : Std.HashSet Name) (start : Name) : Array Name := Id.run do
  let owned := fun (name : Name) => Id.run do
    let some index := env.getModuleIdxFor? name | return false
    let some module := env.header.modules[index.toNat]? | return false
    return repositoryRoots.any (·.isPrefixOf module.module)
  let mut seen : Std.HashSet Name := {}
  let mut pending := [start]
  let mut found := #[]
  while true do
    match pending with
    | [] => break
    | name :: rest =>
      pending := rest
      if seen.contains name then continue
      seen := seen.insert name
      if registered.contains name then found := found.push name
      unless owned name do continue
      let some info := env.find? name | continue
      let mut next := info.type.getUsedConstants
      if let some value := info.value? true then next := next ++ value.getUsedConstants
      if let .inductInfo value := info then next := next ++ value.ctors.toArray
      pending := next.toList ++ pending
  return found.qsort Name.lt

/-- The head constant of an application, if any. -/
def headName (expression : Expr) : Option Name :=
  expression.getAppFn.consumeMData.constName?

def nameJson : Option Name → Json
  | some name => Json.str name.toString
  | none => Json.null

/-- The arguments of an application, each with its head constant and its text. -/
def argumentsJson (expression : Expr) : MetaM Json := do
  let arguments ← expression.getAppArgs.mapM fun argument => do
    return Json.mkObj [("head", nameJson (headName argument)), ("text", Json.str (toString (← ppExpr argument)))]
  return Json.arr arguments

/-- Every leading binder is recorded without interpreting it as an authorized assumption. -/
def bindersJson (type : Expr) : MetaM Json :=
  forallTelescope type fun binders _ => do
    let found ← binders.mapM fun binder => do
      let declaration ← binder.fvarId!.getDecl
      let proof ← isProp declaration.type
      return Json.mkObj [
        ("binder", Json.str (binderName declaration.binderInfo)),
        ("premise", Json.bool proof),
        ("type_head", if declaration.type.isSort then Json.str "sort"
          else nameJson (headName declaration.type)),
        ("type", Json.str (toString (← ppExpr declaration.type)))]
    return Json.arr found

/-- Generic statement observations. No receipt, protocol or source layout is reconstructed. -/
def detail (env : Environment) (registered : Std.HashSet Name) (properties : Std.HashSet Name)
    (info : ConstantInfo) : MetaM Json := do
  let statement ← ppExpr info.type
  let premiseText ← forallTelescope info.type fun binders _ =>
    binders.mapM fun binder => do
      return Json.str (toString (← ppExpr (← binder.fvarId!.getDecl).type))
  let (typeHead, typeArguments, property) ← forallTelescope info.type fun _ body => do
    let head := headName body
    let property ← if head.any properties.contains then do
        match ← unfoldDefinition? body with
        | some unfolded => pure (Json.mkObj [
            ("statement", Json.str (toString (← ppExpr unfolded))),
            ("premise_telescope", Json.arr ((← premises unfolded).map premiseJson))])
        | none => pure Json.null
      else pure Json.null
    return (head, ← argumentsJson body, property)
  let (valueHead, valueArguments) ← match info.value? (allowOpaque := true) with
    | some value => lambdaTelescope value fun _ body =>
        return (headName body, ← argumentsJson body)
    | none => pure (none, Json.null)
  return Json.mkObj [("statement", Json.str (toString statement)),
    ("premises", Json.arr premiseText),
    ("premise_telescope", Json.arr ((← premises info.type).map premiseJson)),
    ("binders", ← bindersJson info.type),
    ("type_head", nameJson typeHead), ("type_arguments", typeArguments),
    ("value_head", nameJson valueHead), ("value_arguments", valueArguments),
    ("property", property),
    ("registered", Json.arr ((reached env registered info.name).map (Json.str ·.toString)))]

def record (env : Environment) (registered : Std.HashSet Name) (properties : Std.HashSet Name) (name : Name)
    (info : ConstantInfo) (module : Name) (actualAxioms : Array Name) (detailed : Bool) : MetaM Json := do
  let axioms := actualAxioms.qsort Name.lt |>.map (Json.str ·.toString)
  let doc ← findSimpleDocString? env name (includeBuiltin := false)
  let mut fields : List (String × Json) := [
    ("name", Json.str (privateToUserName? name |>.getD name).toString),
    ("module", Json.str module.toString),
    ("kind", Json.str (kind info)),
    ("statement", Json.mkObj [("structural", Json.str (hex (structuralHash info.type))),
      ("explicit", Json.str (hex (explicitHash env info.type)))]),
    ("axioms", Json.arr axioms),
    ("doc", match doc with | some text => Json.str text | none => Json.null),
    ("tags", Json.arr ((tags env name info).map Json.str))]
  if info.isTheorem then
    fields := fields ++ [("premises", Json.arr ((← premises info.type).map premiseJson))]
  if detailed then
    fields := fields ++ [("detail", ← detail env registered properties info)]
  return Json.mkObj fields

def runMeta {α : Type} (env : Environment) (action : MetaM α) : IO α := do
  -- Nested generated requests need more depth than the elaborator's default.
  -- Keep this finite metadata budget in both options and Core.Context so
  -- pretty printing through `withOptions` does not reset it to 512.
  let options := Lean.maxRecDepth.set {} 4096
  let context : Core.Context :=
    { fileName := "<declaration records>", fileMap := default, maxHeartbeats := 0,
      options, maxRecDepth := Lean.maxRecDepth.get options }
  let (result, _, _) ← action.toIO context { env }
  return result

/-- The JSON `name` of a record line, used to name differences. -/
def lineName (line : String) : String :=
  match Json.parse line with
  | .ok json => match json.getObjValAs? String "name", json.getObjValAs? String "module" with
    | .ok name, .ok module => s!"{name} ({module})"
    | _, _ => (line.take 80).toString
  | .error _ => (line.take 80).toString

/-- Name the declarations whose records differ between two outputs. -/
def differences (expected actual : Array String) : Array String := Id.run do
  let key := fun (line : String) => lineName line
  let expectedSet : Std.HashSet String := Std.HashSet.ofArray expected
  let actualSet : Std.HashSet String := Std.HashSet.ofArray actual
  let expectedKeys : Std.HashSet String := Std.HashSet.ofArray (expected.map key)
  let actualKeys : Std.HashSet String := Std.HashSet.ofArray (actual.map key)
  let mut found := #[]
  for line in actual do
    unless expectedSet.contains line do
      found := found.push ((if expectedKeys.contains (key line) then "changed: " else "added: ") ++ key line)
  for line in expected do
    unless actualSet.contains line || actualKeys.contains (key line) do
      found := found.push ("removed: " ++ key line)
  return found

end DeclarationRecords

open DeclarationRecords in
unsafe def main (arguments : List String) : IO UInt32 := do
  let options ← match parse arguments {} with
    | .ok options => pure options
    | .error message => IO.eprintln message; return 2
  let usage := "usage: DeclarationRecords [--check BASELINE] [--registry NAME] [--endpoints NAME] " ++
    "[--detail NAME]... [--trace-records] OUTPUT DIRECTORY..."
  let some output := options.positional[0]?
    | IO.eprintln usage; return 2
  let directories := options.positional.extract 1
  if directories.isEmpty then
    IO.eprintln "no directories selected"; return 2
  let mut modules := #[]
  let mut families := #[]
  for directory in directories do
    let path : System.FilePath := directory
    let found ← if path.extension == some "lean" then
        pure #[(path.withExtension "").components.foldl Name.str Name.anonymous]
      else modulesBelow path
    if found.isEmpty then
      IO.eprintln s!"no modules below {directory}"; return 2
    modules := modules ++ found
    families := families.push ((path.withExtension "").components.foldl Name.str Name.anonymous)
  let started ← IO.monoMsNow
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.qsort Name.lt |>.map fun module => { module, importAll := true }) {}
    (loadExts := true) (arts := ← ZkcTools.ImportArtifacts.collect)
  let imported ← IO.monoMsNow
  IO.eprintln s!"declaration-records: import {imported - started}ms"
  let moduleOf := fun (name : Name) => Id.run do
    let some index := env.getModuleIdxFor? name | return none
    let some module := env.header.modules[index.toNat]? | return none
    return if families.any (·.isPrefixOf module.module) then some module.module else none
  let sources := providers env
  let owners := resolvedOwners env
  let indexed ← IO.monoMsNow
  IO.eprintln s!"declaration-records: providers {indexed - imported}ms"
  let mut provenanceCache : DeclarationRecords.Cache := {}
  let mut checkedAxioms : Std.HashMap Name (Array Name) := {}
  let mut auditRoots := options.details
  if let some name := options.registry then auditRoots := auditRoots.push name
  if let some name := options.endpoints then auditRoots := auditRoots.push name
  for index in [:env.header.modules.size] do
    let owner := env.header.modules[index]!.module
    unless families.any (·.isPrefixOf owner) do continue
    for info in env.header.moduleData[index]!.constants do
      auditRoots := auditRoots.push info.name
  for name in auditRoots do
    let some info := env.find? name | continue
    let (axioms, updated) ← storedAxioms env sources owners {} info provenanceCache
    provenanceCache := updated
    checkedAxioms := checkedAxioms.insert name axioms
  let audited ← IO.monoMsNow
  IO.eprintln s!"declaration-records: stored proof audit {audited - indexed}ms"
  for name in options.details do
    unless env.contains name do
      IO.eprintln s!"detailed declaration is not in the selected modules: {name}"
      return 1
  let mut registry := Json.null
  let mut registered : Std.HashSet Name := {}
  if let some name := options.registry then
    unless env.contains name do
      IO.eprintln s!"registry table is missing: {name}"; return 1
    let table ← IO.ofExcept (env.evalConst (List (String × String × Option Name × String)) {} name)
    registry := Json.arr <| table.toArray.map fun (identifier, category, schema, statement) =>
      Json.mkObj [("identifier", Json.str identifier), ("category", Json.str category),
        ("schema", match schema with | some schema => Json.str schema.toString | none => Json.null),
        ("statement", Json.str statement)]
    for (_, _, schema, _) in table do
      if let some schema := schema then
        registered := registered.insert schema
        if let some info := env.find? schema then
          let (_, updated) ← storedAxioms env sources owners {} info provenanceCache
          provenanceCache := updated
  let mut endpoints := Json.null
  let mut endpointTheorems : Array Name := #[]
  if let some name := options.endpoints then
    unless env.contains name do
      IO.eprintln s!"endpoint table is missing: {name}"; return 1
    let table ← IO.ofExcept (env.evalConst (List (String × String × String × Name)) {} name)
    endpoints := Json.arr <| table.toArray.map fun (endpoint, property, statement, target) =>
      Json.mkObj [("endpoint", Json.str endpoint), ("property", Json.str property),
        ("statement", Json.str statement), ("theorem", Json.str target.toString)]
    for (_, _, _, target) in table do
      registered := registered.insert target
      endpointTheorems := endpointTheorems.push target
      if let some info := env.find? target then
        let (_, updated) ← storedAxioms env sources owners {} info provenanceCache
        provenanceCache := updated
  -- The registered properties: the heads of the endpoint theorems' statements.
  let mut properties : Std.HashSet Name := {}
  for target in endpointTheorems do
    if let some info := env.find? target then
      if let some head ← runMeta env (forallTelescope info.type fun _ body => pure (headName body)) then
        properties := properties.insert head
  let mut selected : Array (String × Name × Name × ConstantInfo) := #[]
  for (name, info) in env.constants.map₁.toList do
    let some module := moduleOf name | continue
    if (privateToUserName? name |>.getD name).isInternal then continue
    if (declRangeExt.find? env name).isNone then continue
    if isAuxRecursor env name || isNoConfusion env name then continue
    if info matches .recInfo _ then continue
    selected := selected.push ((privateToUserName? name |>.getD name).toString, module, name, info)
  let sorted := selected.qsort fun (left, leftModule, _, _) (right, rightModule, _, _) =>
    left < right || (left == right && leftModule.toString < rightModule.toString)
  let header := Json.mkObj [
    ("format", Json.str "zkc.declarations/0"),
    ("toolchain", Json.str Lean.versionString),
    ("axiom_provenance", Json.str "resolved-constant-info/0"),
    ("reference_provenance", Json.str "checked-stored-module/0"),
    ("families", Json.arr (families.map (Json.str ·.toString))),
    ("modules", toJson modules.size),
    ("declarations", toJson sorted.size),
    ("registry", registry),
    ("endpoints", endpoints)]
  let mut lines := #[header.compress]
  for (_, module, name, info) in sorted do
    try
      let recordStarted ← IO.monoMsNow
      if options.traceRecords then IO.eprintln s!"declaration-records: start {name}"
      let detailed := options.details.contains name || endpointTheorems.contains name
      let some actualAxioms := checkedAxioms[name]?
        | throw <| IO.userError s!"selected declaration was not provenance audited: {name}"
      let json ← runMeta env (record env registered properties name info module actualAxioms detailed)
      lines := lines.push json.compress
      if options.traceRecords then
        IO.eprintln s!"declaration-records: done {name} {(← IO.monoMsNow) - recordStarted}ms"
    catch error =>
      throw <| IO.userError s!"declaration record {name}: {error}"
  IO.FS.writeFile output (String.intercalate "\n" lines.toList ++ "\n")
  IO.eprintln s!"declaration-records: records and output {(← IO.monoMsNow) - audited}ms"
  IO.println s!"{sorted.size} declarations from {modules.size} modules"
  if let some baseline := options.check then
    let expected := ((← IO.FS.readFile baseline).splitOn "\n").toArray.filter (· ≠ "")
    let found := differences expected lines
    if !found.isEmpty then
      for line in found.toList.take 50 do IO.eprintln line
      IO.eprintln s!"{found.size} declaration records differ from {baseline}"
      return 1
    IO.println s!"records agree with {baseline}"
  return 0
