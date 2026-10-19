import ZkcTools.DeclarationAudit

/-! Declaration records for package-owned code.

Writes one JSON line per declaration written in the source of the selected
module families, sorted by name and module, after a header line. A record
states the declaration's name, module and kind, its structural and explicit
statement hashes (`ZkcTools.Statements` in `ZkcTools.DeclarationAudit`), its axiom closure (Lean's transitive
`collectAxioms`, opaque proof bodies included), its docstring, structural tags
and, for theorems, its premise telescope: every leading binder, implicit and
instance binders included, with whether it is a premise and the head constant
of the premise's proposition. Declarations that Lean generates (recursors,
matchers, equation and injectivity lemmas, auxiliary proofs) carry no source
range and are omitted; the declaration audit still covers them.

Run after building the selected packages, from the package directory:

```sh
lake env lean --run ../checks/DeclarationRecords.lean [OPTION]... OUTPUT DIRECTORY...
```

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
  of covered endpoint, property, statement form and theorem, and record it in
  the header.
- `--detail NAME`: also record the pretty-printed statement and premises of the
  declaration `NAME`, its premise telescope whatever its kind, and the
  registered constants (registry schemas and endpoints) it reaches through
  repository declarations (repeatable); a missing declaration is an error.

The output is deterministic for a fixed toolchain and fixed sources. Equal
statement hashes are regression evidence, not semantic preservation. -/

open Lean Meta ZkcTools.Statements

namespace DeclarationRecords

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

partial def parse : List String → Options → Except String Options
  | [], options => .ok options
  | "--check" :: path :: rest, options => parse rest { options with check := some path }
  | "--registry" :: name :: rest, options => parse rest { options with registry := some name.toName }
  | "--endpoints" :: name :: rest, options => parse rest { options with endpoints := some name.toName }
  | "--detail" :: name :: rest, options =>
      parse rest { options with details := options.details.push name.toName }
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
  [`Zkc, `ZkcExamples, `ZkcTools, `ZkcSecurity, `ZkcClean, `Tests, `TestsSecurity, `TestsClean]

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

/-- Pretty-printed statement and premises of one declaration, and the
registered constants it reaches. -/
def detail (env : Environment) (registered : Std.HashSet Name) (info : ConstantInfo) : MetaM Json := do
  let statement ← ppExpr info.type
  let premiseText ← forallTelescope info.type fun binders _ => do
    binders.mapM fun binder => do
      let declaration ← binder.fvarId!.getDecl
      return Json.str (toString (← ppExpr declaration.type))
  return Json.mkObj [("statement", Json.str (toString statement)),
    ("premises", Json.arr premiseText),
    ("premise_telescope", Json.arr ((← premises info.type).map premiseJson)),
    ("registered", Json.arr ((reached env registered info.name).map (Json.str ·.toString)))]

def record (env : Environment) (registered : Std.HashSet Name) (name : Name) (info : ConstantInfo)
    (module : Name) (detailed : Bool) : MetaM Json := do
  let axioms := (← collectAxioms name).qsort Name.lt |>.map (Json.str ·.toString)
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
    fields := fields ++ [("detail", ← detail env registered info)]
  return Json.mkObj fields

def runMeta {α : Type} (env : Environment) (action : MetaM α) : IO α := do
  let context : Core.Context :=
    { fileName := "<declaration records>", fileMap := default, maxHeartbeats := 0 }
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
    "[--detail NAME]... OUTPUT DIRECTORY..."
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
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.qsort Name.lt |>.map fun module => { module, importAll := true }) {}
    (loadExts := true)
  let moduleOf := fun (name : Name) => Id.run do
    let some index := env.getModuleIdxFor? name | return none
    let some module := env.header.modules[index.toNat]? | return none
    return if families.any (·.isPrefixOf module.module) then some module.module else none
  for name in options.details do
    unless env.contains name do
      IO.eprintln s!"detailed declaration is missing: {name}"; return 1
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
      if let some schema := schema then registered := registered.insert schema
  let mut endpoints := Json.null
  if let some name := options.endpoints then
    unless env.contains name do
      IO.eprintln s!"endpoint table is missing: {name}"; return 1
    let table ← IO.ofExcept (env.evalConst (List (String × String × String × Name)) {} name)
    endpoints := Json.arr <| table.toArray.map fun (endpoint, property, statement, target) =>
      Json.mkObj [("endpoint", Json.str endpoint), ("property", Json.str property),
        ("statement", Json.str statement), ("theorem", Json.str target.toString)]
    for (_, _, _, target) in table do registered := registered.insert target
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
    ("families", Json.arr (families.map (Json.str ·.toString))),
    ("modules", toJson modules.size),
    ("declarations", toJson sorted.size),
    ("registry", registry),
    ("endpoints", endpoints)]
  let mut lines := #[header.compress]
  for (_, module, name, info) in sorted do
    let json ← runMeta env (record env registered name info module (options.details.contains name))
    lines := lines.push json.compress
  IO.FS.writeFile output (String.intercalate "\n" lines.toList ++ "\n")
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
