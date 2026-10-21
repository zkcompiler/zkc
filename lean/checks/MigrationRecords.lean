import ZkcTools.DeclarationAudit

/-! Exact structural records for a semantic migration.

Unlike statement hashes, these records retain every binder, universe and
referenced definition body in the selected stored module versions. Metadata and
binder names are omitted; binder visibility and all semantic expression nodes
are retained. Equal records are regression evidence. An intentional semantic
change still needs a checked correspondence theorem.

Run with an output path followed by one exact module name. Use
`check_migration.py --capture-from PACKAGE --capture-modules MODULES.json
--output RECORDS.jsonl` for multiple modules, each in its own process. A package's dependency
pins and source inventory must accompany the records. The emitter does not
silently replace a missing selected module with an empty inventory.
-/

open Lean Meta
namespace MigrationRecords

private def node (tag : String) (args : List Json := []) : Json :=
  Json.arr (Json.str tag :: args).toArray

-- A JSON string containing tagged kernel components, rooted at anonymous.
-- Name.toString is diagnostic only: even string and numeric components can
-- have the same display spelling. Keep keys usable in explicit JSON maps.
private def nameComponents : Name → List Json
  | .anonymous => []
  | .str parent value => nameComponents parent ++ [node "str" [toJson value]]
  | .num parent value => nameComponents parent ++ [node "num" [toJson value]]

private def nameKey (name : Name) : String :=
  (toJson (nameComponents name)).compress

private def semanticName (name : Name) : Json := toJson (nameKey name)

private partial def level : Level → Json
  | .zero => node "zero"
  | .succ x => node "succ" [level x]
  | .max x y => node "max" [level x, level y]
  | .imax x y => node "imax" [level x, level y]
  | .param name => node "parameter" [semanticName name]
  | .mvar name => node "metavariable" [semanticName name.name]

private partial def expression : Expr → Json
  | .bvar index => node "bound" [toJson index]
  | .fvar id => node "free" [semanticName id.name]
  | .mvar id => node "metavariable" [semanticName id.name]
  | .sort u => node "sort" [level u]
  | .const name levels => node "constant" [semanticName name, toJson (levels.map level)]
  | .app f x => node "application" [expression f, expression x]
  | .lam _ type body binder => node "lambda"
      [Json.str (ZkcTools.Statements.binderName binder), expression type, expression body]
  | .forallE _ type body binder => node "forall"
      [Json.str (ZkcTools.Statements.binderName binder), expression type, expression body]
  | .letE _ type value body nondependent => node "let"
      [expression type, expression value, expression body, toJson nondependent]
  | .lit (.natVal value) => node "natural" [toJson value]
  | .lit (.strVal value) => node "string" [toJson value]
  | .mdata _ inner => expression inner
  | .proj owner index inner => node "projection"
      [semanticName owner, toJson index, expression inner]

private def names (values : List Name) : Json := toJson (values.map nameKey)

private def hints : ReducibilityHints → Json
  | .opaque => node "opaque"
  | .abbrev => node "abbreviation"
  | .regular height => node "regular" [toJson height.toNat]

private def shape : ConstantInfo → Json
  | .inductInfo value => Json.mkObj [
      ("parameters", toJson value.numParams), ("indices", toJson value.numIndices),
      ("mutual", names value.all), ("constructors", names value.ctors),
      ("nested", toJson value.numNested), ("recursive", toJson value.isRec),
      ("unsafe", toJson value.isUnsafe), ("reflexive", toJson value.isReflexive)]
  | .ctorInfo value => Json.mkObj [
      ("inductive", semanticName value.induct), ("index", toJson value.cidx),
      ("parameters", toJson value.numParams), ("fields", toJson value.numFields),
      ("unsafe", toJson value.isUnsafe)]
  | .recInfo value => Json.mkObj [
      ("mutual", names value.all), ("parameters", toJson value.numParams),
      ("indices", toJson value.numIndices), ("motives", toJson value.numMotives),
      ("minors", toJson value.numMinors), ("k", toJson value.k),
      ("unsafe", toJson value.isUnsafe),
      ("rules", toJson (value.rules.map fun rule => Json.mkObj [
        ("constructor", semanticName rule.ctor), ("fields", toJson rule.nfields),
        ("rhs", expression rule.rhs)]))]
  | .defnInfo value => Json.mkObj [("safety", toJson (reprStr value.safety)),
      ("hints", hints value.hints)]
  | .opaqueInfo value => Json.mkObj [("unsafe", toJson value.isUnsafe)]
  | .axiomInfo value => Json.mkObj [("unsafe", toJson value.isUnsafe)]
  | _ => Json.null

private def record (info : ConstantInfo) (owner : Name) (axioms : Array Name)
    (references : Json) : Json :=
  Json.mkObj [
    ("name", semanticName info.name), ("display_name", Json.str info.name.toString),
    ("module", Json.str owner.toString), ("references", references),
    ("kind", Json.str (ZkcTools.Statements.kind info)),
    ("universes", names info.levelParams), ("type", expression info.type),
    ("body", if info.isTheorem then Json.null else
      (info.value? true).map expression |>.getD Json.null),
    ("shape", shape info),
    ("axioms", names (axioms.qsort Name.lt |>.toList)),
    ("type_dependencies", names (info.type.getUsedConstants.qsort Name.lt |>.toList)),
    ("body_dependencies", toJson ((info.value? true).map Expr.getUsedConstants |>.getD #[]
      |>.qsort Name.lt |>.toList.map nameKey))]

/-- Compare complete stored values, including theorem proofs. Only identical
versions may share a provider class; definitional equality/proof irrelevance
must not collapse different proofs or their axiom dependencies. -/
private def sameStored : ConstantInfo → ConstantInfo → Bool
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

private abbrev Providers := Std.HashMap Name (Option (Name × ConstantInfo))

/-- Lean can store identical generated declarations in several modules. Admit
these only after comparing all stored fields (proof bodies included), choosing
the least module Name as a deterministic representative. Differing versions are
ambiguous even if Lean's merged map happens to prefer one. -/
private def providers (env : Environment) : Providers := Id.run do
  let mut found : Providers := {}
  for index in [:env.header.modules.size] do
    let owner := env.header.modules[index]!.module
    for info in env.header.moduleData[index]!.constants do
      let value := match found[info.name]? with
        | none => some (owner, info)
        | some none => none
        | some (some (previous, stored)) =>
          if sameStored stored info then some (if Name.lt owner previous then owner else previous, stored)
          else none
      found := found.insert info.name value
  return found

private def provider (sources : Providers) (name : Name) : IO Name := do
  match sources[name]? with
  | some (some (owner, _)) => return owner
  | some none => throw <| IO.userError s!"ambiguous stored providers for dependency: {name}"
  | none => throw <| IO.userError s!"uncovered stored dependency: {name}"

private def dependencies (info : ConstantInfo) : Array Name := Id.run do
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

private structure Cache where
  edges : Std.HashMap Name (Array Name) := {}
  closed : Std.HashMap Name (Array Name) := {}

/-- Traverse actual resolved ConstantInfo bodies, including opaque proofs.
Never consult collectAxioms' imported extension. Only a fully traversed root is
cached; a cycle sentinel is never published as an axiom closure. If the complete
closure is empty, every visited subclosure is empty too and can safely be cached.
The edge and completed-closure caches belong to this one environment. -/
private def storedAxioms (env : Environment) (sources : Providers)
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

private def moduleRecords (env : Environment) (owner : Name) : IO (Array String) := do
  let some index := env.header.modules.findIdx? (·.module == owner)
    | throw <| IO.userError s!"missing module: {owner}"
  let declarations := env.header.moduleData[index]!.constants
  let sources := providers env
  let mut owned : Std.HashMap Name ConstantInfo := {}
  for info in declarations do
    let _ ← provider sources info.name
    if owned.contains info.name then
      throw <| IO.userError s!"duplicate stored declaration: {owner}: {info.name}"
    owned := owned.insert info.name info
  let mut cache : Cache := {}
  let mut rows := #[]
  for info in declarations.qsort (fun a b => Name.lt a.name b.name) do
    let (axioms, updated) ← storedAxioms env sources owned info cache
    cache := updated
    let refs := (dependencies info ++ axioms).push info.name
    let mut seen : Std.HashSet Name := {}
    let mut provenance := []
    for name in refs.qsort Name.lt do
      if seen.contains name then continue
      seen := seen.insert name
      let representative ← provider sources name
      provenance := provenance ++ [(nameKey name, semanticName (if name == info.name then owner else representative))]
    rows := rows.push (record info owner axioms (Json.mkObj provenance)).compress
  return rows

end MigrationRecords

open MigrationRecords in
unsafe def main (args : List String) : IO UInt32 := do
  let [output, selected] := args
    | IO.eprintln "expected OUTPUT MODULE (use check_migration.py for isolated multi-module capture)"; return 2
  let owner := selected.toName
  unless owner.toString == selected do
    IO.eprintln "module selection must round-trip through its kernel name"; return 2
  initSearchPath (← findSysroot)
  enableInitializersExecution
  -- One loaded environment per process. Loaded extension state may retain
  -- imported region references, so freeRegions is not safe here.
  let env ← importModules #[{ module := owner, importAll := true }] {} (loadExts := true)
  let rows ← moduleRecords env owner
  IO.FS.withFile output .write fun handle => do
    handle.putStrLn (Json.mkObj [
      ("format", toJson "zkc.migration-declarations/0"),
      ("name_encoding", toJson "lean-name-components/0"),
      ("axiom_provenance", toJson "resolved-constant-info/0"),
      ("reference_provenance", toJson "checked-stored-module/0"),
      ("modules", toJson [selected]), ("declarations", toJson rows.size)]).compress
    for row in rows do handle.putStrLn row
  return 0
