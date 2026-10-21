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

private def record (info : ConstantInfo) (owner : Name) (axioms : Array Name) : Json :=
  Json.mkObj [
    ("name", semanticName info.name), ("display_name", Json.str info.name.toString),
    ("module", Json.str owner.toString),
    ("kind", Json.str (ZkcTools.Statements.kind info)),
    ("universes", names info.levelParams), ("type", expression info.type),
    ("body", if info.isTheorem then Json.null else
      (info.value? true).map expression |>.getD Json.null),
    ("shape", shape info),
    ("axioms", names (axioms.qsort Name.lt |>.toList)),
    ("type_dependencies", names (info.type.getUsedConstants.qsort Name.lt |>.toList)),
    ("body_dependencies", toJson ((info.value? true).map Expr.getUsedConstants |>.getD #[]
      |>.qsort Name.lt |>.toList.map nameKey))]

private abbrev AxiomCache := Std.HashMap Name (Array Name)

/-- Start at the actual stored declaration, never at a merged version of its
name. Owned dependencies use this module's stored versions too. Imported
closures come from Lean's module-specific axiom extension in an environment
that imports only the owning module. The cache must not outlive that environment.

Only imported closures are memoized. A fresh visited set for each owned root
keeps mutually recursive declarations from caching an incomplete closure. -/
private def storedAxioms (env : Environment) (owned : Std.HashMap Name ConstantInfo)
    (root : ConstantInfo) (cache : AxiomCache) : IO (Array Name × AxiomCache) := do
  let mut cache := cache
  let mut pending := #[root]
  let mut visited : Std.HashSet Name := {}
  let mut axioms : Std.HashSet Name := {}
  while !pending.isEmpty do
    let info := pending.back!
    pending := pending.pop
    if visited.contains info.name then continue
    visited := visited.insert info.name
    if info matches .axiomInfo _ then axioms := axioms.insert info.name
    let mut refs := info.type.getUsedConstants ++
      ((info.value? true).map Expr.getUsedConstants |>.getD #[])
    if let .inductInfo value := info then refs := refs ++ value.ctors.toArray
    for name in refs do
      if let some dependency := owned[name]? then
        pending := pending.push dependency
      else
        unless (env.find? name).isSome do
          throw <| IO.userError s!"unresolved dependency: {info.name} uses {name}"
        let found ← match cache[name]? with
          | some cached => pure cached
          | none => do
            let action : MetaM (Array Name) := collectAxioms name
            let (value, _, _) ← action.toIO
              { fileName := "<migration records>", fileMap := default, maxHeartbeats := 0 } { env }
            cache := cache.insert name value
            pure value
        for name in found do axioms := axioms.insert name
  return (axioms.toArray, cache)

private def moduleRecords (env : Environment) (owner : Name) : IO (Array String) := do
  let some index := env.header.modules.findIdx? (·.module == owner)
    | throw <| IO.userError s!"missing module: {owner}"
  let declarations := env.header.moduleData[index]!.constants
  let mut owned : Std.HashMap Name ConstantInfo := {}
  for info in declarations do
    if owned.contains info.name then
      throw <| IO.userError s!"duplicate stored declaration: {owner}: {info.name}"
    owned := owned.insert info.name info
  let mut cache : AxiomCache := {}
  let mut rows := #[]
  for info in declarations.qsort (fun a b => Name.lt a.name b.name) do
    let (axioms, updated) ← storedAxioms env owned info cache
    cache := updated
    rows := rows.push (record info owner axioms).compress
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
      ("axiom_provenance", toJson "owning-module-environment/0"),
      ("modules", toJson [selected]), ("declarations", toJson rows.size)]).compress
    for row in rows do handle.putStrLn row
  return 0
