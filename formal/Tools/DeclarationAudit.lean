import Lean

/-! Kernel assumption and declaration dependency checks for package-owned code.
Module ownership, rather than declaration spelling, also covers private helpers,
generated declarations and declarations added to an existing namespace.
Each stored module version is inspected: Lean can realize equivalent equation
proofs lazily in several modules, so merged ownership and proof bodies alone
do not reliably identify dependency provenance.
-/

set_option autoImplicit false

namespace Tools.DeclarationAudit
open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def moduleOf (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  (env.header.modules[index.toNat]?).map (·.module)

def below (base name : Name) : Bool := base.isPrefixOf name

/-- Implementation dependencies of the generic library cannot enter protocol
applications or downstream clients. Probability also excludes source/compiler
syntax. External theorem ecosystems belong only to the optional package. -/
def permitted (owner dependency : Name) : Bool := Id.run do
  if below `Zkc owner then
    if [ `Tests, `TestsArkLib, `Examples, `Tools, `ZkcArkLib,
         `ArkLib, `VCVio, `PolyFun ].any (below · dependency) then return false
    if !below `Zkc.Protocols owner && below `Zkc.Protocols dependency then return false
    if [ `Zkc.Modules, `Zkc.Source ].any (below · owner) &&
        below `Zkc.Compiler dependency then return false
    if below `Zkc.Probability owner &&
        [ `Zkc.Source, `Zkc.Compiler ].any (below · dependency) then return false
  if below `ZkcArkLib owner &&
      [ `Tests, `TestsArkLib, `Examples, `Tools ].any (below · dependency) then return false
  return true

abbrev Graph := Std.HashMap Name (Array Name)

/-- Compute the finite closure, including cycles between mutually defined
declarations. Edges conservatively combine all declarations of each module. -/
partial def closure (graph : Graph) (pending : List Name)
    (seen : Std.HashSet Name := {}) : Std.HashSet Name :=
  match pending with
  | [] => seen
  | name :: rest =>
      if seen.contains name then closure graph rest seen
      else closure graph ((graph[name]?.getD #[]).toList ++ rest) (seen.insert name)

/-- Audit every declaration owned by the selected imported module families.
Types and proof/definition bodies are inspected separately. The dependency
closure is conservative at module granularity; axiom collection is Lean's
transitive declaration-level check, including opaque proof bodies.
`exactModules` selects individual modules instead of families; `marker` identifies
the validation scope in build receipts.

A family is a module name, never a namespace: selection compares against the
module a declaration came from. A module is also not in its own environment
while it elaborates, so a file cannot audit itself -- what it owns is covered
by an audit run from a module that imports it. A family matching nothing is an
error rather than a pass with a smaller count, because six invocations here
named a namespace or their own module and reported a pass over nothing. -/
def check (families : List Name) (marker : String := "AUDIT-PASS")
    (exactModules : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  let mut graph : Graph := {}
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut typeReferences : Nat := 0
  let mut valueReferences : Nat := 0
  let mut audited : Std.HashSet Name := {}
  let mut names : Std.HashSet Name := {}
  let mut matched : Std.HashSet Name := {}
  for index in [:env.header.moduleData.size] do
    let owner := env.header.modules[index]!.module
    let selected := families.filter (fun family =>
      if exactModules then family == owner else below family owner)
    if selected.isEmpty then continue
    for family in selected do
      matched := matched.insert family
    let data := env.header.moduleData[index]!
    let localNames : Std.HashSet Name := Std.HashSet.ofArray data.constNames
    for info in data.constants do
      let name := info.name
      names := names.insert name
      declarations := declarations + 1
      if info.isTheorem then theorems := theorems + 1
      if info matches .axiomInfo _ then
        unless allowedAxioms.contains name do
          throwError "unexpected owned axiom: {name} in {owner}"
      let types := info.type.getUsedConstants
      let values := (info.value? true).map Expr.getUsedConstants |>.getD #[]
      typeReferences := typeReferences + types.size
      valueReferences := valueReferences + values.size
      -- Inspect every stored version of a lazily realized equation theorem.
      -- A merged Environment can retain one module's owner index and another
      -- module's equivalent proof body. ModuleData keeps their provenance paired.
      for reference in (types ++ values).push name do
        if !audited.contains reference then
          audited := audited.insert reference
          for axiomName in ← Lean.collectAxioms reference do
            unless allowedAxioms.contains axiomName do
              throwError "unexpected axiom: {name} uses {reference}, which depends on {axiomName}"
      for (kind, references) in [("type", types), ("body", values)] do
        for dependency in references do
          let dependencyOwner? :=
            if localNames.contains dependency then some owner else moduleOf env dependency
          let some dependencyOwner := dependencyOwner? | continue
          unless permitted owner dependencyOwner do
            throwError "forbidden {kind} dependency: {name} in {owner} uses {dependency} from {dependencyOwner}"
          let edges := graph[owner]?.getD #[]
          if !edges.contains dependencyOwner then
            graph := graph.insert owner (edges.push dependencyOwner)
  for (owner, edges) in graph.toList do
    for dependency in (closure graph edges.toList).toList do
      unless permitted owner dependency do
        throwError "forbidden transitive declaration dependency: {owner} reaches {dependency}"
  -- A family that selected no module audits nothing and would still report a
  -- pass, so the count would name a scope wider than the one examined. The
  -- usual cause is a namespace where a module name belongs.
  for family in families do
    unless matched.contains family do
      throwError "{family} selected no module: audits name modules, not namespaces"
  logInfo m!"{marker} declarations={declarations} theorems={theorems}"
  logInfo m!"DECLARATION-VERSIONS total={declarations} distinct-names={names.size}"
  logInfo m!"DEPENDENCY-AUDIT-PASS modules={graph.size} type-references={typeReferences} body-references={valueReferences}"

end Tools.DeclarationAudit
