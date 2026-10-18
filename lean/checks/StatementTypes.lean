import Lean

/-! Statement-type report for package-owned declarations.

Prints one line `name<TAB>kind<TAB>type hash<TAB>explicit hash` for every
theorem, definition, inductive type and constructor written in the source of the
selected module families, sorted by name. The type hash is a structural hash of
the elaborated type: it does not unfold definitions, so a statement keeps its
hash when only the bodies of the definitions it mentions change. The explicit
hash omits the implicit and instance arguments of applied constants, as the
statement's text does: a declaration whose type hash changes while its explicit
hash stays has the same text, and only an inferred argument of a constant it
mentions changed. Binder types of the statement itself are always hashed in
full. Declarations that Lean generates (recursors, matchers, equation and
injectivity lemmas, auxiliary proofs) carry no source range and are omitted.

Run after building the selected packages, from the package directory:

```sh
lake env lean --run ../checks/StatementTypes.lean OUTPUT DIRECTORY...
```

Each `DIRECTORY` is a source directory or a single `.lean` file relative to the
current directory, such as `Zkc` or `ZkcTools/JsonSupport.lean`; every module
below it is imported and selected. Executable roots, which each define `main`,
cannot be imported together and are selected by their library directories.
Compare two reports with `diff` to list declarations whose statements changed.
This is a change report for refactorings, not an admission check. -/

open Lean

namespace StatementTypes

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

/-- Structural hash of an expression, ignoring binder names, binder
information and metadata. Constants are hashed by name and universe levels. -/
partial def structuralHash : Expr → UInt64
  | .bvar index => mixHash 1 (hash index)
  | .fvar id => mixHash 2 (hash id.name)
  | .mvar id => mixHash 3 (hash id.name)
  | .sort level => mixHash 4 (hash level)
  | .const name levels => mixHash 5 (mixHash (hash name) (hash levels))
  | .app function argument => mixHash 6 (mixHash (structuralHash function) (structuralHash argument))
  | .lam _ type body _ => mixHash 7 (mixHash (structuralHash type) (structuralHash body))
  | .forallE _ type body _ => mixHash 8 (mixHash (structuralHash type) (structuralHash body))
  | .letE _ type value body _ =>
      mixHash 9 (mixHash (structuralHash type) (mixHash (structuralHash value) (structuralHash body)))
  | .lit (.natVal value) => mixHash 10 (hash value)
  | .lit (.strVal value) => mixHash 11 (hash value)
  | .mdata _ inner => structuralHash inner
  | .proj owner index inner => mixHash 12 (mixHash (hash owner) (mixHash (hash index) (structuralHash inner)))

/-- Binder information of the leading binders of a constant's type. -/
def binderInfos (env : Environment) (name : Name) : Array BinderInfo := Id.run do
  let some info := env.find? name | return #[]
  let mut type := info.type
  let mut found := #[]
  while true do
    match type with
    | .forallE _ _ body binder => found := found.push binder; type := body
    | .mdata _ inner => type := inner
    | _ => break
  return found

/-- Structural hash that skips the implicit, strict-implicit and instance
arguments of applied constants. -/
partial def explicitHash (env : Environment) (expression : Expr) : UInt64 :=
  match expression with
  | .app .. =>
    let function := expression.getAppFn
    let arguments := expression.getAppArgs
    match function with
    | .const name levels =>
      let binders := binderInfos env name
      let kept := arguments.zipIdx.filterMap fun (argument, position) =>
        if (binders[position]?.getD .default).isExplicit then some argument else none
      kept.foldl (fun state argument => mixHash 6 (mixHash state (explicitHash env argument)))
        (mixHash 5 (mixHash (hash name) (hash levels)))
    | _ => arguments.foldl (fun state argument => mixHash 6 (mixHash state (explicitHash env argument)))
        (explicitHash env function)
  | .lam _ type body _ => mixHash 7 (mixHash (explicitHash env type) (explicitHash env body))
  | .forallE _ type body _ => mixHash 8 (mixHash (explicitHash env type) (explicitHash env body))
  | .letE _ type value body _ =>
      mixHash 9 (mixHash (explicitHash env type) (mixHash (explicitHash env value) (explicitHash env body)))
  | .mdata _ inner => explicitHash env inner
  | .proj owner index inner => mixHash 12 (mixHash (hash owner) (mixHash (hash index) (explicitHash env inner)))
  | other => structuralHash other

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

end StatementTypes

open StatementTypes in
unsafe def main (arguments : List String) : IO UInt32 := do
  let output :: directories := arguments
    | IO.eprintln "usage: StatementTypes OUTPUT DIRECTORY..."; return 2
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
  let env ← importModules (modules.map fun module => { module, importAll := true }) {}
    (loadExts := true)
  let selected := fun (name : Name) => Id.run do
    let some index := env.getModuleIdxFor? name | return false
    let some module := env.header.modules[index.toNat]? | return false
    return families.any (·.isPrefixOf module.module)
  let mut lines := #[]
  for (name, info) in env.constants.map₁.toList do
    if !selected name || (privateToUserName? name |>.getD name).isInternal then continue
    if (declRangeExt.find? env name).isNone then continue
    if isAuxRecursor env name || isNoConfusion env name then continue
    if info matches .recInfo _ then continue
    lines := lines.push
      s!"{name}\t{kind info}\t{structuralHash info.type}\t{explicitHash env info.type}"
  let sorted := lines.qsort (· < ·)
  IO.FS.writeFile output (String.intercalate "\n" sorted.toList ++ "\n")
  IO.println s!"{sorted.size} declarations"
  return 0
