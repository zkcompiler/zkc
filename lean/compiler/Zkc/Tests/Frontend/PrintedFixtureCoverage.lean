import Lean
import Zkc.Tests.Frontend.PrintedFixtures

/-!
The fixtures of the printer hold every constructor that a program by names can hold.

From the types of the fixtures, the constructors of every inductive type that a value can hold
are collected through the types of the constructors' fields. From the values of the fixtures,
the constructors that they hold are collected. A constructor of the first collection that is
not in the second is an error of this file, so a constructor added to the program by names, to
a key of the vocabulary or to a parameter of a project primitive stops the build until a
fixture holds it.

Numbers and strings are left out: they are literals. Proofs and types are not values. A
constructor with a field of a type that has no constructor has no value and is not asked for.
The comparison is by constructor: one occurrence of a constructor stands for every field of
its type.
-/

open Lean Meta

namespace Zkc.Tests.Frontend.PrintedFixtureCoverage

/-- Whether the type is an inductive type without a constructor. -/
def empty (type : Expr) : MetaM Bool := do
  let .const name _ := (← whnf type).getAppFn | return false
  let some (.inductInfo info) := (← getEnv).find? name | return false
  return info.ctors.isEmpty

/-- The constructors of every inductive type that a value of the type can hold. -/
partial def reachable (type : Expr) : StateRefT (Std.HashSet Expr × NameSet) MetaM Unit := do
  let type ← whnf type
  if (← get).1.contains type then return
  modify fun (seen, constructors) => (seen.insert type, constructors)
  let .const name levels := type.getAppFn | return
  if name == ``Nat || name == ``String then return
  let some (.inductInfo info) := (← getEnv).find? name | return
  let parameters := type.getAppArgs.extract 0 info.numParams
  for constructor in info.ctors do
    let general := (← getConstInfo constructor).type.instantiateLevelParams info.levelParams levels
    forallTelescope (← instantiateForall general parameters) fun fields _ => do
      let fieldTypes ← fields.mapM (inferType ·)
      if ← fieldTypes.anyM (liftM <| empty ·) then return
      modify fun (seen, constructors) => (seen, constructors.insert constructor)
      for fieldType in fieldTypes do
        unless ← isProp fieldType do reachable fieldType

/-- The constructors that a value holds, in its fields and theirs. -/
partial def held (value : Expr) : StateRefT NameSet MetaM Unit := do
  let value ← whnf value
  let .const name _ := value.getAppFn | return
  let some (.ctorInfo info) := (← getEnv).find? name | return
  modify (·.insert name)
  let arguments := value.getAppArgs
  for i in [info.numParams:arguments.size] do
    let field := arguments[i]!
    unless (← isProp (← inferType field)) || (← isType field) do held field

/-- The constructors that values of the fixtures can hold and do not. -/
def missing (fixtures : List Name) : MetaM (List Name) := do
  let mut wanted : Std.HashSet Expr × NameSet := ({}, {})
  let mut found : NameSet := {}
  for fixture in fixtures do
    let value := mkConst fixture
    (_, wanted) ← (reachable (← inferType value)).run wanted
    (_, found) ← (held value).run found
  return (wanted.2.toList.filter (!found.contains ·)).mergeSort (·.toString < ·.toString)

run_meta do
  let absent ← missing [``PrintedFixtures.bindingRows, ``PrintedFixtures.definitions,
    ``PrintedFixtures.association]
  unless absent.isEmpty do
    throwError "the fixtures of the printer hold no{indentD (MessageData.joinSep (absent.map (m!"{·}")) Format.line)}"

end Zkc.Tests.Frontend.PrintedFixtureCoverage
