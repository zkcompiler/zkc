import Lean
import Zkc.Tests.Frontend.PrintedFixtures

/-!
The fixtures of the printer hold every constructor that a program by names can hold.

For each fixture, the constructors of every inductive type that a value of its type can hold
are collected through the types of the constructors' fields, and the constructors that its
value holds are collected. A constructor of the first collection that is not in the second is
an error of this file. `just test-packages` builds this file, so a constructor added to the
program by names, to a key of the vocabulary or to a parameter of a project primitive makes
that recipe fail until a fixture holds it.

Numbers and strings are left out: they are literals. Proofs and types are not values. A
constructor with a field of a type that has no constructor has no value and is not asked for.
The comparison is by constructor within one fixture: one occurrence of a constructor stands
for every field of its type in that fixture.
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

/-- The constructors that a value of the fixture's type can hold and the fixture does not. -/
def missing (fixture : Name) : MetaM (List Name) := do
  let value := mkConst fixture
  let (_, _, wanted) ← (reachable (← inferType value)).run ({}, {})
  let (_, found) ← (held value).run {}
  return (wanted.toList.filter (!found.contains ·)).mergeSort (·.toString < ·.toString)

run_meta do
  for fixture in [``PrintedFixtures.bindingRows, ``PrintedFixtures.definitions,
      ``PrintedFixtures.association] do
    let absent ← missing fixture
    unless absent.isEmpty do
      throwError "{fixture} holds no{indentD (MessageData.joinSep (absent.map (m!"{·}")) Format.line)}"

end Zkc.Tests.Frontend.PrintedFixtureCoverage
