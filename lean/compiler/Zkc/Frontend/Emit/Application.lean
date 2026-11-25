module

public import Zkc.Frontend.Emit.Root
public import Zkc.Frontend.Typed.Find

@[expose] public section
namespace Zkc.Frontend.Emit

/-- A lexical operand, including the range used when a natural is supplied at a finite index type. -/
inductive LocalOperand where
  | binder (id : LocalId)
  | bounded (upper : Nat) (id : LocalId)
  deriving DecidableEq

/-- A direct specification-function application to lexical variables in the typed caller. -/
structure LocalApplication where
  target : InstanceId
  operands : List LocalOperand
  deriving DecidableEq

namespace LocalApplication

def operand : Typed.Expr → Option LocalOperand
  | .local _ id => some (.binder id)
  | .convert info .bounded (.local _ id) _ => do
    let .index upper := info.type | none
    return .bounded upper id
  | _ => none

def read (port : String) (arguments : Array (String × Typed.Expr)) : Option LocalApplication := do
  let [(_, .apply _ (.instance target) args)] := arguments.toList.filter (fun arg => arg.1 == port) | none
  return ⟨target, ← args.toList.mapM operand⟩

end LocalApplication

/-- Recover a specification argument shared by the emitted attachment and the typed source
event at the given instruction. Each lookup must identify exactly one attachment or port. -/
def RootEmission.localApplicationAt? (e : RootEmission) (state : Compile.State)
    (caller site callee : Core.Key) (roles : List Nat) (port : String) : Option LocalApplication := do
  let checked ← state.results.checked? caller.number
  let .protocol body := checked.definition.body | none
  let [origin] := e.origins.toList.filter (·.definition == caller) | none
  let [attached] := origin.specification.toList.filter (·.instruction == site) | none
  let node ← origin.nodes[site.number]?
  let .stmt (.event _ _ (.apply _ target _ specification roleMap ..)) ← body.find? node | none
  guard (target == callee.number && roleMap.toList == roles)
  let application ← LocalApplication.read port specification
  guard (LocalApplication.read port attached.arguments == some application)
  return application

def RootEmission.matchesLocalApplication (e : RootEmission) (state : Compile.State)
    (caller site callee : Core.Key) (roles : List Nat) (port : String) (expected : LocalApplication) : Bool :=
  e.localApplicationAt? state caller site callee roles port == some expected

/-- Resolve a direct application of a named `spec def` to its declared external symbol.
The consumer supplies the interpretation of that symbol. -/
def RootEmission.externalApplicationAt? (e : RootEmission) (state : Compile.State)
    (caller site callee : Core.Key) (roles : List Nat) (port symbol : String) : Option LocalApplication := do
  let application ← e.localApplicationAt? state caller site callee roles port
  let target ← state.table.allocatedKey? application.target
  let declaration ← state.program.declarations[target.declaration]?
  let .«def» definition := declaration.node | none
  let some (.spec _) := definition.modifier | none
  let .external binding := definition.binding | none
  guard (binding.name.content == symbol)
  return application

end Zkc.Frontend.Emit
