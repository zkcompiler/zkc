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

/-- Check the source application at the origin of this emitted instruction, its protocol
instance, role map and the selected specification operand. Both copies of the operand
must refer to the requested function instance and the same ordered lexical binders. -/
def RootEmission.matchesLocalApplication (e : RootEmission) (state : Compile.State) (caller site callee : Core.Key)
    (roles : List Nat) (port : String) (expected : LocalApplication) : Bool := Id.run do
  let some checked := state.results.checked? caller.number | return false
  let .protocol body := checked.definition.body | return false
  let [origin] := e.origins.toList.filter (·.definition == caller) | return false
  let [attached] := origin.specification.toList.filter (·.instruction == site) | return false
  let some node := origin.nodes[site.number]? | return false
  let some (.stmt (.event _ _ (.apply _ target _ specification roleMap _))) := body.find? node | return false
  return target == callee.number && roleMap.toList == roles &&
    LocalApplication.read port specification == some expected &&
    LocalApplication.read port attached.arguments == some expected

end Zkc.Frontend.Emit
