import Zkc.Frontend.Written.Root
import Zkc.Formal.Interactive.EndpointExpression

namespace Zkc.Tools.Formal.RoundSpecification
open Zkc.Frontend Zkc.Formal.Interactive.Sumcheck

/-- The instance IDs below are local to the compilation that produced the typed laws. -/
structure Selected where
  owner : InstanceId
  ends : InstanceId
  atPoint : InstanceId
  boundary : InstanceId
  evaluate : InstanceId
  polynomial : InstanceId
  expression : LineExpression
  deriving DecidableEq

private def body (s : Compile.State) (id : InstanceId) : Option Typed.FunctionBody := do
  let tree ← s.results.trees.result? id
  let .function f := tree.body | none
  guard f.statements.isEmpty
  return f

private def row (field : StaticValue) (name : String) : Typed.Expr → Option (Array Typed.Expr)
  | .apply _ (.row ref) args => if ref.name == name && ref.statics == #[field] then some args else none
  | _ => none

private def external (s : Compile.State) (id : InstanceId) (name : String) (arguments : Array StaticValue) : Bool := Id.run do
  let some key := s.results.key? id | return false
  if key.arguments != arguments then return false
  let some tree := s.results.trees.result? id | return false
  let .external symbol := tree.body | return false
  return symbol == name

private def localIs (id : LocalId) : Typed.Expr → Bool
  | .local _ x => x == id
  | _ => false

private def component (field : StaticValue) (m : LocalId) : Typed.Expr → Option EndpointExpression
  | .project _ (.local _ x) pos _ =>
    if x != m then none else match pos with
      | 0 => some .first
      | 1 => some .second
      | _ => none
  | .apply _ (.row ref) args => do
    let [a,b] := args.attach.toList | none
    guard (ref.name == "field.add" && ref.statics == #[field])
    return .add (← component field m a.val) (← component field m b.val)
  | _ => none
termination_by e => sizeOf e
decreasing_by all_goals first
  | (have := Array.sizeOf_lt_of_mem a.property; simp +arith; omega)
  | (have := Array.sizeOf_lt_of_mem b.property; simp +arith; omega)

private def valueAt (s : Compile.State) (field : StaticValue) (m : LocalId) (expr : Typed.Expr) :
    Option (InstanceId × Typed.Expr) := do
  let .apply _ (.instance value) #[.apply _ (.instance poly) #[arg], r] := expr | none
  guard (external s value "Zkc.Polynomial.value" #[field,.natural 1] && localIs m arg)
  return (poly,r)

private def readBodies (s : Compile.State) (field : StaticValue) (owner ends atPoint : InstanceId) :
    Option Selected := do
  let e ← body s ends
  let #[m] := e.parameters | none
  let #[.apply _ (.instance boundary) #[arg], sum] ← row field "field.equal" e.result | none
  guard (localIs m.id arg)
  let #[zero,one] ← row field "field.add" sum | none
  let (p, .literal _ (.nominal [0])) ← valueAt s field m.id zero | none
  let (q, .literal _ (.nominal [1])) ← valueAt s field m.id one | none
  let a ← body s atPoint
  let #[msg,challenge] := a.parameters | none
  let #[.apply _ (.instance evaluate) #[arg,coin], rhs] ← row field "field.equal" a.result | none
  let (t,r) ← valueAt s field msg.id rhs
  guard (p == q && p == t && localIs msg.id arg && localIs challenge.id coin && localIs challenge.id r)
  let poly ← body s p
  let #[wire] := poly.parameters | none
  let .apply _ (.instance line) #[u,v] := poly.result | none
  guard (external s line "Zkc.Polynomial.line" #[field])
  let .module _ members ← s.table.content? owner | none
  let some (.natural 1) := (members.find? (·.1 == "Degree")).map Prod.snd | none
  let moduleKey ← s.results.key? owner
  for (name,id) in [("boundary",boundary),("evaluate",evaluate),("polynomial",p)] do
    let some (.definition decl) := (members.find? (·.1 == name)).map Prod.snd | none
    let key ← s.results.key? id
    guard (key.declaration == decl && key.arguments == moduleKey.arguments)
  return ⟨owner, ends, atPoint, boundary, evaluate, p, ⟨← component field wire.id u, ← component field wire.id v⟩⟩

/-- Read the two verifier laws under Self at the actual module argument of this reduction.
The expressions retain resolved member instances, field rows, external symbols and operands. -/
def read (state : Compile.State) (reduction : InstanceId) : Except String Selected := do
  let some call := state.table.entries[reduction]? | throw "missing reduction instance"
  let #[field, .module owner, .natural _, .natural _, .natural _] := call.key.arguments
    | throw "expected a field, a round implementation and three dimensions"
  let (_, laws) ← Written.evaluate state default (Instances.moduleLaws owner)
  let law (name : String) : Option InstanceId := do
    let [id] := (List.range laws.table.entries.size).filter (fun i =>
      let key := laws.table.entries[i]!.key
      key.owner == some owner && laws.program.nameOf key.declaration == name) | none
    return id
  let some ends := law "ends" | throw "expected one ends obligation at the selected module"
  let some atPoint := law "at_point" | throw "expected one at_point obligation at the selected module"
  let (_, typed) ← Written.evaluate laws default do
    Typing.typeBody ends default
    Typing.typeBody atPoint default
  let some result := readBodies typed field owner ends atPoint
    | throw "the typed verifier laws or polynomial interpretation did not match"
  return result

end Zkc.Tools.Formal.RoundSpecification
