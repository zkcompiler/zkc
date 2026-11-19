module

public import Zkc.Frontend.Written.ChargeData
public import Zkc.Frontend.Written.Selection
public import Zkc.Frontend.Static.Rational

@[expose] public section
namespace Zkc.Frontend.Written

structure DeclaredDraw where
  event : Nat
  ceiling : Rat

/-- Resolve the authored clause in its closed instance, before looking up realized addresses. -/
def declaredDraw (s : Compile.State) (owner : Core.Key) (name : String) : ExportM DeclaredDraw := do
  let some entry := s.table.entries[owner.number]? | throw "missing charge instance"
  let id := entry.key.declaration
  let some decl := s.program.declarations[id]? | throw "missing charge declaration"
  let some {content := .protocol head .., ..} := s.env.modules.lowered? id
    | throw "expected a resolved protocol"
  let #[(source, event)] := head.events.zipIdx.filter (fun (e, _) => e.name == some name)
    | throw s!"expected one source event named {name}"
  let .transfer _ (some _) := source.audience | throw s!"{name} is not a draw"
  let #[bound] := (← contractOf s id source.span).filterMap (fun
    | .charge _ site expr => if site.names.map (·.text) == #[name] then some expr else none
    | _ => none) | throw s!"expected one charge on sites.{name}"
  let env := Static.instanceEnv s.program decl entry.key.arguments entry.key.specification
  let (result, after) := (Static.evalRational env bound).run sourceContext s
  let .ok amount := result | do
    let diagnostics := after.log.entries.extract s.log.entries.size after.log.entries.size
    let messages := diagnostics.toList.map (·.render after.env.renderer)
    throw s!"{location bound.span}: cannot close the rational ceiling: {String.intercalate "; " messages}"
  if amount.num < 0 then throw "a draw ceiling must be nonnegative"
  return ⟨event, amount⟩

/-- A zero-trip loop retains its declaration. Every realized draw must have a unique address. -/
def drawCharge {V : Core.Vocabulary} (s : Compile.State) (program : Core.Typed V)
    (owner : Core.Key) (name : String) : ExportM DrawCharge := do
  let ⟨event, amount⟩ ← declaredDraw s owner name
  let some (.protocol code) := s.results.body? owner.number | throw "missing elaborated charge owner"
  let some addresses := Emit.SiteAddresses.forProtocol program owner | throw "missing admitted charge owner"
  let occurrences := Typing.SiteEntry.realizations code.sites event "value"
  let some draws := occurrences.toList.mapM addresses.resolve | throw "ambiguous or missing draw address"
  return ⟨owner,amount.num.toNat,amount.den,draws⟩

end Zkc.Frontend.Written
