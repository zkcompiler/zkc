module

public import Zkc.Frontend.Written.ChargeData
public import Zkc.Frontend.Written.Selection

@[expose] public section
namespace Zkc.Frontend.Written

/-- Resolve a direct named draw in the selected closed instance. A zero-trip stepped loop
still has a declared event. Each nonempty realization must map to one admitted address. -/
def drawCharge {V : Core.Vocabulary} (s : Compile.State) (program : Core.Typed V)
    (owner : Core.Key) (name : String) : ExportM DrawCharge := do
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
  let .operator _ .divide #[numerator, denominator] := bound
    | throw "expected a quotient of static naturals"
  let env := Static.instanceEnv s.program decl entry.key.arguments entry.key.specification
  let (result, after) := (Prod.mk <$> Static.evalSize env numerator <*> Static.evalSize env denominator).run sourceContext s
  let .ok (num, den) := result | do
    let diagnostics := after.log.entries.extract s.log.entries.size after.log.entries.size
    let messages := diagnostics.toList.map (·.render after.env.renderer)
    throw s!"{location bound.span}: cannot close the charge quotient: {String.intercalate "; " messages}"
  let some (.protocol code) := s.results.body? owner.number | throw "missing elaborated charge owner"
  let some addresses := Emit.SiteAddresses.forProtocol program owner | throw "missing admitted charge owner"
  let occurrences := Typing.SiteEntry.realizations code.sites event "value"
  let some draws := occurrences.toList.mapM addresses.resolve | throw "ambiguous or missing draw address"
  -- TY8 defines division by zero in a rational expression to give zero.
  return if den == 0 then ⟨owner,0,1,draws⟩ else ⟨owner,num,den,draws⟩

end Zkc.Frontend.Written
