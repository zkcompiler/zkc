import Zkc.Frontend.Emit.Application
import Zkc.Frontend.Written.Root

namespace Zkc.Tools.Formal
open Zkc.Core Zkc.Frontend

def gateRow := Emit.primitiveName ⟨"circuit.gate_evaluate", #[.type (StandardNames.fieldType .bls12381Fr)]⟩

structure CallerKeys where
  site : Key
  reduction : Key
  evaluator : Key

/-- Read the application site and both callees from the emitted caller. -/
def sumcheckCallKeys (e : Emit.RootEmission) (root : Key) : Option CallerKeys := do
  let .protocol _ _ _ _ (.mk _ steps _) ← e.named.definitions.find? (·.key == root) | none
  let [(site,red)] := steps.filterMap (fun
    | .op site _ (.apply callee [0,1]) _ => some (site,callee)
    | _ => none) | none
  let [eval] := steps.filterMap (fun
    | .op _ _ (.compute [1] (.call fn)) _ => some fn
    | _ => none) | none
  return ⟨site,red,eval⟩

/-- Check the formal symbol and the actual table argument attached to the reduction. -/
def hasSourceExtension (c : Written.AdmittedRoot) : Bool := Id.run do
  let key : Key := ⟨c.id⟩
  let some keys := sumcheckCallKeys c.emission key | return false
  let some caller := c.state.results.checked? c.id | return false
  let .protocol body := caller.definition.body | return false
  let #[values, _] := body.ports | return false
  let some claim := c.emission.externalApplicationAt? c.state key keys.site keys.reduction [0,1]
    "p" "Zkc.Polynomial.extension" | return false
  return claim.operands == [.binder values.binder.id]

/-- Recognize the relation selected by the deciding role by its resolved operands and
definition. Binder names and the name chosen for the relation may vary. -/
def tableSumClaim? (c : Written.AdmittedRoot) : Option DeclarationId := do
  let s := c.state
  let key ← s.results.key? c.id
  let decl ← s.env.modules.lowered? key.declaration
  let .protocol head .. := decl.content | none
  let #[values, claim] := head.ports | none
  let clauses ← (Written.contractOf s key.declaration default).toOption
  let [(clause,place)] := clauses.toList.zipIdx.filter (fun (cl,_) => cl matches .proves ..) | none
  let .proves span (some 1) .. := clause | none
  let (typed, after) ← (Written.evaluate s span (Typing.typedClauses c.id #[] (only := some place))).toOption
  let #[(_, .apply _ (.instance inst) #[.local _ xs, .local _ v])] := typed | none
  guard (xs == values.binder.id && v == claim.binder.id)
  let selected ← after.table.entries[inst]?
  let id := selected.key.declaration
  let owner ← after.program.declarations[id]?
  let .relation _ := owner.node | none
  let preconditions ← (Written.contractOf after id span).toOption
  guard (!preconditions.any (fun clause => clause matches .requires ..))
  let relation ← s.env.modules.lowered? id
  let .function fn (.body expr) := relation.content | none
  let #[table, target] := fn.parameters | none
  guard (fn.statementParameters == some 2)
  let body := match expr with | .block _ #[] result => result | result => result
  let .operator _ .equal #[.local _ lhs, .fold _ .sum (.collection item _ (.local _ source)) (.local _ element)] := body | none
  guard (lhs == target.binder.id && source == table.binder.id && element == item.id)
  return id

end Zkc.Tools.Formal
