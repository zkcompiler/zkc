import Zkc.Frontend.Emit.Application
import Zkc.Frontend.Written.Root

namespace ZkcFormalTools
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
  let #[.proves _ (some 1) _ (.call _ ref #[.positional _ (.local _ xs), .positional _ (.local _ v)] none)] :=
    clauses.filter (fun cl => cl matches .proves ..) | none
  guard (xs == values.binder.id && v == claim.binder.id)
  let id ← (Written.closedDeclaration ref).toOption
  let owner ← s.program.declarations[id]?
  let .relation _ := owner.node | none
  let preconditions ← (Written.contractOf s id ref.span).toOption
  guard (!preconditions.any (fun clause => clause matches .requires ..))
  let checked ← s.results.checked? c.id
  let .protocol typed := checked.definition.body | none
  let (signature, _) := (do
    let inst ← Static.instantiate id key.arguments ⟨s.program.nameOf id, ref.span⟩
    Emit.signatureTypes inst).run Written.sourceContext s
  let .ok (arguments, some .bool) := signature | none
  guard (arguments == typed.ports.map (·.binder.type))
  let relation ← s.env.modules.lowered? id
  let .function fn (.body expr) := relation.content | none
  let #[table, target] := fn.parameters | none
  guard (fn.statementParameters == some 2)
  let body := match expr with | .block _ #[] result => result | result => result
  let .operator _ .equal #[.local _ lhs, .fold _ .sum (.collection item _ (.local _ source)) (.local _ element)] := body | none
  guard (lhs == target.binder.id && source == table.binder.id && element == item.id)
  return id

end ZkcFormalTools
