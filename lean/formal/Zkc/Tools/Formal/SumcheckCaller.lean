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

/-- The two total operands in the supported public-table relation fragment. -/
inductive TableOperand where
  | claim | total

def TableOperand.read (table target : LocalId) : Lowered.Expr → Option TableOperand
  | .local _ id => if id == target then some .claim else none
  | .fold _ .sum (.collection item _ (.local _ source)) (.local _ element) =>
    if source == table && element == item.id then some .total else none
  | _ => none

def TableOperand.value {F : Type} [Zero F] [Add F] (xs : List F) (v : F) : TableOperand → F
  | .claim => v
  | .total => xs.sum

def tableEquality? (table target : LocalId) (expr : Lowered.Expr) : Option (TableOperand × TableOperand) := do
  let .operator _ .equal #[lhs,rhs] := expr | none
  return (← TableOperand.read table target lhs, ← TableOperand.read table target rhs)

def tableMeaning {F : Type} [Zero F] [Add F] (table target : LocalId) (expr : Lowered.Expr)
    (xs : List F) (v : F) : Option Prop :=
  (tableEquality? table target expr).map fun (l,r) => l.value xs v = r.value xs v

structure SourceTableSum where
  declaration : DeclarationId
  table : LocalId
  target : LocalId
  body : Lowered.Expr
  meaning : ∀ {F : Type} [Zero F] [Add F] (xs : List F) (v : F),
    tableMeaning table target body xs v = some (v = xs.sum)

private def certifyTableEquality (id : DeclarationId) (table target : LocalId) (body : Lowered.Expr) :
    Option SourceTableSum :=
  match read : tableEquality? table target body with
  | some (.claim,.total) => some ⟨id,table,target,body,by intros; simp [tableMeaning, read, TableOperand.value]⟩
  | some (.total,.claim) => some ⟨id,table,target,body,by intros; simp [tableMeaning, read, TableOperand.value, eq_comm]⟩
  | _ => none

/-- Recognize the relation selected by the deciding role by its resolved operands and
definition. Binder names and the name chosen for the relation may vary. -/
def tableSumRelation? (c : Written.AdmittedRoot) : Option SourceTableSum := do
  let s := c.state
  let key ← s.results.key? c.id
  let decl ← s.env.modules.lowered? key.declaration
  let .protocol head .. := decl.content | none
  let #[values, claim] := head.ports | none
  let clauses ← (Written.contractOf s key.declaration default).toOption
  let #[.proves _ (some 1) _ (.call span ref supplied none)] :=
    clauses.filter (fun cl => cl matches .proves ..) | none
  let id ← (Written.closedDeclaration ref).toOption
  let owner ← s.program.declarations[id]?
  let .relation rel := owner.node | none
  guard (!supplied.any (fun arg => arg matches .spec ..))
  let #[.local _ xs, .local _ v] ← (Lowered.pairValueArguments rel.name.text
    (rel.statement.map (·.name.text)) supplied span).toOption | none
  guard (xs == values.binder.id && v == claim.binder.id)
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
  certifyTableEquality id table.binder.id target.binder.id body

def tableSumClaim? (c : Written.AdmittedRoot) : Option DeclarationId :=
  (tableSumRelation? c).map (·.declaration)

end Zkc.Tools.Formal
