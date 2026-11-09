module

public import Zkc.IR.Source.Structured.CommonCoordinateCertificate

@[expose] public section

/-! A bounded proposer for the finite typed certificate. It reads every stored protocol,
including dormant ones. Imported source authority is carried by the canonical payload;
certificate construction cannot replace a body, formal parameter or role substitution. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm
open Availability (Analysis chargeOperations chargeDependencies chargeReplay)

variable (snapshot : Snapshot) (definitions : List CheckedProtocol) (pair : Pair)

def diagnostic (cursor : Cursor) (op : ProtocolOp) : String :=
  let (definition, row) := match op with
    | .oracle _ location => (location.definition, location.row)
    | _ => (cursor.definition, cursor.row)
  "oracle-common-coordinate-opaque:definition=" ++ toString definition ++ ":row=" ++ toString row

/- Node charging includes copied term structure, so repeatedly doubling an expression
cannot escape the finite replay allowance. It is not a runtime complexity theorem. -/
mutual
  def expressionSize {scope : Scope} {ty : Ty} : Expression scope ty → Nat
    | .calc _ _ terms _ => 1 + termsSize terms
    | .law entry _ _ => Fin.elim0 entry
    | _ => 1
  def termsSize {scope : Scope} {types : List Ty} : Terms [] scope types → Nat
    | .nil => 0
    | .cons head tail => expressionSize head + termsSize tail
end

def chargeSymbols : {scope : Scope} → {types : List Ty} → Symbols scope types → Analysis Unit
  | _, _, .nil => pure ()
  | _, _, .cons term rest => do
    chargeReplay (1 + (term.map expressionSize).getD 0)
    chargeSymbols rest

/-- Fuel bounds structural/call depth; independent shared counters charge all branches.
The retained source already passes the importer's acyclic full-signature linking. -/
def propose : (fuel : Nat) → {scope : Scope} → {inputs outputs : List Ty} →
    (roles : Nat → Nat) → (cursor : Cursor) → (origins : Origins scope) →
    (body : Region protocolDialect inputs outputs) → (env : Symbols scope inputs) →
    Analysis (Plan snapshot definitions pair roles cursor origins body env)
  | 0, _, _, _, _, _, _, _, _ => throw "oracle-common-coordinate-depth-limit"
  | fuel + 1, _, _, _, roles, cursor, origins, .ret _, _ => do
    chargeOperations 1
    return .ret
  | fuel + 1, _, _, _, roles, cursor, origins, .stop _, _ => do
    chargeOperations 1
    return .stop
  | fuel + 1, scope, _, _, roles, cursor, origins, .bind (mid := middle) body next, env => do
    chargeOperations 1
    let inside ← propose fuel roles cursor origins body env
    let tail ← propose fuel roles cursor origins next ((unknown scope middle).append env)
    return .bind inside tail
  | fuel + 1, scope, _, _, roles, cursor, origins,
      .letOp (.protocolApply signature selected site) args .nil next, env => do
    chargeOperations 1
    chargeDependencies (definitions.length + args.indices.length + selected.length)
    let actual := args.eval env.get
    chargeSymbols actual
    match found : definitions.find? (fun definition ↦ definition.signature == signature) with
    | none => throw "oracle-common-coordinate-callee"
    | some definition =>
      have member : definition ∈ definitions := List.mem_of_find?_eq_some found
      have same : definition.signature = signature := by
        simpa only [beq_iff_eq] using List.find?_some found
      let childRoles := roles ∘ roleSubstitution selected
      let child : Region protocolDialect signature.inputs signature.outputs :=
        same ▸ (show Region protocolDialect definition.signature.inputs definition.signature.outputs
          from definition.body)
      let inside ← propose fuel childRoles
        (cursor.enter (snapshot.definitions.findIdx (·.name == definition.name))) origins child
        (maskSymbols pair childRoles signature.inputScopes actual)
      let tail ← propose fuel roles cursor origins next
        ((unknown scope signature.outputs).append env)
      return .apply definition member same inside tail
  | fuel + 1, scope, _, _, roles, cursor, origins,
      .letOp (.repeat spec site) args (.cons body .nil) next, env => do
    chargeOperations 1
    chargeDependencies args.indices.length
    let callback := callbackSymbols pair roles spec (args.eval env.get)
    chargeSymbols callback
    let inside ← propose fuel roles cursor.child
      (.cons (.counter cursor.definition cursor.applications cursor.row) origins) body callback
    let tail ← propose fuel roles cursor origins next ((unknown scope spec.state).append env)
    return .repeat inside tail
  | fuel + 1, _, _, _, roles, cursor, origins, .letOp op args bodies next, env => do
    chargeOperations 1
    chargeDependencies args.indices.length
    if leaf : atomic op = true then
      if noRegions : op.regions = [] then
        if coordinate : supported pair roles op (args.eval env.get) = true then
          let results := transfer pair roles op (args.eval env.get)
          chargeSymbols results
          let tail ← propose fuel roles (cursor.after op) origins next (results.append env)
          return .step leaf noRegions coordinate tail
        else throw (diagnostic cursor op)
      else throw "oracle-common-coordinate-regions"
    else throw "oracle-common-coordinate-structural"

inductive PlansFor (snapshot : Snapshot) (definitions : List CheckedProtocol)
    (definition : CheckedProtocol) : List Pair → Type where
  | nil : PlansFor snapshot definitions definition []
  | cons {pair rest}
      (head : Plan snapshot definitions pair id
        {definition := snapshot.definitions.findIdx (·.name == definition.name)}
        (inputOrigins (snapshot.definitions.findIdx (·.name == definition.name)) definition.inputs)
        definition.body
        (inputSymbols pair id definition.inputs definition.inputScopes))
      (tail : PlansFor snapshot definitions definition rest) :
      PlansFor snapshot definitions definition (pair :: rest)

def rolePairs (count : Nat) : List Pair :=
  (List.range count).flatMap fun left ↦
    ((List.range count).filter (left < ·)).map (fun right ↦ ⟨left, right⟩)

def proposePairs (definition : CheckedProtocol) : (pairs : List Pair) →
    Analysis (PlansFor snapshot definitions definition pairs)
  | [] => pure .nil
  | pair :: rest => do
    let index := snapshot.definitions.findIdx (·.name == definition.name)
    let plan ← propose snapshot definitions pair 100000
      id {definition := index}
      (inputOrigins index definition.inputs) definition.body
      (inputSymbols pair id definition.inputs definition.inputScopes)
    let tail ← proposePairs definition rest
    return .cons plan tail

/-- Complete retained-unit coverage is an index of this finite witness. -/
inductive UnitCertificate (snapshot : Snapshot) (definitions : List CheckedProtocol) :
    List CheckedProtocol → Type where
  | nil : UnitCertificate snapshot definitions []
  | cons {definition rest}
      (head : PlansFor snapshot definitions definition (rolePairs definition.roles.length))
      (tail : UnitCertificate snapshot definitions rest) :
      UnitCertificate snapshot definitions (definition :: rest)

def proposeUnit : (remaining : List CheckedProtocol) →
    Analysis (UnitCertificate snapshot definitions remaining)
  | [] => pure .nil
  | definition :: rest => do
    chargeDependencies (definition.roles.length * definition.roles.length)
    chargeReplay (definition.inputs.length + definition.roles.length)
    let head ← proposePairs snapshot definitions definition (rolePairs definition.roles.length)
    let tail ← proposeUnit rest
    return .cons head tail

def certify (snapshot : Snapshot) (definitions : List CheckedProtocol)
    (budget : Availability.Budget := {}) :
    Except String (UnitCertificate snapshot definitions definitions) :=
  ((proposeUnit snapshot definitions definitions).run budget).map Prod.fst

end Zkc.Source.Structured.CommonCoordinate
