module

public meta import Lean

/-! Inspect checked construction terms without adding a proof rule. Counts include owner-local
auxiliary proofs and exclude theorem types and unrelated imports. -/

public meta section
open Lean Meta Elab Command
namespace ProtocolProof.Tools.ConstructionAudit

private def references (callee : Name) : Expr → Nat
  | .const name _ => if name == callee then 1 else 0
  | .app fn argument => references callee fn + references callee argument
  | .lam _ _ body _ | .forallE _ _ body _ => references callee body
  | .letE _ _ value body _ => references callee value + references callee body
  | .mdata _ body | .proj _ _ body => references callee body
  | _ => 0

/-- Include Lean's extracted local proofs, without unfolding the shared callee. -/
private def inspect (owner callee : Name) : MetaM (Nat × Nat × Nat) := do
  let environment := (← getEnv).setExporting false
  let mut pending := [owner]
  let mut seen : NameSet := {}
  let mut uses := 0
  let mut nodes := 0
  let mut unique : ExprSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := environment.find? name | throwError "missing checked owner {name}"
    let some value := info.value? (allowOpaque := true) | throwError "missing proof body {name}"
    uses := uses + references callee value
    nodes := nodes + value.sizeWithoutSharing
    let mut expressions := [value]
    while !expressions.isEmpty do
      let expression := expressions.head!
      expressions := expressions.tail!
      if unique.contains expression then continue
      unique := unique.insert expression
      expressions := expression.foldlM (m := Id) (fun rest child => child :: rest) expressions
    for dependency in value.getUsedConstants do
      if owner.isPrefixOf dependency then pending := dependency :: pending
  return (uses, nodes, unique.size)

def requireUses (owner callee : Name) (expected maxNodes : Nat) : MetaM Unit := do
  let (uses, _, unique) ← inspect owner callee
  unless uses == expected do
    throwError "{owner}: expected {expected} checked references to {callee}, got {uses}"
  unless unique ≤ maxNodes do
    throwError "{owner}: unique proof size {unique} exceeds regression limit {maxNodes}"

/-- Fresh proof elaboration and synchronous declaration checking, excluding imports.
The external driver measures whole-process time and memory separately. -/
elab "measured_construction " identifier:ident " : " type:term " := " proof:term : command =>
    liftTermElabM do
  let start ← IO.monoNanosNow
  let expected ← Term.elabType type
  let value ← Term.elabTermEnsuringType proof expected
  Term.synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  let value ← instantiateMVars value
  if expected.hasMVar || value.hasMVar || value.hasSorry then
    throwError "unfinished construction measurement"
  let (expected, value) := _root_.ShareCommon.shareCommon' (expected, value)
  let name := (← getCurrNamespace) ++ identifier.getId
  let proposed ← IO.monoNanosNow
  withOptions (Elab.async.set · false) <|
    addDecl (.thmDecl { name, levelParams := [], type := expected, value })
  let checked ← IO.monoNanosNow
  logInfo m!"CONSTRUCTION-PHASE {(Json.mkObj [
    ("owner", toJson name.toString), ("elaboration_ns", toJson (proposed - start)),
    ("declaration_check_ns", toJson (checked - proposed))]).compress}"

/-- Optional diagnostics: fresh kernel rechecking, independently of tactic execution. -/
elab "construction_metrics " owner:ident " using " callee:ident : command => liftTermElabM do
  let owner ← realizeGlobalConstNoOverloadWithInfo owner
  let callee ← realizeGlobalConstNoOverloadWithInfo callee
  let (uses, nodes, unique) ← inspect owner callee
  let environment := (← getEnv).setExporting false
  let info ← getConstInfo owner
  let some value := info.value? (allowOpaque := true) | throwError "missing proof {owner}"
  let mut samples : Array Nat := #[]
  for _ in [:3] do
    let start ← IO.monoNanosNow
    let type ← match Kernel.check environment {} value with
      | .ok type => pure type
      | .error error => throwError "kernel recheck failed: {error.toMessageData (← getOptions)}"
    let .ok true := Kernel.isDefEq environment {} type info.type
      | throwError "kernel recheck produced a different declaration type"
    samples := samples.push ((← IO.monoNanosNow) - start)
  logInfo m!"CONSTRUCTION-METRIC {(Json.mkObj [
    ("owner", toJson owner.toString), ("callee", toJson callee.toString),
    ("references", toJson uses), ("expanded_nodes", toJson nodes),
    ("unique_nodes", toJson unique), ("kernel_ns", toJson samples)]).compress}"

end ProtocolProof.Tools.ConstructionAudit
