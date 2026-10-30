import ZkcTools.ConstructionBindings.Alignment
import Lean.Elab.Command
import Lean.Util.NumObjs

/-! Focused experiment instrumentation. Declaration installation is synchronous;
proposal time includes elaboration and finite search, and kernel time includes
`addDecl` bookkeeping. Imports and later module serialization are excluded.
Counts inspect the produced declaration value, without unfolding body families.
-/
public meta section
open Lean Meta Elab Command Term

namespace Tests.ConnectionPlacementMetrics

private def occurrences (expression : Expr) (selected : Name → Bool) : Nat :=
  (go expression).run' {}
where
  go (expression : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
    if let some count := (← get)[expression]? then return count
    let count ← match expression with
      | .const name _ => pure (if selected name then 1 else 0)
      | .app function argument => return (← go function) + (← go argument)
      | .lam _ type body _ | .forallE _ type body _ => return (← go type) + (← go body)
      | .letE _ type value body _ => return (← go type) + (← go value) + (← go body)
      | .mdata _ body | .proj _ _ body => go body
      | _ => pure 0
    modify (·.insert expression count)
    return count

private def familyCounts (value : Expr) : CoreM (Array (String × Json)) := do
  return (ZkcTools.ConstructionBindings.TargetPlacement.checkedBodies.getState (← getEnv)).map
    fun family => (family.toString, toJson (occurrences value (· == family)))

syntax "measured_placement_decl " ident " : " term " := " term : command
elab_rules : command
  | `(measured_placement_decl $identifier:ident : $type:term := $proof:term) => liftTermElabM do
    let start ← IO.monoNanosNow
    let expected ← Term.elabType type
    let value ← Term.elabTermEnsuringType proof expected
    Term.synthesizeSyntheticMVarsNoPostponing
    let expected ← instantiateMVars expected
    let value ← instantiateMVars value
    if value.hasMVar || value.hasSorry then throwError "unfinished placement experiment"
    let (expected, value) := _root_.ShareCommon.shareCommon' (expected, value)
    let name := (← getCurrNamespace) ++ identifier.getId
    let declaration ← mkDefinitionValInferringUnsafe name [] expected value
      (.regular (getMaxHeight (← getEnv) value + 1))
    let proposed ← IO.monoNanosNow
    withOptions (Elab.async.set · false) <| addDecl (.defnDecl declaration)
    let checked ← IO.monoNanosNow
    modifyEnv (addNoncomputable · name)
    let familyReferences ← familyCounts value
    let objects ← value.numObjs
    logInfo m!"PLACEMENT-METRIC {Json.mkObj [
      ("name", toJson name.toString), ("proposal_ns", toJson (proposed - start)),
      ("kernel_ns", toJson (checked - proposed)), ("expression_objects", toJson objects),
      ("family_references", Json.mkObj familyReferences.toList),
      ("generated_exact_bodies", toJson (← ZkcTools.ConstructionBindings.Alignment.placementCosts.get).size),
      ("inline_alignment_guards", toJson (occurrences value (· == ``Zkc.Construction.ConnectionCertificate.Alignment.guard))),
      ("inline_alignment_calculations", toJson (occurrences value (· == ``Zkc.Construction.ConnectionCertificate.Alignment.calculation)))]}"

syntax "audit_placements " ident num " [" ident,* "]" : command
elab_rules : command
  | `(audit_placements $identifier:ident $count:num [$families:ident,*]) => liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo identifier
    let value := (← getConstInfo name).value!
    let families ← families.getElems.mapM fun family => do
      realizeGlobalConstNoOverloadWithInfo family
    let references := occurrences value (families.contains ·)
    unless references == 2 * count.getNat do
      throwError "placement audit: expected {2 * count.getNat} alignment/extent family references, found {references}"
    if value.getUsedConstants.any (fun constant =>
        (constant.toString.splitOn "retainedConnectionAlignment").length > 1) then
      throwError "placement audit: a new exact-placement body declaration was referenced"
    for rule in [``Zkc.Construction.ConnectionCertificate.Alignment.guard,
        ``Zkc.Construction.ConnectionCertificate.Alignment.ownedHelper,
        ``Zkc.Construction.ConnectionCertificate.Alignment.receive] do
      unless occurrences value (· == rule) == 0 do
        throwError "placement audit: body constructor embedded at a use: {rule}"
    logInfo m!"PLACEMENT-AUDIT {name}: placements={count.getNat}; family_references={references}; inline_guard_helper_receive=0"

syntax "audit_exact_placements " ident num num : command
elab_rules : command
  | `(audit_exact_placements $identifier:ident $count:num $size:num) => liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo identifier
    let value := (← getConstInfo name).value!
    let exactBodies := value.getUsedConstants.filter fun constant =>
      (constant.toString.splitOn "retainedConnectionAlignment").length > 1
    unless exactBodies.size == count.getNat do
      throwError "exact placement control: expected {count.getNat} distinct retained bodies, found {exactBodies.size}"
    let mut calculations := #[]
    for body in exactBodies do
      let proof := (← getConstInfo body).value!
      calculations := calculations.push (occurrences proof
        (· == ``Zkc.Construction.ConnectionCertificate.Alignment.calculation))
    let callerCalculations := occurrences value
      (· == ``Zkc.Construction.ConnectionCertificate.Alignment.calculation)
    unless callerCalculations + calculations.foldl (· + ·) 0 == count.getNat * size.getNat do
      throwError "exact placement control: wrong total body calculation count: {calculations}"
    logInfo m!"EXACT-PLACEMENT-CONTROL {name}: distinct_body_declarations={exactBodies.size}; body_calculation_rules={calculations}; caller_calculation_rules={callerCalculations}"

end Tests.ConnectionPlacementMetrics
