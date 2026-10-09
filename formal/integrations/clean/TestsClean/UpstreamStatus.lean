import ZkcClean.Specification
import ZkcClean.Native
import TestsClean.Bits
import TestsClean.Nested
import TestsClean.Refusals
import Tools.DeclarationAudit

/-! Axiom status of the selected bridge theorems and of the upstream Clean
source declarations at the pinned revision. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted, including inside upstream proof cones. The
generated `TestsClean.Audit` separately audits every package-owned declaration.
-/

open Lean Elab Command

run_cmd do
  let bridge := [``ZkcClean.flatten_eq_toFlat, ``ZkcClean.exportComponent_ok,
    ``ZkcClean.exportOperations_eq_ok, ``ZkcClean.exportOperations_refused,
    ``ZkcClean.export_expression,
    ``ZkcClean.evaluateAt_decode, ``ZkcClean.decode_export, ``ZkcClean.holds_iff,
    ``ZkcClean.table_holds_iff, ``ZkcClean.constraintsHold_data,
    ``ZkcClean.guarantees_of_export, ``ZkcClean.row_spec, ``ZkcClean.table_spec,
    ``ZkcClean.export_ring, ``ZkcClean.component_ring, ``ZkcClean.ring_decode,
    ``ZkcClean.native_ring, ``ZkcClean.component_native_ring,
    ``ZkcClean.no_presentation_of_not_prime, ``Zkc.Relation.AIR.Expr.toRing_eval]
  let upstream := [``Expression.eval, ``Environment.fromArray, ``Operations.ConstraintsHold,
    ``Operations.constraints_toFlat, ``Operations.lookups_toFlat,
    ``Operations.interactions_toFlat, ``FiniteField.fromNat_val,
    ``Air.Flat.Component.weakSoundness, ``Air.Flat.Table.weakSoundness,
    ``GeneralFormalCircuit.original_full_soundness, ``Gadgets.ToBits.toBits,
    ``Gadgets.IsEqual.circuit, ``Gadgets.Addition8Full.circuit, ``add8,
    ``FlatOperation.dynamicWitnesses]
  for (label, names) in [("BRIDGE-AXIOMS", bridge), ("UPSTREAM-AXIOMS", upstream)] do
    for name in names do
      unless (← getEnv).contains name do
        throwError "selected declaration is missing: {name}"
      let axioms ← Lean.collectAxioms name
      unless axioms.all Tools.DeclarationAudit.allowedAxioms.contains do
        throwError "unexpected axiom in {name}: {axioms}"
      logInfo m!"{label} {name}: {axioms}"
