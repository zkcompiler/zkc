import Tests.DeriveRegion
import Tests.DeriveRegionCallbacks
import Tests.DeriveRegionNested
import Tests.RegionViewControls
import ZkcTools.DeclarationAudit

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Source.DeriveRegion, `Zkc.Source.DerivationLaws, `Zkc.Source.RegionView,
     `Zkc.Source.Structured.ProjectedBody, `Zkc.Source.Structured.DerivationRules,
     `Zkc.Source.Structured.EqualityDerivationRules,
     `Tests.DeriveRegion, `Tests.DeriveRegionCallbacks, `Tests.DeriveRegionNested,
     `Tests.DeriveRegionSchnorr, `Tests.DeriveRegionSumcheck, `Tests.RegionViewControls]
    "DERIVE-REGION-AUDIT-PASS" true

#print axioms Tests.DeriveRegion.obligation_resumed
#print axioms Tests.DeriveRegionCallbacks.symbolic_repeat
#print axioms Tests.DeriveRegionNested.nested_callback_open
#print axioms Tests.DeriveRegionSources.schnorr_formula_reversed
#print axioms Tests.DeriveRegionSources.sum_formula_automated

open Lean Elab Command in
run_cmd do
  for name in [``Tests.DeriveRegion.commuted,
      ``Tests.DeriveRegionCallbacks.nested,
      ``Tests.DeriveRegionCallbacks.symbolic_repeat,
      ``Tests.DeriveRegionSources.schnorrView,
      ``Tests.DeriveRegionSources.schnorr_formula_reversed,
      ``Tests.DeriveRegionSources.sumAddView,
      ``Tests.DeriveRegionSources.sum_add_reversed,
      ``Tests.DeriveRegionSources.sum_formula_automated,
      ``Tests.DeriveRegionSources.sum_formula_reversed] do
    let info ← getConstInfo name
    let some value := info.value? true | throwError "missing value for {name}"
    logInfo m!"EXPRESSION-SIZE {name} nodes-without-sharing={value.sizeWithoutSharing}"

#reduce Tests.DeriveRegionSources.schnorrView.nodeCount
#reduce Tests.DeriveRegionSources.sumAddView.nodeCount
