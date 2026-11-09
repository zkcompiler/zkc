import Zkc.Tests.IR.DeriveRegion
import Zkc.Tests.IR.DeriveRegionCallbacks
import Zkc.Tests.IR.DeriveRegionNested
import Zkc.Tests.Applications.IR.RegionViewControls
import Zkc.Tools.Program.DeclarationAudit

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Program.Source.DeriveRegion, `Zkc.Program.Source.DerivationLaws, `Zkc.Program.Source.RegionView, `Zkc.IR.Source.Structured.ProjectedBody, `Zkc.IR.Source.Structured.DerivationRules, `Zkc.IR.Source.Structured.EqualityDerivationRules, `Zkc.Tests.IR.DeriveRegion, `Zkc.Tests.IR.DeriveRegionCallbacks, `Zkc.Tests.IR.DeriveRegionNested, `Zkc.Tests.Applications.IR.DeriveRegionSchnorr, `Zkc.Tests.Applications.IR.DeriveRegionSumcheck, `Zkc.Tests.Applications.IR.RegionViewControls]
    "DERIVE-REGION-AUDIT-PASS" true

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
