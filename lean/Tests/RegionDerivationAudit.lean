import Tests.RegionDerivationControls
import ZkcTools.DeclarationAudit

/-! Inspect imported module ownership, including generated declarations, and
transitive axioms in both theorem types and proof bodies. -/

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`Zkc.Source.RegionDerivation, `Tests.RegionDerivation, `Tests.RegionDerivationControls]
    "REGION-DERIVATION-AUDIT-PASS" true

open Lean Elab Command in
run_cmd do
  for name in [``Zkc.Source.Region.Derivation.sound,
      ``Tests.RegionDerivation.schnorr_derive, ``Tests.RegionDerivation.round_derive,
      ``Tests.RegionDerivation.sumcheck_derive,
      ``Tests.RegionDerivation.occurrence_local_rewrites] do
    let info ← getConstInfo name
    let some proof := info.value? true | throwError "missing proof body: {name}"
    logInfo m!"PROOF-SIZE {name} expression-nodes-without-sharing={proof.sizeWithoutSharing}"

#eval (Tests.RegionDerivation.schnorr true).nodeCount
#eval (Tests.RegionDerivation.sumcheck 0).nodeCount
#eval (Tests.RegionDerivation.sumcheck 100).nodeCount
