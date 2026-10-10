import ArkLib.OracleReduction.FiatShamir.Basic
import VCVio.CryptoFoundations.FiatShamir.Sigma.Security
import VCVio.CryptoFoundations.FiatShamir.WithAbort.Security
import Tools.DeclarationAudit

/-! Record the status of selected upstream claims at the package's exact pins.
Importing this audit is not an adapter or a proof of a zkc security claim.
The optional library imports none of the incomplete theorems inspected here.
-/

open Lean Elab Command

run_cmd do
  for (name, complete) in [
      (`FiatShamir.euf_cma_to_nma, true),
      (`FiatShamir.euf_nma_bound, true),
      (`FiatShamir.euf_cma_bound, true),
      (`fiatShamir_completeness, false),
      (`FiatShamirWithAbort.euf_cma_bound, false),
      (`FiatShamirWithAbort.euf_cma_bound_perfectHVZK, false)] do
    let env ← getEnv
    unless env.contains name do
      throwError "selected upstream declaration is missing: {name}"
    let axioms ← Lean.collectAxioms name
    let clean := axioms.all Tools.DeclarationAudit.allowedAxioms.contains
    unless clean == complete do
      throwError "upstream status changed; review the proposition and consumers: {name}: {axioms}"
    if !complete && !axioms.contains `sorryAx then
      throwError "unreviewed upstream assumption: {name}: {axioms}"
    logInfo m!"UPSTREAM-STATUS {name}: complete={complete}, axioms={axioms}"
