import TestsSecurity.GkrCanonicalClaims
import ZkcTools.DeclarationAudit

/-! The canonical claims retain their complete public meanings. In particular,
adversarial source rejection takes exactly its false-statement premise, and
neither the compiled exports nor their receipts acquire an honest-input or
successful-execution premise. Count implicit and instance binders as well. -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← Lean.getEnv
  for (name, expected) in [
      (`ZkcSecurity.Realizations.Gkr.SourceValidator.rejected, 1),
      (`ZkcSecurity.Realizations.Gkr.CanonicalSource.rejected, 1),
      (`ZkcSecurity.Realizations.Gkr.CanonicalSoundness.reductionExport, 0),
      (`ZkcSecurity.Realizations.Gkr.CanonicalCompleteness.compiled_ideal_complete, 0),
      (`ZkcSecurity.Realizations.Gkr.Generated.SubjectCompletenessClaims.completeReceipt, 0),
      (`ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessClaims.request0Receipt, 0),
      (`ZkcSecurity.Realizations.Gkr.Generated.SubjectSoundnessClaims.request1Receipt, 0)] do
    let some declaration := env.find? name | throwError "missing GKR contract: {name}"
    let binders ← ZkcTools.Statements.premises declaration.type
    let premises := binders.filter (·.proof)
    unless premises.size = expected do
      throwError "GKR premise telescope changed for {name}: {premises.size}, expected {expected}"
    Lean.logInfo m!"GKR-SOURCE-TELESCOPE-PASS {name} proof-premises={premises.size}"

#print axioms ZkcSecurity.Realizations.Gkr.CanonicalSoundness.reductionExport
#print axioms ZkcSecurity.Realizations.Gkr.CanonicalCompleteness.compiled_ideal_complete
