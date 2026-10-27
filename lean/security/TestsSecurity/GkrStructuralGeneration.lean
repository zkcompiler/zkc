import ZkcSecurity.Realizations.Gkr.OriginalCertificates
import ZkcSecurity.Realizations.Gkr.Rebound.OriginalProducerRoot
import ZkcSecurity.Realizations.Gkr.Rebound.OriginalValidatorRoot
import ZkcSecurity.Generation.GkrConnections

/-! The alternate formal artifact has new live input references, one additional
root slot and different recursive callback selectors. Both full roots are
checked without changes to callback mathematics or the installation schema.
This control does not associate the alternate tree with canonical native bytes. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.GkrStructuralGeneration
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured ZkcExamples.Construction
open ZkcSecurity.Realizations.Gkr
open ZkcSecurity.Generation

-- Generator applicability is a syntax control, as in the other registered
-- construction bindings. The independently checked full certificates below
-- provide semantic authority, rather than a kernel evaluation of the printer.
run_cmd do
  let result ← Lean.Elab.Command.liftTermElabM do
    let term ← `(GkrConnections.inputFields 0 LayoutVariant.producer [])
    let expression ← Lean.Elab.Term.elabTerm term none
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let expression ← Lean.Meta.withTransparency .all <|
      Lean.Meta.reduce (← Lean.instantiateMVars expression)
    Lean.Meta.evalExpr (Except String (List (String × String)))
      (← Lean.Meta.inferType expression) expression
  match result with
  | .error "gkr-connection-input-interface" => pure ()
  | _ => Lean.throwError "mismatched GKR input descriptor accepted"

-- These descriptor definitions participate in the checked callback/loop
-- equations. Reuse those small equations rather than evaluating both complete
-- source/artifact discovery trees again in each control.
example (side : GkrSourceRouting.Side) :
    Rebound.OriginalRounds.validatorOffset side = OriginalRounds.validatorOffset side + 1 := by
  cases side <;> rfl
example (side : GkrSourceRouting.Side) :
    Rebound.OriginalRounds.validatorYielded side =
      (OriginalRounds.validatorYielded side).map (· + 1) := by
  cases side <;> rfl
example : Rebound.OriginalRounds.validatorInitial .left ≠ OriginalRounds.validatorInitial .left := by
  decide +kernel
example : LayoutVariant.validator ≠ CanonicalPair.Validator.participant := LayoutVariant.validator_changed
example : LayoutVariant.producer ≠ CanonicalPair.Producer.participant := LayoutVariant.producer_changed

/-- A descriptor from the canonical layout cannot certify the changed callback. -/
example {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] :
    True := by
  have _checked := Rebound.OriginalRounds.validator_body (F := F) (G := G) .left
  fail_if_success
    have wrong :
        (Rebound.OriginalRounds.validatorOffset .left,
          Rebound.OriginalRounds.validatorInitial .left,
          Rebound.OriginalRounds.validatorYielded .left) =
        (OriginalRounds.validatorOffset .left,
          OriginalRounds.validatorInitial .left,
          OriginalRounds.validatorYielded .left) := by
      kernel_rfl
  trivial

-- These declarations expose the same full Simulation and runM contracts as the
-- canonical pair, including live input ABI, returns, arbitrary replies/stops,
-- physical environments, history, nested occurrences and shared handler state.
#check Rebound.OriginalCertificates.producer
#check Rebound.OriginalCertificates.validator
#check Rebound.OriginalCertificates.producer_run
#check Rebound.OriginalCertificates.validator_run
#print axioms Rebound.OriginalCertificates.producer
#print axioms Rebound.OriginalCertificates.validator
#print axioms OriginalCertificates.producer
#print axioms OriginalCertificates.validator
end TestsSecurity.GkrStructuralGeneration
