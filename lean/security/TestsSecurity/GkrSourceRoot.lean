module

import ZkcSecurityExamples.Gkr.SourceValidator
import TestsSecurity.GkrRootEncoding

set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace TestsSecurity.GkrSourceRoot
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Realizations.Gkr ZkcExamples.Structured
open TestsSecurity.GkrRootEncoding

def handler : PIR.Handler (Occurrence.signature (uniformCarriers ℚ ℚ)) (List ℚ) String
  | .action (.receive (.field _) site _), value :: rest => ⟨.returned value, rest, [site]⟩
  | .action (.query site _ _), proof => by
      change PIR.Execution (List ℚ) String ℚ
      exact ⟨.returned 0, proof, [site]⟩
  | .action (.send site _ _), proof => ⟨.returned (), proof, [site]⟩
  | .enter frame, proof => ⟨.returned (), proof, ["enter:" ++ frame.site]⟩
  | .leave frame, proof => ⟨.returned (), proof, ["leave:" ++ frame.site]⟩
  | _, proof => ⟨.stopped .refused, proof, []⟩

/-- The source consumes the one complete layer and leaves the suffix intact. -/
theorem accepts : (SourceValidator.body (G := ℚ) oneLayer).run handler [3, 99] =
    ⟨.returned (.cons (some true) .nil), [99],
      ["enter:s57", GkrVerifier.lineConstantSite {}, GkrVerifier.lineChallengeSite {},
        GkrVerifier.lineDeliverySite {}, "leave:s57"]⟩ := by
  rw [SourceValidator.admitted_body oneLayer admitted]
  kernel_rfl

/-- A shape-valid false output rejects before the line challenge. No honest
producer premise is used to admit this validator statement. -/
theorem false_output_rejects : (SourceValidator.body (G := ℚ) falseOutput).run handler [3, 99] =
    ⟨.stopped .reject, [99], ["enter:s57", GkrVerifier.lineConstantSite {}]⟩ := by
  rw [SourceValidator.admitted_body falseOutput false_output_admitted]
  kernel_rfl

theorem malformed_add_rejects : (SourceValidator.body (G := ℚ) malformedZeroLayerAdd).run handler [99] =
    ⟨.stopped .reject, [99], []⟩ := by
  have actual : SourceValidator.body (G := ℚ) malformedZeroLayerAdd = .halt .reject := by
    kernel_rfl
  rw [actual]
  rfl

theorem malformed_mul_rejects : (SourceValidator.body (G := ℚ) malformedZeroLayerMul).run handler [99] =
    ⟨.stopped .reject, [99], []⟩ := by
  have actual : SourceValidator.body (G := ℚ) malformedZeroLayerMul = .halt .reject := by
    kernel_rfl
  rw [actual]
  rfl

/-- An absent validator capability stops at its actual query. The pending
layer stays open, and the unused proof suffix is preserved. -/
theorem missing_service :
    (Occurrence.participant (ringModel ℚ ℚ) GkrSourceViews.program 1
      (HonestProducerSource.currentInputs oneLayer.encoding oneLayer.outputs none)).run handler [3, 99] =
      ⟨.stopped .incomplete, [99], ["enter:s57", GkrVerifier.lineConstantSite {}]⟩ := by
  kernel_rfl

#print axioms accepts
#print axioms false_output_rejects
#print axioms malformed_add_rejects
#print axioms malformed_mul_rejects
#print axioms missing_service
end TestsSecurity.GkrSourceRoot
