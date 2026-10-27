module

import ZkcSecurity.Realizations.Gkr.CanonicalSource
import TestsSecurity.GkrRootEncoding

set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
namespace TestsSecurity.GkrSourceRoot
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Realizations.Gkr ZkcExamples.Structured
open TestsSecurity.GkrRootEncoding

def handler : PIR.Handler (Actions ℚ ℚ) (List ℚ) String
  | .receive (.field _) site _, value :: rest => ⟨.returned value, rest, [site]⟩
  | .query site _ _, proof => ⟨.returned 0, proof, [site]⟩
  | .send site _ _, proof => ⟨.returned (), proof, [site]⟩
  | _, proof => ⟨.stopped .refused, proof, []⟩

/-- The source consumes the one complete layer and leaves the suffix intact. -/
theorem accepts : (Source.body (G := ℚ) oneLayer).run handler [3, 99] =
    ⟨.returned (some true), [99],
      [GkrVerifier.lineConstantSite {}, GkrVerifier.lineChallengeSite {},
        GkrVerifier.lineDeliverySite {}]⟩ := by
  rw [Source.admitted_binding oneLayer admitted]
  kernel_rfl

/-- A shape-valid false output rejects before the line challenge. No honest
producer premise is used to admit this validator statement. -/
theorem false_output_rejects : (Source.body (G := ℚ) falseOutput).run handler [3, 99] =
    ⟨.stopped .reject, [99], [GkrVerifier.lineConstantSite {}]⟩ := by
  rw [Source.admitted_binding falseOutput false_output_admitted]
  kernel_rfl

theorem malformed_add_rejects : (Source.body (G := ℚ) malformedZeroLayerAdd).run handler [99] =
    ⟨.stopped .reject, [99], []⟩ := by
  have actual : Source.body (G := ℚ) malformedZeroLayerAdd = .halt .reject := by
    kernel_rfl
  rw [actual]
  rfl

theorem malformed_mul_rejects : (Source.body (G := ℚ) malformedZeroLayerMul).run handler [99] =
    ⟨.stopped .reject, [99], []⟩ := by
  have actual : Source.body (G := ℚ) malformedZeroLayerMul = .halt .reject := by
    kernel_rfl
  rw [actual]
  rfl

#print axioms accepts
#print axioms false_output_rejects
#print axioms malformed_add_rejects
#print axioms malformed_mul_rejects
end TestsSecurity.GkrSourceRoot
