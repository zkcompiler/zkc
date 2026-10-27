module

import ZkcExamples.Structured.GkrLayerReading
import ZkcExamples.Structured.GkrProverContinuation
import ZkcSecurity.Realizations.Gkr.CanonicalSource

set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace TestsSecurity.GkrCurrentReading
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured

/-- Zero rounds preserve the complete pending prefix without any interaction. -/
theorem zero_rounds (a b claim : ℚ) :
    GkrRoundsNormalForms.verifierRoundsProcess (F := ℚ) (G := ℚ) {}
      (some [a, b]) (some claim) (some 0) (some 0) =
      .done (GkrRoundsReading.roundsResults ([a, b], claim)) := by kernel_rfl

/-- The source's empty pending-point case is a successful split, not a refusal. -/
theorem empty_split :
    invoke (GkrRoundsReading.closed (F := ℚ) (G := ℚ))
      GkrSourceBodies.sourceHelper50Helper (.cons [] .nil) =
      .done (.cons [] (.cons [] .nil)) := by kernel_rfl

#print axioms GkrRoundsReading.round_prefix
#print axioms GkrRoundsReading.repeat_prefix
#print axioms GkrRoundsReading.reads
#print axioms GkrLayerReading.split_pending_plain
#print axioms GkrLayerReading.layer_reads
#print axioms GkrLayerReading.layers_reads
#print axioms GkrSourceContinuation.participant
#print axioms GkrProverContinuation.participant
#print axioms GkrSourceVerifier.verifier_reads
#print axioms ZkcSecurity.Realizations.Gkr.Source.admitted_represents
#print axioms ZkcSecurity.Realizations.Gkr.Source.binding
#print axioms ZkcSecurity.Realizations.Gkr.Source.admitted_binding
#print axioms ZkcSecurity.Realizations.Gkr.Source.rejected
#print axioms ZkcSecurity.Realizations.Gkr.Source.run_binding
#print axioms ZkcSecurity.Realizations.Gkr.CanonicalSource.rejected
#print axioms zero_rounds
#print axioms empty_split
end TestsSecurity.GkrCurrentReading
