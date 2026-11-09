module

import Zkc.Tools.Protocol.Construction
import Zkc.Tests.Protocol.Models.AdaptiveChecks

set_option experimental.vcgen true
open PIR ProtocolProof Std.WP ProtocolProofExamples.AdaptiveChecks

namespace ProtocolProofExamples.ProcessContinuations
noncomputable section

abbrev upperLogic : WPMonad (Process Challenge)
    (Potential Unit Unit)ᵒᵈ (Stop → Potential Unit Unit)ᵒᵈ :=
  coinSpec.toUpperWPMonad coinSpec_mono
attribute [local instance] upperLogic

/-- Direct call continuations use the ordinary bind path, including a reached failure. -/
def caller : Process Challenge Bool :=
  .call () fun first => if first then .call () .done else .halt .reject

theorem caller_upper :
    ⦃OrderDual.toDual (fun _ : Unit × List Unit => half * half)⦄ caller
    ⦃fun accepted => OrderDual.toDual (fun _ => reward accepted 1);
      OrderDual.toDual (fun _ _ => 0)⦄ := by
  unfold caller
  construct_region
  change ∀ state, _ ≤ _
  intro state
  simp [coinSpec, OperationSpec.outcomePost, reward]

abbrev lowerLogic : WPMonad (Process Challenge)
    (Potential Unit Unit) (Stop → Potential Unit Unit) := coinSpec.toWPMonad coinSpec_mono
attribute [local instance] lowerLogic

theorem caller_lower :
    ⦃fun _ : Unit × List Unit => half * half⦄ caller
    ⦃fun accepted => fun _ => reward accepted 1; fun _ _ => 0⦄ := by
  unfold caller
  construct_region
  simp [coinSpec, OperationSpec.outcomePost, reward]

end
end ProtocolProofExamples.ProcessContinuations
