module

public import ProtocolProof.Claims.Transfer
public import ProtocolProofExamples.ClaimBoundaries

/-! Security transfers cannot improve an invalid fixed claim by choosing another proof route. -/

public section
open ProtocolProof ProtocolProofExamples.ClaimBoundaries

namespace ProtocolProofExamples.TransferControls

/-- An established model event does not authorize accepting a negative instance at zero error. -/
theorem accepting_negative_not_transferable :
    ¬ Nonempty (UpperTransfer (acceptsStatement 2).toUpper (acceptsStatement 1).toUpper) := by
  rintro ⟨transfer⟩
  exact accepting_negative_refused (transfer.establish accepting_gap_established)

/-- Lost honest mass cannot be recovered by a reduction or an infinite loss annotation. -/
theorem honest_abort_not_transferable :
    ¬ Nonempty (LowerTransfer (completeness 0).toLower
      (completeness (2 : ENNReal)⁻¹).toLower) := by
  rintro ⟨transfer⟩
  exact honest_perfect_completeness_refused (transfer.establish honest_half_completeness)

end ProtocolProofExamples.TransferControls
