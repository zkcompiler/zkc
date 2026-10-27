module

public import ZkcSecurity.Endpoint.Soundness
public import ZkcArkLib.Examples.Subjects.Sumcheck.Evidence

@[expose] public section

/-! Maintained security endpoints for actual resource-free Domain execution.
Byte endpoint assembly is separate and retains its native transport obligations. -/

namespace ZkcSecurity.Examples.Subjects.Sumcheck
open ZkcSecurity.Endpoint

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The evidence of ordinary soundness of the ideal meaning for fixed
statements. -/
noncomputable def fixedIdealEvidence :=
  soundness (F := F) (G := G) .idealMeaning .fixed PUnit.unit PUnit.unit

/-- Also covered: ordinary soundness of the ideal meaning for fixed statements,
at the subject's artifacts and contract. -/
theorem fixed_soundness :
    FixedSoundness (art := artifacts) (claim := Contract.falseStatement) (regime := Regime.exact F)
      (fixedIdealEvidence (F := F) (G := G)) :=
  ZkcSecurity.Endpoint.fixed_soundness (fixedIdealEvidence)

/-- The evidence of ordinary soundness of the ideal meaning for adaptive
statements in an application context. -/
noncomputable def adaptiveIdealEvidence (application : String) :=
  soundness (F := F) (G := G) .idealMeaning .adaptive ⟨application⟩ PUnit.unit

/-- Also covered: ordinary soundness of the ideal meaning for adaptive
statements, at the subject's artifacts and contract. -/
theorem adaptive_soundness (application : String) :
    AdaptiveSoundness (art := artifacts) (claim := Contract.falseStatement) (regime := Regime.exact F)
      (adaptiveIdealEvidence (F := F) (G := G) application) :=
  ZkcSecurity.Endpoint.adaptive_soundness (adaptiveIdealEvidence application)

end ZkcSecurity.Examples.Subjects.Sumcheck
