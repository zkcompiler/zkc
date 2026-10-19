module

public import ZkcSecurity.Endpoint.Soundness
public import ZkcSecurity.Examples.Subjects.Sumcheck.Evidence

@[expose] public section

/-! Generated claims of the subject `sumcheck`. Regenerate with
`lean/bridges/subject.py --write`.

The manifest claims ordinary soundness of program bytes for adaptive statements.
The claim is the registered endpoint applied to the subject's evidence in every
bound application context, stated at the subject's artifacts, its contract
(`Contract.falseStatement`) and its regime: the kernel checks that the evidence
has that type.

The family constructor's evidence at every other endpoint and statement form the
subject covers is applied below the claim, at the same artifacts, contract and
regime. -/

namespace ZkcSecurity.Examples.Subjects.Sumcheck
open ZkcSecurity.Endpoint

set_option linter.unusedSectionVars false

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The evidence of ordinary soundness of program bytes for adaptive statements
in an application context. -/
noncomputable def evidence (application : String) :=
  soundness (F := F) (G := G) .executableBytes .adaptive ⟨application⟩ lowering

/-- The claim: ordinary soundness of program bytes for adaptive statements, at
the subject's artifacts and contract. -/
theorem adaptive_soundness_bytes (application : String) :
    AdaptiveSoundnessBytes (art := artifacts) (claim := Contract.falseStatement) (regime := Regime.exact F)
      (evidence (F := F) (G := G) application) :=
  ZkcSecurity.Endpoint.adaptive_soundness_bytes (evidence application)

/-! ## Other covered endpoints and statement forms -/

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

/-- The evidence of ordinary soundness of program bytes for fixed statements. -/
noncomputable def fixedBytesEvidence :=
  soundness (F := F) (G := G) .executableBytes .fixed PUnit.unit lowering

/-- Also covered: ordinary soundness of program bytes for fixed statements, at
the subject's artifacts and contract. -/
theorem fixed_soundness_bytes :
    FixedSoundnessBytes (art := artifacts) (claim := Contract.falseStatement) (regime := Regime.exact F)
      (fixedBytesEvidence (F := F) (G := G)) :=
  ZkcSecurity.Endpoint.fixed_soundness_bytes (fixedBytesEvidence)

end ZkcSecurity.Examples.Subjects.Sumcheck
