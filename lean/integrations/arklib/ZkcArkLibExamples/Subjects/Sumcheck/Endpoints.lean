module

public import ZkcSecurity.Claims.Methods.Soundness
public import ZkcArkLibExamples.Subjects.Sumcheck.CompiledEndpoints
public import ZkcArkLibExamples.Subjects.Sumcheck.Lowering

@[expose] public section

/-! Maintained endpoint regression clients, independent of source claim authority.

These declarations preserve the prior endpoint APIs and mathematical statements.
Generated source receipts import this module but obtain their meaning only from
source requests and typed property/model registries. -/

namespace ZkcSecurity.Examples.Subjects.Sumcheck
open ZkcSecurity.Endpoint


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
