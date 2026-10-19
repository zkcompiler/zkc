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
has that type. -/

namespace ZkcSecurity.Examples.Subjects.Sumcheck
open ZkcSecurity.Endpoint

set_option linter.unusedSectionVars false

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- The evidence of the claim in an application context. -/
noncomputable def evidence (application : String) :=
  soundness (F := F) (G := G) .executableBytes .adaptive ⟨application⟩ lowering

/-- The claim: ordinary soundness of program bytes for adaptive statements, at
the subject's artifacts and contract. -/
theorem adaptive_soundness_bytes (application : String) :
    AdaptiveSoundnessBytes (art := artifacts) (claim := Contract.falseStatement) (regime := Regime.exact F)
      (evidence (F := F) (G := G) application) :=
  ZkcSecurity.Endpoint.adaptive_soundness_bytes (evidence application)

end ZkcSecurity.Examples.Subjects.Sumcheck
