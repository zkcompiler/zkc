module

public import ZkcSecurity.Endpoint.Soundness
public import ZkcSecurity.Examples.Subjects.Guess.Evidence

@[expose] public section

/-! Generated claims of the subject `guess`. Regenerate with
`lean/bridges/subject.py --write`.

The manifest claims ordinary soundness of the ideal meaning for adaptive
statements. The claim is the registered endpoint applied to the subject's
evidence in every bound application context, stated at the subject's artifacts,
its application claim (`Contract.falseStatement`) and exactly uniform challenges:
the kernel checks that the evidence has that type. -/

namespace ZkcSecurity.Examples.Subjects.Guess
open ZkcSecurity.Endpoint

set_option linter.unusedSectionVars false

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- The evidence of the claim in an application context. -/
noncomputable def evidence (application : String) :=
  soundness (F := F) (G := G) .adaptive ⟨application⟩

/-- Ordinary soundness of the ideal meaning for adaptive statements, at the
subject's artifacts, its application claim and exactly uniform challenges. -/
theorem adaptive_soundness (application : String) :
    AdaptiveSoundness (art := artifacts) (claim := Contract.falseStatement) (regime := Regime.exact F)
      (evidence (F := F) (G := G) application) :=
  ZkcSecurity.Endpoint.adaptive_soundness (evidence application)

end ZkcSecurity.Examples.Subjects.Guess
