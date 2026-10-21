module

public import ZkcSecurity.Endpoint.Knowledge
public import ZkcSecurity.Examples.Subjects.SchnorrAnd.Evidence

@[expose] public section

/-! Generated claims of the subject `schnorr-and`. Regenerate with
`lean/bridges/subject.py --write`.

The manifest claims knowledge soundness of the ideal meaning for fixed
statements. The claim is the registered endpoint applied to the subject's
evidence, stated at the subject's artifacts, its contract (`Contract.holds`):
the kernel checks that the evidence has that type.

The family constructor's evidence at every other endpoint and statement form the
subject covers is applied below the claim, at the same artifacts and contract. -/

namespace ZkcSecurity.Examples.Subjects.SchnorrAnd
open ZkcSecurity.Endpoint

set_option linter.unusedSectionVars false

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- The evidence of knowledge soundness of the ideal meaning for fixed
statements. -/
noncomputable def evidence :=
  knowledge (F := F) (G := G) .idealMeaning PUnit.unit

/-- The claim: knowledge soundness of the ideal meaning for fixed statements, at
the subject's artifacts and contract. -/
theorem knowledge_soundness :
    KnowledgeSoundness (art := artifacts) (holds := Contract.holds)
      (evidence (F := F) (G := G)) :=
  ZkcSecurity.Endpoint.knowledge_soundness (evidence)

end ZkcSecurity.Examples.Subjects.SchnorrAnd
