module

public import ZkcSecurity.Endpoint.Knowledge
public import ZkcSecurity.Examples.Subjects.Schnorr.Evidence

@[expose] public section

/-! Maintained security endpoints for actual resource-free Domain execution.
Byte endpoint assembly is separate and retains its native transport obligations. -/

namespace ZkcSecurity.Examples.Subjects.Schnorr
open ZkcSecurity.Endpoint

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- The evidence of knowledge soundness of the ideal meaning for fixed
statements. -/
noncomputable def idealEvidence :=
  knowledge (F := F) (G := G) .idealMeaning PUnit.unit

/-- Also covered: knowledge soundness of the ideal meaning for fixed statements,
at the subject's artifacts and contract. -/
theorem knowledge_soundness :
    KnowledgeSoundness (art := artifacts) (holds := Contract.holds)
      (idealEvidence (F := F) (G := G)) :=
  ZkcSecurity.Endpoint.knowledge_soundness (idealEvidence)

end ZkcSecurity.Examples.Subjects.Schnorr
