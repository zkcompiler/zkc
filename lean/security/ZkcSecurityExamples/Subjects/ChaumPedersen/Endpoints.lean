module

public import ZkcSecurity.Claims.Methods.KnowledgeEndpoint
public import ZkcSecurityExamples.Subjects.ChaumPedersen.Evidence

@[expose] public section

/-! Maintained endpoint regression clients, independent of source claim authority.

These declarations preserve the prior endpoint APIs and mathematical statements.
Generated source receipts import this module but obtain their meaning only from
source requests and typed property/model registries. -/

namespace ZkcSecurity.Examples.Subjects.ChaumPedersen
open ZkcSecurity.Endpoint


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

end ZkcSecurity.Examples.Subjects.ChaumPedersen
