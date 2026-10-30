module

public import ZkcSecurity.Claims.Methods.KnowledgeEndpoint
public import ZkcSecurityExamples.Subjects.Schnorr.CompiledEndpoints
public import ZkcSecurityExamples.Subjects.Schnorr.Lowering

@[expose] public section

/-! Maintained endpoint regression clients, independent of source claim authority.

These declarations preserve the prior endpoint APIs and mathematical statements.
Generated source receipts import this module but obtain their meaning only from
source requests and typed property/model registries. -/

namespace ZkcSecurity.Examples.Subjects.Schnorr
open ZkcSecurity.Endpoint


variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- The evidence of knowledge soundness of program bytes for fixed statements. -/
noncomputable def evidence :=
  knowledge (F := F) (G := G) .executableBytes lowering

/-- The claim: knowledge soundness of program bytes for fixed statements, at the
subject's artifacts and contract. -/
theorem knowledge_soundness_bytes :
    KnowledgeSoundnessBytes (art := artifacts) (holds := Contract.holds)
      (evidence (F := F) (G := G)) :=
  ZkcSecurity.Endpoint.knowledge_soundness_bytes (evidence)


end ZkcSecurity.Examples.Subjects.Schnorr
