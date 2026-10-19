module

public import ZkcSecurity.Endpoint.Knowledge
public import ZkcSecurity.Examples.Subjects.Schnorr.Evidence

@[expose] public section

/-! Generated claims of the subject `schnorr`. Regenerate with
`lean/bridges/subject.py --write`.

The manifest claims knowledge soundness of program bytes for fixed statements.
The claim is the registered endpoint applied to the subject's evidence, stated
at the subject's artifacts and the witness relation of the admitted original's
contract (`Contract.holds`): the kernel checks that the evidence has that type. -/

namespace ZkcSecurity.Examples.Subjects.Schnorr
open ZkcSecurity.Endpoint

set_option linter.unusedSectionVars false

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- The evidence of the claim. -/
noncomputable def evidence := knowledge (F := F) (G := G) .executableBytes lowering

/-- Knowledge soundness of program bytes for fixed statements, at the subject's
artifacts and its contract's witness relation. -/
theorem knowledge_soundness_bytes :
    KnowledgeSoundnessBytes (art := artifacts) (holds := Contract.holds) (evidence (F := F) (G := G)) :=
  ZkcSecurity.Endpoint.knowledge_soundness_bytes evidence

end ZkcSecurity.Examples.Subjects.Schnorr
