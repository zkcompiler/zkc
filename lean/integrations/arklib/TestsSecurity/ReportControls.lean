import ZkcSecurity.Examples.Subjects.Schnorr.Claims

/-! Emitted declarations for the assurance report's premise audit.

Each theorem applies the registered knowledge endpoint to the Schnorr subject's
evidence, as a generated application does. `clean` states no premise of its
own; the others add one premise the registry does not know: an explicit
`False`, an implicit `False` and a `Fact False` instance. The records check
emits them in detail and requires the report's telescope audit to accept the
first and to name the added premise of each other one as omitted. -/

namespace TestsSecurity.ReportControls
open ZkcSecurity.Endpoint
open ZkcSecurity.Examples.Subjects.Schnorr

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]

/-- The passing counterpart: no premise of its own. -/
theorem clean :
    KnowledgeSoundness (art := artifacts) (holds := Contract.holds)
      (idealEvidence (F := F) (G := G)) :=
  ZkcSecurity.Endpoint.knowledge_soundness (idealEvidence)

/-- An explicit `False` premise. -/
theorem explicit_false (_assumption : False) :
    KnowledgeSoundness (art := artifacts) (holds := Contract.holds)
      (idealEvidence (F := F) (G := G)) :=
  ZkcSecurity.Endpoint.knowledge_soundness (idealEvidence)

/-- An implicit `False` premise. -/
theorem implicit_false {_assumption : False} :
    KnowledgeSoundness (art := artifacts) (holds := Contract.holds)
      (idealEvidence (F := F) (G := G)) :=
  ZkcSecurity.Endpoint.knowledge_soundness (idealEvidence)

/-- An unregistered propositional instance premise. -/
theorem instance_premise [Fact False] :
    KnowledgeSoundness (art := artifacts) (holds := Contract.holds)
      (idealEvidence (F := F) (G := G)) :=
  ZkcSecurity.Endpoint.knowledge_soundness (idealEvidence)

end TestsSecurity.ReportControls
