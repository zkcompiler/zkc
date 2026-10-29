import ZkcSecurity.Examples.Subjects.Schnorr.Claims
import ZkcArkLib.Examples.Subjects.Guess.Claims

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

namespace TestsSecurity.ReportControls
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Endpoint ZkcSecurity.FiatShamir
open ZkcSecurity.Examples.Subjects.Guess

variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Its proof depends on type parameters, instances and the application string,
but on no assumption. The emitter must classify it as a proof. -/
noncomputable def proved_binding (application : String) :
    SoundnessEvidence (F := F) (G := G) artifacts .idealMeaning .adaptive
      Contract.falseStatement (Regime.exact F) :=
  { soundness .idealMeaning .adaptive ⟨application⟩ PUnit.unit with
    hypotheses := [{ identifier := "binding.statement-determination"
                     category := .binding .statementDetermination
                     claim := Zkc.Transcript.Determined (policyCodec (F := F) (G := G) artifacts.publics (by rfl) application).encode
                     status := .proved (policyCodec (F := F) (G := G) artifacts.publics (by rfl) application).determined }] }

/-- An actual assumption binder in a .proved term must be reported as a premise. -/
noncomputable def assumed_binding (application : String)
    (assumption : Zkc.Transcript.Determined (policyCodec (F := F) (G := G) artifacts.publics (by rfl) application).encode) :
    SoundnessEvidence (F := F) (G := G) artifacts .idealMeaning .adaptive
      Contract.falseStatement (Regime.exact F) :=
  { proved_binding application with
    hypotheses := [{ identifier := "binding.statement-determination"
                     category := .binding .statementDetermination
                     claim := Zkc.Transcript.Determined (policyCodec (F := F) (G := G) artifacts.publics (by rfl) application).encode
                     status := .proved assumption }] }

/-- Merely having an unused propositional binder does not make a proof assumed. -/
noncomputable def unused_assumption_binding (application : String) (_assumption : False) :
    SoundnessEvidence (F := F) (G := G) artifacts .idealMeaning .adaptive
      Contract.falseStatement (Regime.exact F) :=
  proved_binding application

/-- Fact wraps an actual proposition even though Fact itself is Type-valued. -/
noncomputable def fact_binding (application : String)
    [Fact (Zkc.Transcript.Determined (policyCodec (F := F) (G := G) artifacts.publics (by rfl) application).encode)] :
    SoundnessEvidence (F := F) (G := G) artifacts .idealMeaning .adaptive
      Contract.falseStatement (Regime.exact F) :=
  assumed_binding application Fact.out

/-- An inhabited proposition can hide an assumption behind an allowed class. -/
noncomputable def inhabited_false_binding (application : String) [Inhabited False] :
    SoundnessEvidence (F := F) (G := G) artifacts .idealMeaning .adaptive
      Contract.falseStatement (Regime.exact F) :=
  assumed_binding application (False.elim (default : False))

/-- A proof-carrying instance must remain a premise even when its proposition
is the actual named hypothesis rather than False. -/
noncomputable def inhabited_proof_binding (application : String)
    [Inhabited (Zkc.Transcript.Determined (policyCodec (F := F) (G := G) artifacts.publics (by rfl) application).encode)] :
    SoundnessEvidence (F := F) (G := G) artifacts .idealMeaning .adaptive
      Contract.falseStatement (Regime.exact F) :=
  assumed_binding application default

/-- Raising a proof into Type does not make it an ordinary model carrier. -/
noncomputable def lifted_proof_binding (application : String)
    [Inhabited (PLift (Zkc.Transcript.Determined
      (policyCodec (F := F) (G := G) artifacts.publics (by rfl) application).encode))] :
    SoundnessEvidence (F := F) (G := G) artifacts .idealMeaning .adaptive
      Contract.falseStatement (Regime.exact F) :=
  assumed_binding application (default : PLift _).down

end TestsSecurity.ReportControls
