import ZkcSecurity.Examples.EmbeddingEqualitySoundness
import Zkc.Construction.DomainExecutionLaws

/-! Refusal and necessity controls for the actual mixed-domain endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
noncomputable section
namespace TestsSecurity.EmbeddingEqualityControls
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.EmbeddingEquality
open ZkcSecurity.Domains.KoalaBearModel (model baseIdentity octicIdentity)
open ZkcExamples.Construction.EmbeddingEqualityBinding

set_option backward.isDefEq.respectTransparency false
local instance : Field Base := ZkcSecurity.Domains.KoalaBearModel.laws.fieldInstance baseIdentity (by decide)
local instance : Field Octic := ZkcSecurity.Domains.KoalaBearModel.laws.fieldInstance octicIdentity (by decide)
local instance : DecidableEq Base := model.fieldDecEq baseIdentity
local instance : DecidableEq Octic := model.fieldDecEq octicIdentity

theorem wrong_nominal_reply (a : Base) :
    (Domain.Payload.field baseIdentity a : Domain.Payload model.toCarriers).value
      (.field octicIdentity) = none := by
  simp [Domain.Payload.value, baseIdentity, octicIdentity]

/-- Even an identical host carrier cannot substitute a nominal field name. -/
theorem wrong_name_same_host (a : model.Field "unadmitted") :
    (Domain.Payload.field "unadmitted" a : Domain.Payload model.toCarriers).value
      (.field baseIdentity) = none := by
  simp [Domain.Payload.value, baseIdentity]

theorem nonquery_reply_is_unit (origin : Origin) (payload : Domain.Payload model.toCarriers) :
    Domain.Raw (Domain.Event.message origin payload) = Unit := rfl

theorem same_name_wrong_artifact :
    checkCompiled imported { artifact with returned := [14, 10] } ≠ .ok () := by
  decide +kernel

theorem same_name_preserved :
    ({ artifact with returned := [14, 10] } : Participant).symbol = artifact.symbol := rfl

theorem second_only_wrong_artifact :
    checkCompiled imported { artifact with returned := [18, 10] } ≠ .ok () := by
  decide +kernel

theorem dropping_second_check (c : Octic) :
    (0 : Base) ≠ 1 ∧
      decide (embedBase (0 : Base) + c = embedBase (0 : Base) + c) = true := by
  exact ⟨zero_ne_one, decide_eq_true rfl⟩

theorem dropping_first_check (c : Octic) :
    (0 : Base) ≠ 1 ∧
      decide (embedBase (1 : Base) + c = embedBase (1 : Base) + c) = true := by
  exact ⟨zero_ne_one, decide_eq_true rfl⟩

theorem both_checks_reject (u c : Octic) : decision (0 : Base) 1 u c = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact zero_ne_one (decision_sound 0 1 u c accepted)

theorem wrong_statement_shape :
    checkCompiled imported { artifact with inputs := [.data (.field baseIdentity)] } ≠ .ok () := by
  decide +kernel

theorem invalid_query_refuses (initial : History)
    (oracle : Domain.Oracle Id model.toCarriers Unit)
    (state : Domain.RuntimeState model.toCarriers Unit) :
    Domain.run .validator oracle
      (.call (.query initial ⟨"invalid", [], none⟩) (fun _ => .done ())) state =
      pure ⟨.stopped .refused, state, []⟩ :=
  Domain.bad_request_refuses oracle initial _ rfl _ state .validator

theorem wrong_nominal_compiled_refuses {m : Type → Type} [Monad m] [LawfulMonad m]
    (query : History → (event : Event) → m (Domain.Raw event))
    (a b fake : Base) (initial : History) (unread : Proof) :
    verifier query a b initial (.field baseIdentity fake :: unread) =
      pure (.stopped .refused, .field baseIdentity fake :: unread) := by
  rw [compiled_verifier_eq]
  simp [Domain.transform, Zkc.Transcript.transform, verifierView,
    Domain.interface, Domain.receivedValue, wrong_nominal_reply]

theorem fake_embedding_refused :
    ¬ EmbeddingLaw (fun a : Base => ZkcSecurity.Domains.KoalaBear.embed a + 1) := by
  intro law
  have bad := law.map_zero
  simp only [map_zero, zero_add] at bad
  exact one_ne_zero bad

#print axioms ZkcExamples.Construction.EmbeddingEqualityBinding.admitted
#print axioms ZkcExamples.Construction.EmbeddingEqualityBinding.compiled
#print axioms ZkcSecurity.Examples.EmbeddingEquality.compiled_verifier_eq
#print axioms ZkcSecurity.Examples.EmbeddingEquality.compiled_ideal_soundness
#print axioms ZkcSecurity.Examples.EmbeddingEqualityDomains.octic_numeric

end TestsSecurity.EmbeddingEqualityControls
