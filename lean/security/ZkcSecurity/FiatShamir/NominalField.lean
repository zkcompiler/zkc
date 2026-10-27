module

public import Zkc.Construction.DomainTranscript
public import ZkcSecurity.FiatShamir.LosslessPresentation

@[expose] public section

/-! Field operations with exact nominal transcript occurrences and payload sorts.
The uniform host carriers never identify distinct nominal fields. The lossless
law uses the actual decoder equations and preserves every typed reply.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.NominalField
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir.Original

variable {F G : Type} [Field F]

inductive Operation (F : Type) (field : String) where
  | receive (origin : Origin)
  | deliver (origin : Origin) (value : F)
  | query (origin : Origin) (request : origin.request = some (.draw field))

abbrev signature (F : Type) (field : String) : PIR.Signature where
  Op := Operation F field
  Reply
    | .receive _ => F
    | .deliver .. => Unit
    | .query .. => F

def received (field : String) (origin : Origin) :
    Domain.Event (uniformCarriers F G) → Option F
  | .message actual payload => if actual = origin then payload.value (.field field) else none
  | _ => none

def interface (field : String) : Interface (signature F field)
    (Domain.Event (uniformCarriers F G)) (Domain.Payload (uniformCarriers F G)) Domain.Raw
  | .receive origin =>
      .receive (.message origin) (received field origin)
  | .deliver origin value => .send (.message origin (.field field value)) ()
  | .query origin request => .query (.challenge origin) fun raw =>
      some (by simpa only [Domain.Raw, request, Request.draw] using raw)

omit [Field F] in
/-- The nominal decoder checks both the occurrence and the precise field sort.
Malformed messages are refused by the existing transcript transform. -/
theorem received_message (field : String) (origin : Origin)
    (payload : Domain.Payload (uniformCarriers F G)) :
    received field origin (.message origin payload) = payload.value (.field field) := by
  simp only [received, ite_true]

/-- The laws are global for this interface: no schedule, root, configuration
or full-result encoder is required by a caller. -/
theorem lossless (field : String) :
    LosslessInterface (interface (F := F) (G := G) field) where
  receive := by
    intro operation ty event recover reply absorbed decoded
    cases operation with
    | deliver => cases absorbed
    | query => cases absorbed
    | receive origin =>
      cases absorbed
      have sameSort : ty = .field field := by
        have recovered : received (G := G) field origin (.message origin (.field field (0 : F))) = some 0 := by
          simp [received_message, Domain.Payload.value]
        have recognized := congrArg Option.isSome ((decoded (.field field 0)).symm.trans recovered)
        simp only [Option.isSome_map, Domain.Payload.value_isSome,
          Option.isSome_some] at recognized
        exact (of_decide_eq_true recognized).symm
      subst ty
      have identity : ∀ value : F, reply value = value := by
        intro value
        have same := decoded (.field field value)
        simp [received_message, Domain.Payload.value] at same
        exact same.symm
      refine ⟨?_, fun value => ⟨.field field value, rfl⟩⟩
      simpa only [show reply = id from funext identity] using Function.bijective_id
  query := by
    intro operation origin reply absorbed
    cases operation with
    | receive => cases absorbed
    | deliver => cases absorbed
    | query actual request =>
      injection absorbed with sameOrigin sameDecoder
      cases sameOrigin
      have identity : ∀ raw : Domain.Raw (.challenge origin : Domain.Event (uniformCarriers F G)),
          reply raw = (by simpa only [Domain.Raw, request, Request.draw] using raw) := by
        intro raw
        exact (Option.some.inj (congrFun (eq_of_heq sameDecoder) raw)).symm
      rw [funext identity]
      exact eq_mp_bijective _
  send := by
    intro operation event value absorbed reply
    cases operation with
    | receive => cases absorbed
    | query => cases absorbed
    | deliver origin sent => exact Subsingleton.elim reply value

end ZkcSecurity.FiatShamir.NominalField
