module

public import ZkcSecurity.Families.Sumcheck.TableComponentNominal
public import ZkcSecurity.FiatShamir.LosslessPresentation

@[expose] public section

/-! The table component's nominal interface loses no typed replies. The proof
uses decoder equality on actual payloads, including nominal sort rejection;
uniform host field carriers alone never justify a change of nominal field.
-/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent.Nominal
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir.Original

variable {F G : Type} [Field F]

/-- The laws are global for this interface: no schedule, root, configuration
or full-result encoder is required by a table-component caller. -/
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
        simp only [Option.isSome_map, Domain.Payload.value_isSome, Domain.Payload.ty,
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

end ZkcSecurity.Families.Sumcheck.TableComponent.Nominal
