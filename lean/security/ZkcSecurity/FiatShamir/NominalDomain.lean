module

public import Zkc.Construction.DomainProducer

public section

/-! A property presentation retaining arbitrary nominal Domain payloads and
request-indexed raw replies. It uses the existing transcript Interface. A
receive checks its origin and exact recursive sort, even when two nominal
domains happen to have the same host carrier.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.NominalDomain
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
variable {carriers : Carriers}

inductive Operation (carriers : Carriers) where
  | receive (ty : Ty) (origin : Origin)
  | deliver (origin : Origin) (payload : Domain.Payload carriers)
  | query (origin : Origin) (supported : Domain.drawRequest origin = true)

abbrev signature (carriers : Carriers) : PIR.Signature where
  Op := Operation carriers
  Reply
    | .receive ty _ => carriers.Value ty
    | .deliver .. => Unit
    | .query origin _ => Domain.Raw (.challenge origin : Domain.Event carriers)

@[expose] def received (ty : Ty) (origin : Origin) :
    Domain.Event carriers → Option (carriers.Value ty)
  | .message actual payload => if actual = origin then payload.value ty else none
  | _ => none

@[expose] def interface : Interface (signature carriers) (Domain.Event carriers)
    (Domain.Payload carriers) Domain.Raw
  | .receive ty origin => .receive (.message origin) (received ty origin)
  | .deliver origin payload => .send (.message origin payload) ()
  | .query origin _ => .query (.challenge origin) some

theorem received_message (ty : Ty) (origin : Origin) (payload : Domain.Payload carriers) :
    received ty origin (.message origin payload) = payload.value ty := by
  simp only [received, ite_true]

/-- Wrong nominal domains and aggregate layouts are refused, independently of
host carrier equality. -/
theorem received_wrong_type (ty : Ty) (origin : Origin) (payload : Domain.Payload carriers)
    (different : payload.ty ≠ ty) : received ty origin (.message origin payload) = none := by
  rw [received_message, Domain.Payload.value_wrong_type different]

theorem received_wrong_origin (ty : Ty) (expected actual : Origin)
    (payload : Domain.Payload carriers) (different : actual ≠ expected) :
    received ty expected (.message actual payload) = none := by
  simp only [received, different, ite_false]

end ZkcSecurity.FiatShamir.NominalDomain
