module

public import ZkcSecurity.Bindings.Transcript.DomainReduction

@[expose] public section

/-! Uniform scalar components can use nominal histories directly. The existing
structured participant signature specializes definitionally at uniformCarriers;
no equality of nominal field names or old uniform transcript events is assumed. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.DomainReduction
open Zkc.Source Zkc.Construction
variable {F G : Type}

/-- The uniform component's operations with the actual nominal payloads/events
and event-indexed query answers. This is the existing Domain.interface. -/
def uniformInterface (context : Context) :
    Typed.Interface (Structured.participantInterface F G)
      (Domain.Event (Structured.uniformCarriers F G))
      (Domain.Payload (Structured.uniformCarriers F G)) Domain.Raw := by
  with_reducible exact Domain.interface (carriers := Structured.uniformCarriers F G) context

theorem uniformInterface_receive (context : Context) (ty : Structured.Ty)
    (site : String) (sender : Nat) :
    uniformInterface (F := F) (G := G) context (.receive ty site sender) =
      .receive (fun payload => .message (context.message site sender context.validator) payload)
        (Domain.receivedValue context ty site sender) := by
  rfl

/-- The dependent raw carrier reduces to F only because this exact occurrence
requests the named field under the uniform carrier specialization. -/
theorem uniformInterface_query (context : Context) (replacement : Replacement)
    (profile : context.profile = .fiatShamir replacement) (site field : String)
    (arguments : Values (Structured.assignment F G) (Structured.services.arguments field)) :
    uniformInterface context (.query site field arguments) =
      .query (.challenge (context.query site (.draw field))) some := by
  simp only [uniformInterface, Domain.interface, profile]

end ZkcSecurity.FiatShamir.DomainReduction
