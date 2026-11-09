module

public import Zkc.Verification.Bindings.Transcript.DomainReduction
public import Zkc.Program.Semantics.OperationSupport

@[expose] public section

/-! Local lossless decoder laws for nominal presentations. They quantify over
actual decoder equations and every reply, independently of any whole-source
simulation or checkpoint-erasure certificate. -/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.Original
open PIR Zkc.Source Zkc.Construction Zkc.Transcript

variable {carriers : Structured.Carriers} {I : PIR.Signature} {A : Type}

/-- Every read reply is represented by a proof payload, actual receive/query
reply maps are bijections, and a send has only its selected reply. The payload
law excludes service handles, which have no proof representation. Quantifying
over decoder equality prevents host carrier equality from erasing nominal sorts.
-/
structure LosslessInterface
    (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw) : Prop where
  receive : ∀ (operation : I.Op) (ty : Structured.Ty)
    (event : Domain.Payload carriers → Domain.Event carriers)
    (recover : Domain.Event carriers → Option (I.Reply operation))
    (reply : carriers.Value ty → I.Reply operation),
    absorb operation = .receive event recover →
    (∀ payload, recover (event payload) = (payload.value ty).map reply) →
    Function.Bijective reply ∧
      (∀ value : carriers.Value ty, ∃ payload : Domain.Payload carriers,
        Domain.Payload.ofValue ty value = some payload)
  query : ∀ (operation : I.Op) (origin : Origin)
    (reply : Domain.Raw (.challenge origin : Domain.Event carriers) → I.Reply operation),
    absorb operation = .query (.challenge origin) (some ∘ reply) → Function.Bijective reply
  send : ∀ (operation : I.Op) (event : Domain.Event carriers) (value : I.Reply operation),
    absorb operation = .send event value → ∀ reply : I.Reply operation, reply = value

/-- Local lossless laws for one operation. Every read reply is represented by a
proof payload, actual receive/query reply maps are bijections, and a send has
only its selected reply. The payload
law excludes service handles, which have no proof representation. Quantifying
over decoder equality prevents host carrier equality from erasing nominal sorts.
-/
structure LosslessOperation
    (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw) (operation : I.Op) : Prop where
  receive : ∀ (ty : Structured.Ty)
    (event : Domain.Payload carriers → Domain.Event carriers)
    (recover : Domain.Event carriers → Option (I.Reply operation))
    (reply : carriers.Value ty → I.Reply operation),
    absorb operation = .receive event recover →
    (∀ payload, recover (event payload) = (payload.value ty).map reply) →
    Function.Bijective reply ∧
      (∀ value : carriers.Value ty, ∃ payload : Domain.Payload carriers,
        Domain.Payload.ofValue ty value = some payload)
  query : ∀ (origin : Origin)
    (reply : Domain.Raw (.challenge origin : Domain.Event carriers) → I.Reply operation),
    absorb operation = .query (.challenge origin) (some ∘ reply) → Function.Bijective reply
  send : ∀ (event : Domain.Event carriers) (value : I.Reply operation),
    absorb operation = .send event value → ∀ reply : I.Reply operation, reply = value

/-- Losslessness is needed only on calls in the presentation, including every
reply-dependent continuation. This is structural support, not an assertion of
honest replies or a probability-one event. -/
abbrev LosslessOn
    (absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw)
    (presented : PIR.Process I A) : Prop := OperationSupport (LosslessOperation absorb) presented

/-- Existing installed global laws remain a sufficient support certificate. -/
theorem LosslessInterface.on
    {absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
    (lossless : LosslessInterface absorb) (presented : PIR.Process I A) : LosslessOn absorb presented := by
  induction presented with
  | done => trivial
  | halt => trivial
  | call operation next ih =>
    exact ⟨⟨lossless.receive operation, lossless.query operation, lossless.send operation⟩, ih⟩

end ZkcSecurity.FiatShamir.Original
