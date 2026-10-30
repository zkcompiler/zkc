module

public import ZkcSecurity.Bindings.Transcript.OriginalTransport
public import Zkc.Semantics.OperationSupport

@[expose] public section

/-! Lossless nominal readings lift complete original/artifact simulations.
The laws constrain the actual typed decoder equations used by `ReadingTo`.
They do not inspect operation labels or require a function on returned values.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.Original
open PIR Zkc.Source Zkc.Construction Zkc.Transcript
open DomainReduction

variable {carriers : Structured.Carriers} {I : PIR.Signature} {A B : Type}

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

variable {absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
variable {Post : Domain.History carriers → A → Prop} {returns : A → B → Prop}
variable {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
variable {source : PIR.Process (Domain.effects carriers) A}
variable {target : PIR.Process (Domain.effects carriers) B}
variable {presented : PIR.Process I A} {history : Domain.History carriers}

private theorem prependLosslessSend (operation : I.Op) (lossless : LosslessOperation absorb operation)
    (next : I.Reply operation → PIR.Process I A)
    (event : Domain.Event carriers) (value : I.Reply operation)
    (absorbed : absorb operation = .send event value)
    (suffix : ∃ targetPresented : PIR.Process I B,
      Alignment returns (next value) targetPresented ∧
      ReadingTo absorb (fun reached b => ∃ a, Post reached a ∧ returns a b)
        (history ++ [event]) target targetPresented) :
    ∃ targetPresented : PIR.Process I B,
      Alignment returns (.call operation next) targetPresented ∧
      ReadingTo absorb (fun reached b => ∃ a, Post reached a ∧ returns a b)
        history target targetPresented := by
  obtain ⟨after, aligned, reading⟩ := suffix
  refine ⟨.call operation (fun _ => after), .call operation ?_,
    .absorbSend operation _ event value absorbed reading⟩
  intro reply
  rw [lossless.send event value absorbed reply]
  exact aligned

/-- Reconstruct the target's full-return presentation from local lossless
effects. Target returns may depend on raw replies forgotten by source returns.
No uniqueness, total return realization, or target reading is assumed.
-/
theorem exists_lossless_reading_on
    (simulation : Zkc.Construction.Original.Simulation returns live source target)
    (reading : ReadingTo absorb Post history source presented)
    (lossless : LosslessOn absorb presented) :
    ∃ targetPresented : PIR.Process I B, Alignment returns presented targetPresented ∧
      ReadingTo absorb (fun reached b => ∃ a, Post reached a ∧ returns a b)
        history target targetPresented := by
  induction simulation generalizing history presented with
  | done related =>
    induction presented generalizing history with
    | done value =>
      cases reading with
      | done reached value holds => exact ⟨.done _, .done related, .done _ _ ⟨_, holds, related⟩⟩
    | halt reason => cases reading
    | call operation next ih =>
      cases reading with
      | absorbSend operation next event value absorbed suffix =>
        exact prependLosslessSend operation lossless.1 next event value absorbed (ih value suffix (lossless.2 value))
  | halt reason =>
    induction presented generalizing history with
    | done value => cases reading
    | halt reason => cases reading; exact ⟨.halt reason, .halt reason, .halt _ reason⟩
    | call operation next ih =>
      cases reading with
      | absorbSend operation next event value absorbed suffix =>
        exact prependLosslessSend operation lossless.1 next event value absorbed (ih value suffix (lossless.2 value))
  | checkpoint frame related next ih =>
    obtain ⟨after, aligned, suffix⟩ := ih reading lossless
    exact ⟨after, aligned, .checkpoint frame suffix⟩
  | call operation next ih =>
    induction presented generalizing history with
    | done value =>
      cases reading with
      | checkpoint frame suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix lossless
        exact ⟨after, aligned, .checkpoint frame reading⟩
      | observe event suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix lossless
        exact ⟨after, aligned, .observe event reading⟩
      | send site schema peer payload suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix lossless
        exact ⟨after, aligned, .send site schema peer payload reading⟩
    | halt reason =>
      cases reading with
      | checkpoint frame suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix lossless
        exact ⟨after, aligned, .checkpoint frame reading⟩
      | observe event suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix lossless
        exact ⟨after, aligned, .observe event reading⟩
      | send site schema peer payload suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix lossless
        exact ⟨after, aligned, .send site schema peer payload reading⟩
    | call nominal after nominalIH =>
      cases reading with
      | checkpoint frame suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix lossless
        exact ⟨after, aligned, .checkpoint frame reading⟩
      | observe event suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix lossless
        exact ⟨after, aligned, .observe event reading⟩
      | send site schema peer payload suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix lossless
        exact ⟨after, aligned, .send site schema peer payload reading⟩
      | absorbSend operation next event value absorbed suffix =>
        exact prependLosslessSend nominal lossless.1 after event value absorbed (nominalIH value suffix (lossless.2 value))
      | receive ty site schema peer left operation next event recover reply absorbed decoded suffix =>
        obtain ⟨bijective, encodable⟩ := lossless.1.receive ty event recover reply absorbed decoded
        let equiv := Equiv.ofBijective reply bijective
        let payload := fun value => Classical.choose (encodable value)
        have encoded := fun value => Classical.choose_spec (encodable value)
        have witnesses := fun value =>
          ih value (suffix (payload value) value (Domain.Payload.value_ofValue (encoded value))) (lossless.2 (reply value))
        choose targetNext alignedNext readingNext using witnesses
        refine ⟨.call nominal (fun value => targetNext (equiv.symm value)), .call nominal ?_,
          .receive ty site schema peer _ nominal _ event recover reply absorbed decoded ?_⟩
        · intro value
          simpa only [show reply (equiv.symm value) = value from equiv.apply_symm_apply value]
            using alignedNext (equiv.symm value)
        · intro message value decodedValue
          have same : payload value = message :=
            Option.some.inj ((encoded value).symm.trans (Domain.Payload.ofValue_value decodedValue))
          simpa only [← same, show equiv.symm (reply value) = value from equiv.symm_apply_apply value]
            using readingNext value
      | query history origin left operation next reply supported absorbed suffix =>
        let equiv := Equiv.ofBijective reply (lossless.1.query origin reply absorbed)
        choose targetNext alignedNext readingNext using (fun raw => ih raw (suffix raw) (lossless.2 (reply raw)))
        refine ⟨.call nominal (fun value => targetNext (equiv.symm value)), .call nominal ?_,
          .query history origin _ nominal _ reply supported absorbed ?_⟩
        · intro value
          simpa only [show reply (equiv.symm value) = value from equiv.apply_symm_apply value]
            using alignedNext (equiv.symm value)
        · intro raw
          simpa only [show equiv.symm (reply raw) = raw from equiv.symm_apply_apply raw]
            using readingNext raw

/-- A globally lossless interface supplies the local laws automatically. -/
theorem exists_lossless_reading (lossless : LosslessInterface absorb)
    (simulation : Zkc.Construction.Original.Simulation returns live source target)
    (reading : ReadingTo absorb Post history source presented) :
    ∃ targetPresented : PIR.Process I B, Alignment returns presented targetPresented ∧
      ReadingTo absorb (fun reached b => ∃ a, Post reached a ∧ returns a b)
        history target targetPresented :=
  exists_lossless_reading_on simulation reading (lossless.on presented)

namespace Bridge

/-- The same-return artifact bridge and all-reply alignment are consequences
of the source bridge, its full simulation and the interface laws alone. -/
theorem exists_lossless_presentation_on
    (bridge : Bridge absorb Post history source target presented returns live)
    (lossless : LosslessOn absorb presented) :
    ∃ targetPresented : PIR.Process I B, Alignment returns presented targetPresented ∧
      DomainReduction.Bridge absorb (fun reached b => ∃ a, Post reached a ∧ returns a b)
        history target targetPresented := by
  obtain ⟨after, aligned, reading⟩ := exists_lossless_reading_on bridge.simulation bridge.sourceReading.reading lossless
  exact ⟨after, aligned, reading, bridge.actualCoherent⟩

/-- Global installed laws specialize the same reconstruction theorem. -/
theorem exists_lossless_presentation
    (bridge : Bridge absorb Post history source target presented returns live)
    (lossless : LosslessInterface absorb) :
    ∃ targetPresented : PIR.Process I B, Alignment returns presented targetPresented ∧
      DomainReduction.Bridge absorb (fun reached b => ∃ a, Post reached a ∧ returns a b)
        history target targetPresented :=
  bridge.exists_lossless_presentation_on (lossless.on presented)

end Bridge
end ZkcSecurity.FiatShamir.Original
