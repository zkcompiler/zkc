module

public import ZkcSecurity.FiatShamir.OriginalTransport

@[expose] public section

/-! Lossless nominal readings lift complete original/artifact simulations.
The laws constrain the actual typed decoder equations used by `ReadingTo`.
They do not inspect operation labels or require a function on returned values.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.Original
open Zkc.Source Zkc.Construction Zkc.Transcript
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

variable {absorb : Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
variable {Post : Domain.History carriers → A → Prop} {returns : A → B → Prop}
variable {live : PIR.Process (Domain.effects carriers) A → Domain.Environment carriers → Prop}
variable {source : PIR.Process (Domain.effects carriers) A}
variable {target : PIR.Process (Domain.effects carriers) B}
variable {presented : PIR.Process I A} {history : Domain.History carriers}

private theorem prependLosslessSend (lossless : LosslessInterface absorb)
    (operation : I.Op) (next : I.Reply operation → PIR.Process I A)
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
  rw [lossless.send operation event value absorbed reply]
  exact aligned

/-- Reconstruct the target's full-return presentation from local lossless
effects. Target returns may depend on raw replies forgotten by source returns.
No uniqueness, total return realization, or target reading is assumed.
-/
theorem exists_lossless_reading (lossless : LosslessInterface absorb)
    (simulation : Zkc.Construction.Original.Simulation returns live source target)
    (reading : ReadingTo absorb Post history source presented) :
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
        exact prependLosslessSend lossless operation next event value absorbed (ih value suffix)
  | halt reason =>
    induction presented generalizing history with
    | done value => cases reading
    | halt reason => cases reading; exact ⟨.halt reason, .halt reason, .halt _ reason⟩
    | call operation next ih =>
      cases reading with
      | absorbSend operation next event value absorbed suffix =>
        exact prependLosslessSend lossless operation next event value absorbed (ih value suffix)
  | checkpoint frame related next ih =>
    obtain ⟨after, aligned, suffix⟩ := ih reading
    exact ⟨after, aligned, .checkpoint frame suffix⟩
  | call operation next ih =>
    induction presented generalizing history with
    | done value =>
      cases reading with
      | checkpoint frame suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix
        exact ⟨after, aligned, .checkpoint frame reading⟩
      | observe event suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix
        exact ⟨after, aligned, .observe event reading⟩
      | send site schema peer payload suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix
        exact ⟨after, aligned, .send site schema peer payload reading⟩
    | halt reason =>
      cases reading with
      | checkpoint frame suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix
        exact ⟨after, aligned, .checkpoint frame reading⟩
      | observe event suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix
        exact ⟨after, aligned, .observe event reading⟩
      | send site schema peer payload suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix
        exact ⟨after, aligned, .send site schema peer payload reading⟩
    | call nominal after nominalIH =>
      cases reading with
      | checkpoint frame suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix
        exact ⟨after, aligned, .checkpoint frame reading⟩
      | observe event suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix
        exact ⟨after, aligned, .observe event reading⟩
      | send site schema peer payload suffix =>
        obtain ⟨after, aligned, reading⟩ := ih () suffix
        exact ⟨after, aligned, .send site schema peer payload reading⟩
      | absorbSend operation next event value absorbed suffix =>
        exact prependLosslessSend lossless nominal after event value absorbed (nominalIH value suffix)
      | receive ty site schema peer left operation next event recover reply absorbed decoded suffix =>
        obtain ⟨bijective, encodable⟩ := lossless.receive nominal ty event recover reply absorbed decoded
        let equiv := Equiv.ofBijective reply bijective
        let payload := fun value => Classical.choose (encodable value)
        have encoded := fun value => Classical.choose_spec (encodable value)
        have witnesses := fun value =>
          ih value (suffix (payload value) value (Domain.Payload.value_ofValue (encoded value)))
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
        let equiv := Equiv.ofBijective reply (lossless.query nominal origin reply absorbed)
        choose targetNext alignedNext readingNext using (fun raw => ih raw (suffix raw))
        refine ⟨.call nominal (fun value => targetNext (equiv.symm value)), .call nominal ?_,
          .query history origin _ nominal _ reply supported absorbed ?_⟩
        · intro value
          simpa only [show reply (equiv.symm value) = value from equiv.apply_symm_apply value]
            using alignedNext (equiv.symm value)
        · intro raw
          simpa only [show equiv.symm (reply raw) = raw from equiv.symm_apply_apply raw]
            using readingNext raw

namespace Bridge

/-- The same-return artifact bridge and all-reply alignment are consequences
of the source bridge, its full simulation and the interface laws alone. -/
theorem exists_lossless_presentation
    (bridge : Bridge absorb Post history source target presented returns live)
    (lossless : LosslessInterface absorb) :
    ∃ targetPresented : PIR.Process I B, Alignment returns presented targetPresented ∧
      DomainReduction.Bridge absorb (fun reached b => ∃ a, Post reached a ∧ returns a b)
        history target targetPresented := by
  obtain ⟨after, aligned, reading⟩ := exists_lossless_reading lossless bridge.simulation bridge.sourceReading.reading
  exact ⟨after, aligned, reading, bridge.actualCoherent⟩

end Bridge
end ZkcSecurity.FiatShamir.Original
