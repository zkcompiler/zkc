module

public import ZkcSecurity.FiatShamir.DomainReduction

@[expose] public section

/-! Composition with a typed return presentation. A deterministic decoder and
its checked round trip reconstruct every component return. The postcondition
retains the exact reached history and all invariant facts. These rules use the
existing Bridge semantics and introduce no new experiment or evaluator. -/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.DomainReduction.Bridge
open Zkc.Source Zkc.Construction
variable {carriers : Structured.Carriers} {I : PIR.Signature} {A B C : Type}
variable {absorb : Zkc.Transcript.Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
variable {history : Domain.History carriers}
variable {actual : PIR.Process (Domain.effects carriers) A} {presented : PIR.Process I B}
variable {Post : Domain.History carriers → C → Prop}

theorem bindEncoded
    (encode : B → A) (decode : A → Option B)
    (roundtrip : ∀ value, decode (encode value) = some value)
    (historyOf : B → Domain.History carriers) (Invariant : B → Prop)
    (head : Bridge absorb
      (fun reached output => ∃ value, reached = historyOf value ∧ Invariant value ∧ output = encode value)
      history actual (presented.bind fun value => .done (encode value)))
    (nextActual : A → PIR.Process (Domain.effects carriers) C)
    (nextPresented : B → PIR.Process I C)
    (next : ∀ value, Invariant value →
      Bridge absorb Post (historyOf value) (nextActual (encode value)) (nextPresented value)) :
    Bridge absorb Post history (actual.bind nextActual) (presented.bind nextPresented) := by
  let continuation (output : A) : PIR.Process I C :=
    match decode output with
    | some value => nextPresented value
    | none => .halt .refused
  have combined := head.bind nextActual continuation (by
    intro reached output post
    obtain ⟨value, rfl, invariant, rfl⟩ := post
    simpa only [continuation, roundtrip] using next value invariant)
  have equation :
      ((presented.bind fun value => .done (encode value)).bind continuation) =
        presented.bind nextPresented := by
    rw [PIR.Process.bind_assoc]
    congr 1
    funext value
    simp only [PIR.Process.bind, continuation, roundtrip]
  rw [equation] at combined
  exact combined

theorem byCasesPresentation {A : Type} {carriers : Structured.Carriers} {I : PIR.Signature}
    {absorb : Zkc.Transcript.Interface I (Domain.Event carriers) (Domain.Payload carriers) Domain.Raw}
    {history : Domain.History carriers} {Post : Domain.History carriers → A → Prop}
    (condition : Prop) [Decidable condition]
    (actual : PIR.Process (Domain.effects carriers) A)
    (yesPresented noPresented : PIR.Process I A)
    (yes : condition → Bridge absorb Post history actual yesPresented)
    (no : ¬condition → Bridge absorb Post history actual noPresented) :
    Bridge absorb Post history actual (if condition then yesPresented else noPresented) := by
  by_cases holds : condition
  · simpa only [holds, ite_true] using yes holds
  · simpa only [holds, ite_false] using no holds

end ZkcSecurity.FiatShamir.DomainReduction.Bridge
