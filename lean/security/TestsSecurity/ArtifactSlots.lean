module

import ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerLoop

/-! Typed callback ABI controls. Candidate coordinates cannot supply semantic
proofs: the complete source tuple and selected frame reads still have to agree. -/
set_option autoImplicit false
namespace TestsSecurity.ArtifactSlots
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured
open ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding
open ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer

example : VerifierOutputs.ofYields "suite" [4, 7]
    (VerifierOutputs.sorts "suite") = none := rfl

example : VerifierOutputs.ofYields "suite" [4, 7, 9]
    [.data (.field "bls12-381.fr"), .data (.vector "bls12-381.fr"),
      .transcript "suite"] = none := rfl

example : VerifierOutputs.ofYields "suite" [4, 7, 9]
    (VerifierOutputs.sorts "other") = none := rfl

example : Outputs.ofYields "suite" [4, 7, 8, 9]
    (Outputs.sorts "suite") = none := rfl

example : Outputs.ofYields "suite" [4, 7, 8, 9, 10]
    [.data (.vector "bls12-381.fr"), .data .index, .data .index,
      .data (.field "bls12-381.fr"), .transcript "suite"] = none := rfl

example : Outputs.ofYields "suite" [4, 7, 8, 9, 10]
    (Outputs.sorts "other") = none := rfl

variable {F G : Type} [CommRing F]

/-- A same-sort wrong producer output is not caught merely by sort admission.
The complete return relation refuses it, even for equal host field carriers. -/
theorem wrong_producer_slot (context : Zkc.Construction.Context) :
    ¬ ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.Returns (F := F) (G := G) context
      ⟨⟨3⟩, ⟨1⟩, ⟨2⟩, ⟨0⟩, ⟨4⟩⟩ []
      (SumcheckProverLaws.embedP ([0], 0, 1, []), ⟨[], []⟩)
      [.data (.vector "bls12-381.fr" [0]), .data (.index 0), .data (.index 1),
        .data (.vector "bls12-381.fr" []), .transcript context.suite []] := by
  rintro ⟨raw, dimension, width, point, output, rawRead, rest⟩
  have values : ([0], 0, 1, []) = (raw, dimension, width, point) := by
    simpa only [SumcheckProverLaws.embedP, SumcheckRoundNormalForms.proverState,
      Values.cons.injEq, Option.some.injEq, and_true, Prod.mk.injEq] using output
  cases values
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.some.injEq, Domain.Value.data.injEq] at rawRead
  have same := (Domain.Payload.mk_inj (carriers := uniformCarriers F G)
    (ty := .vector "bls12-381.fr")).mp rawRead
  cases same

/-- Structural simulation cannot turn that wrong slot into a certified return. -/
theorem wrong_slot_simulation (context : Zkc.Construction.Context) :
    ¬ Nonempty (Original.Simulation (carriers := uniformCarriers F G)
      (ZkcExamples.Structured.SumcheckArtifacts.OriginalProducer.Returns (F := F) (G := G) context ⟨⟨3⟩, ⟨1⟩, ⟨2⟩, ⟨0⟩, ⟨4⟩⟩ [])
      (fun _ _ => True)
      (.done (SumcheckProverLaws.embedP ([0], 0, 1, []), ⟨[], []⟩))
      (.done [.data (.vector "bls12-381.fr" [0]), .data (.index 0), .data (.index 1),
        .data (.vector "bls12-381.fr" []), .transcript context.suite []])) := by
  rintro ⟨simulation⟩
  cases simulation with
  | done returned => exact wrong_producer_slot context returned

#print axioms wrong_producer_slot
#print axioms wrong_slot_simulation
end TestsSecurity.ArtifactSlots
