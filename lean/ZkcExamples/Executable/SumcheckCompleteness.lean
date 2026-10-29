module

public import ZkcExamples.Executable.SumcheckCharges
public import ZkcExamples.Executable.SumcheckProof
public import ZkcExamples.Executable.SumcheckDomainHonest

@[expose] public section

/-! Honest completeness at the actual canonical Sumcheck Process and Code VM.
The byte theorem composes actual checked interpreted execution with honest success. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.SumcheckCompleteness
open Zkc Zkc.Construction Zkc.Executable Zkc.Source
open SumcheckCharges
open Zkc.Construction.Uniform.DomainAdapter

-- Keep the certificate opaque while composing its already checked theorem.
-- Otherwise elaboration unfolds the entire concrete Code before unification.
attribute [local irreducible] DomainVM.Sufficient DomainVM.Passes Executable.validate DomainVM.metered

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The existing honest producer and its existing field-message framing. -/
abbrev honestRounds := SumcheckDomainHonest.messages (F := F) (G := G)
abbrev honestBytes := SumcheckMessages.honestBytes (F := F)

/-- Successful canonical metered execution, with an empty unread suffix and
exact selected output true. The nominal transcript suffix is retained. -/
theorem honest_metered (oracle : History F G → F) (budget : Nat) (values : List F) (rounds : Nat)
    (admitted : rounds ≤ SumcheckProof.maximum) (shaped : values.length = 2 ^ rounds)
    (initial : History F G) (fits : charge rounds ≤ budget) :
    ∃ history suffix, DomainVM.metered (m := Id) ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Construction.SumcheckProof.context Origin.withoutCoordinates initial oracle cost budget
      SumcheckProof.lowered (SumcheckProof.physicalInputs values values.sum rounds [])
      ((honestRounds oracle initial values rounds).map (.field "bls12-381.fr")) =
        (.returned [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history], []) ∧
      Zkc.Construction.Uniform.DomainAdapter.readbackHistory Origin.withoutCoordinates history = some suffix := by
  obtain ⟨returned, unread, good, executed⟩ := DomainVM.metered_success (F := F) (G := G)
    ZkcExamples.Construction.SumcheckProof.program ZkcExamples.Construction.SumcheckProof.context
    Origin.withoutCoordinates initial oracle cost budget SumcheckProof.lowered
    (SumcheckProof.physicalInputs values values.sum rounds []) _ _
    (sufficient (F := F) (G := G) budget values values.sum rounds [] _ shaped fits)
    (SumcheckDomainHonest.observation_passes (F := F) (G := G) oracle initial values rounds admitted shaped)
  obtain ⟨selected, rfl, history, rfl, suffix, mapped⟩ := good
  exact ⟨history, suffix, executed, mapped⟩

omit [Field F] [DecidableEq F] in
/-- The existing 40-byte framing header, with precisely the old binding premise. -/
theorem honest_header (encode : F → List UInt8) (binding : List UInt8)
    (bindingLength : binding.length = 32) (messages : List F) :
    (honestBytes encode binding messages).take 40 = magic ++ binding :=
  messageBytes_header encode bindingLength messages

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- Only field-message codec laws are needed for the actual receive plan. -/
theorem honest_decoded (oracle : History F G → F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (encode : F → List UInt8)
    (roundtrip : ∀ value, decode SumcheckProof.coordinate (encode value) = some (.field "bls12-381.fr" value))
    (bounded : ∀ value, (encode value).length ≤ proofLimit)
    (binding : List UInt8) (bindingLength : binding.length = 32)
    (values : List F) (rounds : Nat) (admitted : rounds ≤ SumcheckProof.maximum) (initial : History F G) :
    decodeProof decode
      (Plan.types (ZkcExamples.Construction.SumcheckProof.inputs (G := G) values values.sum rounds)
        SumcheckProof.lowered.plan)
      ((honestBytes encode binding (honestRounds oracle initial values rounds)).drop 40) =
        (honestRounds oracle initial values rounds).map (.field "bls12-381.fr") := by
  simp only [honestBytes, SumcheckMessages.honestBytes]
  rw [messageBytes_body encode bindingLength, SumcheckProof.plan_types]
  have receives : SumcheckProof.receives rounds =
      List.replicate (2 * rounds) SumcheckProof.coordinate := by
    simp only [SumcheckProof.receives, ite_eq_left admitted, SumcheckProof.round]
    clear admitted
    induction rounds with
    | zero => rfl
    | succ rounds ih =>
        simp only [List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append]
        rw [ih]
        simp [Nat.mul_succ, List.replicate_succ]
  rw [receives, ← SumcheckMessages.honestRounds_length SumcheckDomainHonest.transcript oracle initial values rounds]
  exact decodeProof_messages decode SumcheckProof.coordinate encode (.field "bls12-381.fr") roundtrip bounded _

/-- Canonical interpreted success on the bytes produced by the unchanged honest
codec, together with the transcript suffix needed by execution consumers. -/
theorem honest_metered_bytes (oracle : History F G → F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (encode : F → List UInt8)
    (roundtrip : ∀ value, decode SumcheckProof.coordinate (encode value) = some (.field "bls12-381.fr" value))
    (bounded : ∀ value, (encode value).length ≤ proofLimit)
    (budget : Nat) (binding : List UInt8) (bindingLength : binding.length = 32)
    (values : List F) (rounds : Nat) (admitted : rounds ≤ SumcheckProof.maximum)
    (shaped : values.length = 2 ^ rounds) (initial : History F G) (fits : charge rounds ≤ budget) :
    ∃ history suffix, DomainVM.metered (m := Id) ZkcExamples.Construction.SumcheckProof.program
      ZkcExamples.Construction.SumcheckProof.context Origin.withoutCoordinates initial oracle cost budget
      SumcheckProof.lowered (SumcheckProof.physicalInputs values values.sum rounds [])
      (decodeProof decode
        (Plan.types (ZkcExamples.Construction.SumcheckProof.inputs (G := G) values values.sum rounds)
          SumcheckProof.lowered.plan)
        ((honestBytes encode binding (honestRounds oracle initial values rounds)).drop 40)) =
        (.returned [.data (.boolean true), .transcript ZkcExamples.Construction.SumcheckProof.context.suite history], []) ∧
      Zkc.Construction.Uniform.DomainAdapter.readbackHistory Origin.withoutCoordinates history = some suffix := by
  rw [honest_decoded oracle decode encode roundtrip bounded binding bindingLength values rounds admitted initial]
  exact honest_metered (F := F) (G := G) oracle budget values rounds admitted shaped initial fits

/-- Honest interpreted-byte acceptance with the original field-coordinate codec laws,
binding length, table shape, admitted rounds and operational budget. -/
theorem honest_accepted (oracle : History F G → F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (encode : F → List UInt8)
    (roundtrip : ∀ value, decode SumcheckProof.coordinate (encode value) = some (.field scalar value))
    (bounded : ∀ value, (encode value).length ≤ proofLimit) (budget : Nat) (binding : List UInt8)
    (bindingLength : binding.length = 32) (values : List F) (rounds : Nat)
    (admitted : rounds ≤ SumcheckProof.maximum) (shaped : values.length = 2 ^ rounds)
    (initial : History F G) (fits : charge rounds ≤ budget) :
    validate (m := Id) installed SumcheckProof.validator context oracle decode budget binding
      ZkcExamples.Construction.SumcheckProof.acceptancePosition
      (ZkcExamples.Construction.SumcheckProof.inputs values values.sum rounds) initial
      (honestBytes encode binding (honestRounds oracle initial values rounds)) = true := by
  rw [ZkcExamples.Construction.SumcheckProof.acceptancePosition_eq]
  obtain ⟨history, suffix, executed, mapped⟩ := honest_metered_bytes oracle decode encode roundtrip bounded
    budget binding bindingLength values rounds admitted shaped initial fits
  rw [DomainVM.checked_validate_metered (m := Id) ZkcExamples.Construction.SumcheckProof.program
    ZkcExamples.Construction.SumcheckProof.context initial oracle installed
    ZkcExamples.Construction.SumcheckProof.participant SumcheckProof.validator decode budget
    SumcheckProof.domain_prepared SumcheckProof.lowered SumcheckProof.nativeScope SumcheckProof.native_checked
    binding 0 (ZkcExamples.Construction.SumcheckProof.inputs values values.sum rounds)
    (honestBytes encode binding (honestRounds oracle initial values rounds))
    (SumcheckProof.admitted values values.sum rounds) (SumcheckProof.nominalInputs values values.sum rounds)
    (SumcheckProof.embedded values values.sum rounds)]
  rw [honest_header encode binding bindingLength _, ite_eq_left rfl]
  change DomainVM.byteAcceptance 0
    (DomainVM.nativeObservation ZkcExamples.Construction.SumcheckProof.context.suite Origin.withoutCoordinates initial
      (DomainVM.metered (m := Id) ZkcExamples.Construction.SumcheckProof.program
        ZkcExamples.Construction.SumcheckProof.context Origin.withoutCoordinates initial oracle cost budget
        SumcheckProof.lowered (SumcheckProof.physicalInputs values values.sum rounds []) _)) = true
  rw [executed]
  simp [DomainVM.byteAcceptance, DomainVM.nativeObservation, Executable.observation,
    Uniform.DomainAdapter.readbackOutcome, Uniform.DomainAdapter.readbackValues,
    Uniform.DomainAdapter.readbackValue, Uniform.DomainAdapter.readbackData, mapped, selectedTrue]

end ZkcExamples.Executable.SumcheckCompleteness
