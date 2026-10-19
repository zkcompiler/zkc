module

public import ZkcExamples.Executable.DeferredRoundsFacts

@[expose] public section

/-! The executable validator of the deferred-rounds fixture.

`DeferredRoundsProgramData` is the validator participant of the
`zkc.program/0` candidate of the fixture's `example::Proof`. The program
computes every product of the verifier in one calculation call after the second
draw, as the compiler's calculation batching schedules it, while the constructed
validator computes `a₀ · r₀` after the first draw. The lowering rule accepts the
pair (`accepted`) by normalization, since the reading is not the constructed
validator instruction for instruction (`rescheduled`).

Host validation therefore prunes, at every budget and with every framing
header, the ideal acceptance of the constructed validator on the proof its
message bytes decode to (`executable_prunes`), and at a budget of at least the
total charge, with the expected header, it is that acceptance
(`executable_validate`). The validator calls no helper. The lowering facts are
generated (`DeferredRoundsFacts`, in this namespace).
-/

set_option autoImplicit false

namespace ZkcExamples.Executable.DeferredRounds
open Zkc.Construction Zkc.Executable Zkc.Source
open ZkcExamples.Construction

set_option maxRecDepth 20000 in
/-- The reading is not the constructed validator instruction for instruction:
the rule accepts it through normalization. -/
theorem rescheduled : Code.instructionList lowered.code ≠ DeferredRounds.participant.instructions := by
  decide +kernel

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- No helper needs preparation. -/
theorem prepared (table : Structured.Evaluation.Meanings F G Structured.closedInterface) :
    ∀ name ∈ Instruction.helpers DeferredRounds.participant.instructions, Prepared installed validator table name := by
  simp [helpers]

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- No helper call needs its result sorts. -/
theorem helpersSorted (table : Structured.Evaluation.Meanings F G Structured.closedInterface) :
    ∀ call ∈ Instruction.callList DeferredRounds.participant.instructions, HelperSorted table call.1 call.2 := by
  simp [calls]

/-- Host validation of proof bytes prunes the ideal acceptance of the constructed
validator on the decoded proof by rejections, at every budget and with every
framing header, for every helper table, challenge function in every lawful monad
and decoder. -/
theorem executable_prunes {m : Type → Type} [Monad m] [LawfulMonad m]
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) (budget : Nat) (binding : List UInt8) (x : F)
    (initial : History F G) (bytes : List UInt8) :
    Prunes (fun accepted => accepted = false)
      (validate installed validator DeferredRounds.context challenge decode budget binding
        DeferredRounds.acceptancePosition (DeferredRounds.inputs x) initial bytes)
      ((fun result => Accepts DeferredRounds.acceptancePosition (idealObservation result)) <$>
        ideal DeferredRounds.context challenge table DeferredRounds.participant.returned
          DeferredRounds.participant.instructions (DeferredRounds.inputs x ++ [.transcript initial])
          (decodeProof decode receives (bytes.drop 40))) := by
  rw [← plan_types (DeferredRounds.inputs (G := G) x)]
  exact validate_prunes_export installed validator DeferredRounds.context challenge table decode budget accepted
    (prepared table) (helpersSorted table) binding DeferredRounds.acceptancePosition _ initial bytes (admitted x)

/-- With the expected framing header and a budget of at least 35, host
validation of the proof bytes is the ideal acceptance of the constructed
validator on the decoded proof. -/
theorem executable_validate {m : Type → Type} [Monad m] [LawfulMonad m]
    (table : Structured.Evaluation.Meanings F G Structured.closedInterface) (challenge : History F G → m F)
    (decode : PhysicalType → List UInt8 → Option (Payload F G)) {budget : Nat} (sufficient : 35 ≤ budget)
    (binding : List UInt8) (x : F) (initial : History F G) (bytes : List UInt8)
    (header : bytes.take 40 = magic ++ binding) :
    validate installed validator DeferredRounds.context challenge decode budget binding
        DeferredRounds.acceptancePosition (DeferredRounds.inputs x) initial bytes =
      (fun result => Accepts DeferredRounds.acceptancePosition (idealObservation result)) <$>
        ideal DeferredRounds.context challenge table DeferredRounds.participant.returned
          DeferredRounds.participant.instructions (DeferredRounds.inputs x ++ [.transcript initial])
          (decodeProof decode receives (bytes.drop 40)) := by
  obtain ⟨read, same, inputs, -⟩ := checkLowering_sound (F := F) (G := G) accepted
  have sorted := admits_sorted (admitted (G := G) x) initial
  rw [inputs] at sorted
  rw [← same DeferredRounds.context challenge table (helpersSorted table) _ sorted,
    ← plan_types (DeferredRounds.inputs (G := G) x)]
  exact validate_ideal installed validator DeferredRounds.context challenge table decode budget _
    (prepared table) read total sufficient binding DeferredRounds.acceptancePosition _ initial bytes (admitted x)
    header

end ZkcExamples.Executable.DeferredRounds
