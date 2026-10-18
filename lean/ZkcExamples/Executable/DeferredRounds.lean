module

public import ZkcExamples.Executable.DeferredRoundsProgramData
public import ZkcExamples.Construction.DeferredRounds
public import Zkc.Executable.NormalizationSoundness
public import Zkc.Executable.Installed

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
(`executable_validate`). The validator calls no helper.
-/

set_option autoImplicit false

namespace ZkcExamples.Executable.DeferredRounds
open Zkc.Construction Zkc.Executable Zkc.Source
open ZkcExamples.Construction

abbrev validator : Validator := DeferredRoundsProgramData.validator

set_option maxRecDepth 20000 in
/-- The reading of the executable validator. -/
def lowered : Lowered :=
  (checkLowering installed DeferredRounds.participant validator).toOption.get (by decide +kernel)

/-- The per-compile lowering rule accepts the actual executable validator. -/
theorem accepted : checkLowering installed DeferredRounds.participant validator = .ok lowered :=
  ok_of_isSome _ _

set_option maxRecDepth 20000 in
/-- The reading is not the constructed validator instruction for instruction:
the rule accepts it through normalization. -/
theorem rescheduled : Code.instructionList lowered.code ≠ DeferredRounds.participant.instructions := by
  decide +kernel

/-- The constructed validator calls no helper. -/
theorem helpers : Instruction.helpers DeferredRounds.participant.instructions = [] := by
  rw [← Instruction.helperList_eq]
  decide +kernel

theorem calls : Instruction.callList DeferredRounds.participant.instructions = [] := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- A complete run charges 35 instructions. -/
theorem total : lowered.total? = some 35 := by decide +kernel

/-- A round message: a scalar field element. -/
abbrev coordinate : PhysicalType := ⟨.data (.field "bls12-381.fr"), "arkworks.fr/0"⟩

/-- The receive types: one message per round. -/
abbrev receives : List PhysicalType := [coordinate, coordinate]

set_option maxRecDepth 20000 in
theorem plan_static : Plan.static lowered.plan = some receives := by decide +kernel

theorem plan_types {F G : Type} (data : List (Value F G)) : Plan.types data lowered.plan = receives :=
  Plan.types_static data plan_static

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

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- The executable admits the validator's data input. -/
theorem admitted (x : F) : validator.admits (DeferredRounds.inputs (G := G) x) = true := by
  rfl

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
