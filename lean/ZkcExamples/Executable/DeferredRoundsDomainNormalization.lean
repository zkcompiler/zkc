module

public import ZkcExamples.Executable.DeferredRoundsProgramData
public import ZkcExamples.Construction.DeferredRounds
public import Zkc.Executable.Installed
public import Zkc.Executable.Reading
public import Zkc.Executable.DomainNormalizationSoundness

@[expose] public section

/-! The actual nonidentical DeferredRounds schedule, compared at canonical
Domain outcomes. The arithmetic before the second receive in the source is
computed after the second query in the executable reading. The proof quantifies
over every receive and query reply; no relation truth or honest proof is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.DeferredRounds
open Zkc Zkc.Construction Zkc.Source Zkc.Executable
open Zkc.Executable.DomainVM
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

set_option maxRecDepth 20000 in
/-- Read the actual native artifact without the retired normalization proof. -/
def checkedReading : Lowered :=
  (Validator.read installed [] DeferredRoundsProgramData.validator).toOption.get (by decide +kernel)

/-- The reader certificate fixes the native Code, receive plan and return refs. -/
theorem reading_checked :
    Validator.read installed [] DeferredRoundsProgramData.validator = .ok checkedReading :=
  ok_of_isSome _ _

set_option maxRecDepth 20000 in
theorem reading_total : checkedReading.total? = some 35 := by decide +kernel

/-- Concrete context checked against the actual exported artifact. -/
def readingContext : Context :=
{ toContextIdentity := { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                         roles := ["role00000000", "role00000001"],
                         producer := 0,
                         validator := 1 },
  profile := Zkc.Construction.Profile.fiatShamir
               { service := 2,
                 contract := "random.bls12-381.fr/0",
                 request := some (.draw "bls12-381.fr"),
                 suite := "merlin3.bls12-381.fr64be/0",
                 draws := [("label_6330", "label_6430_0"), ("label_6331", "label_6431_0")] } }

set_option maxRecDepth 20000 in
theorem reading_context : ZkcExamples.Construction.DeferredRounds.context = readingContext := by decide +kernel

/-- Exact instruction schedule read from the checked executable artifact. -/
def readingInstructions : List Instruction :=
[{ operation := Zkc.Construction.Operation.receive
                  "label_6d30_0"
                  "label_6d30_0"
                  "role00000000"
                  (Zkc.Source.Structured.Ty.field "bls12-381.fr"),
   operands := [],
   results := [Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")],
   body := [] },
 { operation := Zkc.Construction.Operation.indicesEmpty,
   operands := [],
   results := [Zkc.Construction.ValueSort.indices],
   body := [] },
 { operation := Zkc.Construction.Operation.observe
                  "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6d30_0", "label_6d30_0", "role00000000", "role00000001"] },
   operands := [1, 2, 3],
   results := [Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"],
   body := [] },
 { operation := Zkc.Construction.Operation.indicesEmpty,
   operands := [],
   results := [Zkc.Construction.ValueSort.indices],
   body := [] },
 { operation := Zkc.Construction.Operation.challenge
                  "merlin3.bls12-381.fr64be/0"
                  "bls12-381.fr"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6330", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"] },
   operands := [4, 5],
   results := [Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),
               Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"],
   body := [] },
 { operation := Zkc.Construction.Operation.indicesEmpty,
   operands := [],
   results := [Zkc.Construction.ValueSort.indices],
   body := [] },
 { operation := Zkc.Construction.Operation.observe
                  "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6430_0", "label_6430_0", "role00000001", "role00000000"] },
   operands := [7, 6, 8],
   results := [Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"],
   body := [] },
 { operation := Zkc.Construction.Operation.receive
                  "label_6d31_0"
                  "label_6d31_0"
                  "role00000000"
                  (Zkc.Source.Structured.Ty.field "bls12-381.fr"),
   operands := [],
   results := [Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")],
   body := [] },
 { operation := Zkc.Construction.Operation.indicesEmpty,
   operands := [],
   results := [Zkc.Construction.ValueSort.indices],
   body := [] },
 { operation := Zkc.Construction.Operation.observe
                  "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6d31_0", "label_6d31_0", "role00000000", "role00000001"] },
   operands := [9, 10, 11],
   results := [Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"],
   body := [] },
 { operation := Zkc.Construction.Operation.indicesEmpty,
   operands := [],
   results := [Zkc.Construction.ValueSort.indices],
   body := [] },
 { operation := Zkc.Construction.Operation.challenge
                  "merlin3.bls12-381.fr64be/0"
                  "bls12-381.fr"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6331", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"] },
   operands := [12, 13],
   results := [Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),
               Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"],
   body := [] },
 { operation := Zkc.Construction.Operation.indicesEmpty,
   operands := [],
   results := [Zkc.Construction.ValueSort.indices],
   body := [] },
 { operation := Zkc.Construction.Operation.observe
                  "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6431_0", "label_6431_0", "role00000001", "role00000000"] },
   operands := [15, 14, 16],
   results := [Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"],
   body := [] },
 { operation := Zkc.Construction.Operation.calculate (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr"),
   operands := [2, 6],
   results := [Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")],
   body := [] },
 { operation := Zkc.Construction.Operation.calculate (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr"),
   operands := [18, 14],
   results := [Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")],
   body := [] },
 { operation := Zkc.Construction.Operation.calculate (Zkc.Construction.Calculation.fieldAdd "bls12-381.fr"),
   operands := [19, 0],
   results := [Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")],
   body := [] },
 { operation := Zkc.Construction.Operation.calculate (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr"),
   operands := [10, 14],
   results := [Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")],
   body := [] },
 { operation := Zkc.Construction.Operation.calculate (Zkc.Construction.Calculation.fieldAdd "bls12-381.fr"),
   operands := [21, 0],
   results := [Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")],
   body := [] },
 { operation := Zkc.Construction.Operation.calculate (Zkc.Construction.Calculation.fieldEqual "bls12-381.fr"),
   operands := [20, 22],
   results := [Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.boolean)],
   body := [] }]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem reading_instructions : Code.instructions checkedReading.code = readingInstructions := by
  rw [← Code.instructionList_eq]
  decide +kernel

set_option maxRecDepth 20000 in
theorem reading_returned : checkedReading.returned = [23, 17] := by decide +kernel

set_option maxRecDepth 20000 in
theorem schedule_differs : readingInstructions ≠ ZkcExamples.Construction.DeferredRounds.participant.instructions := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem normalization_checked :
    (CanonicalNormalization.check
      ZkcExamples.Construction.DeferredRounds.participant.inputs
      ZkcExamples.Construction.DeferredRounds.participant.outputs
      ZkcExamples.Construction.DeferredRounds.participant.instructions
      ZkcExamples.Construction.DeferredRounds.participant.returned
      readingInstructions [23, 17]).toOption.isSome = true := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem normalized_schedule (program : Structured.Program) (x : F)
    (history : Domain.History (Structured.uniformCarriers F G)) :
    observation program ZkcExamples.Construction.DeferredRounds.context
      (Code.instructions checkedReading.code) checkedReading.returned
      [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history] =
    observation program ZkcExamples.Construction.DeferredRounds.context
      ZkcExamples.Construction.DeferredRounds.participant.instructions
      ZkcExamples.Construction.DeferredRounds.participant.returned
      [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history] := by
  rw [reading_instructions, reading_returned]
  exact CanonicalNormalization.accepted_sound program _ normalization_checked _ rfl

variable {m : Type → Type} [Monad m]
variable (program : Structured.Program) (key : Origin → Origin) (initial : History F G)
  (challenge : History F G → m F) (cost : String → List (Value F G) → Nat)
  (budget : Nat) (x : F) (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G)

theorem metered_normalized (sufficient : 35 ≤ budget) :
    DomainVM.metered program ZkcExamples.Construction.DeferredRounds.context key initial challenge cost budget
      checkedReading [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history] proof =
    Uniform.DomainAdapter.run key initial challenge
      (DomainVM.observation program ZkcExamples.Construction.DeferredRounds.context
        ZkcExamples.Construction.DeferredRounds.participant.instructions
        ZkcExamples.Construction.DeferredRounds.participant.returned
        [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history]) proof := by
  apply CanonicalNormalization.metered_checked program _ key initial challenge cost budget
    (inputs := ZkcExamples.Construction.DeferredRounds.participant.inputs)
    (outputs := ZkcExamples.Construction.DeferredRounds.participant.outputs)
    (total := 35) ?_ reading_total sufficient _ rfl proof
  rw [reading_instructions, reading_returned]
  exact normalization_checked

theorem metered_prunes_normalized :
    Prunes Stopped
      (DomainVM.metered program ZkcExamples.Construction.DeferredRounds.context key initial challenge cost budget
        checkedReading [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history] proof)
      (Uniform.DomainAdapter.run key initial challenge
        (DomainVM.observation program ZkcExamples.Construction.DeferredRounds.context
          ZkcExamples.Construction.DeferredRounds.participant.instructions
          ZkcExamples.Construction.DeferredRounds.participant.returned
          [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history]) proof) := by
  apply CanonicalNormalization.metered_prunes_checked program _ key initial challenge cost budget
    (inputs := ZkcExamples.Construction.DeferredRounds.participant.inputs)
    (outputs := ZkcExamples.Construction.DeferredRounds.participant.outputs)
    checkedReading ?_ _ rfl proof
  rw [reading_instructions, reading_returned]
  exact normalization_checked

end ZkcExamples.Executable.DeferredRounds
