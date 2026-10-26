module

public import ZkcExamples.Executable.DeferredRoundsFacts
public import Zkc.Executable.DomainNormalization
public import Zkc.Construction.DomainCorrespondence
public import Zkc.Construction.Uniform.SourceProcess

@[expose] public section

/-! The actual nonidentical DeferredRounds schedule, compared at canonical
Domain outcomes. The arithmetic before the second receive in the source is
computed after the second query in the executable reading. The proof quantifies
over every receive and query reply; no relation truth or honest proof is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcExamples.Executable.DeferredRounds
open Zkc Zkc.Construction Zkc.Source Zkc.Executable
open Zkc.Executable.DomainVM Zkc.Construction.Uniform.SourceProcess
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

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
theorem reading_instructions : Code.instructions lowered.code = readingInstructions := by
  rw [← Code.instructionList_eq]
  decide +kernel

set_option maxRecDepth 20000 in
theorem reading_returned : lowered.returned = [23, 17] := by decide +kernel

set_option maxRecDepth 20000 in
theorem schedule_differs : readingInstructions ≠ ZkcExamples.Construction.DeferredRounds.participant.instructions := by
  decide +kernel

set_option maxRecDepth 20000 in
private def readingView (program : Structured.Program) :
    {view : Domain.View.Block (Structured.uniformCarriers F G) //
      Domain.Correspondence.Block (model := Structured.ringModel F G) (program := program)
        (context := readingContext) readingInstructions view} := by
  exact ⟨_, Domain.Correspondence.sequence (Domain.Correspondence.receive "label_6d30_0"
                  "label_6d30_0"
                  "role00000000"
                  (Zkc.Source.Structured.Ty.field "bls12-381.fr") ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.observe "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6d30_0", "label_6d30_0", "role00000000", "role00000001"] } 1 2 3 ([Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.challenge "merlin3.bls12-381.fr64be/0"
                  "bls12-381.fr"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6330", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"] } 4 5 ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),
               Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.observe "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6430_0", "label_6430_0", "role00000001", "role00000000"] } 7 6 8 ([Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.receive "label_6d31_0"
                  "label_6d31_0"
                  "role00000000"
                  (Zkc.Source.Structured.Ty.field "bls12-381.fr") ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.observe "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6d31_0", "label_6d31_0", "role00000000", "role00000001"] } 9 10 11 ([Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.challenge "merlin3.bls12-381.fr64be/0"
                  "bls12-381.fr"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6331", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"] } 12 13 ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),
               Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.observe "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6431_0", "label_6431_0", "role00000001", "role00000000"] } 15 14 16 ([Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr") ([2, 6]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr") ([18, 14]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldAdd "bls12-381.fr") ([19, 0]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr") ([10, 14]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldAdd "bls12-381.fr") ([21, 0]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldEqual "bls12-381.fr") ([20, 22]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.boolean)]))
      (Domain.Correspondence.empty))))))))))))))))))))⟩

set_option maxRecDepth 20000 in
private def exportedView (program : Structured.Program) :
    {view : Domain.View.Block (Structured.uniformCarriers F G) //
      Domain.Correspondence.Block (model := Structured.ringModel F G) (program := program)
        (context := readingContext) ZkcExamples.Construction.DeferredRounds.participant.instructions view} := by
  exact ⟨_, Domain.Correspondence.sequence (Domain.Correspondence.receive "label_6d30_0"
                  "label_6d30_0"
                  "role00000000"
                  (Zkc.Source.Structured.Ty.field "bls12-381.fr") ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.observe "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6d30_0", "label_6d30_0", "role00000000", "role00000001"] } 1 2 3 ([Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.challenge "merlin3.bls12-381.fr64be/0"
                  "bls12-381.fr"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6330", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"] } 4 5 ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),
               Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.observe "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6430_0", "label_6430_0", "role00000001", "role00000000"] } 7 6 8 ([Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr") ([2, 6]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.receive "label_6d31_0"
                  "label_6d31_0"
                  "role00000000"
                  (Zkc.Source.Structured.Ty.field "bls12-381.fr") ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.observe "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6d31_0", "label_6d31_0", "role00000000", "role00000001"] } 9 11 12 ([Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.challenge "merlin3.bls12-381.fr64be/0"
                  "bls12-381.fr"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["query", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6331", "input_2", "random.bls12-381.fr/0", "draw", "role00000001"] } 13 14 ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr"),
               Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.indicesEmpty ([Zkc.Construction.ValueSort.indices]))
      (Domain.Correspondence.sequence (Domain.Correspondence.observe "merlin3.bls12-381.fr64be/0"
                  { entry := "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                    steps := [],
                    event := ["message", "zkl_2c85a03e4ef7c48412e5b5f9549ac1046d606d881fe23614fbad9f174aebe56b",
                              "label_6431_0", "label_6431_0", "role00000001", "role00000000"] } 16 15 17 ([Zkc.Construction.ValueSort.transcript "merlin3.bls12-381.fr64be/0"]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr") ([10, 15]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldAdd "bls12-381.fr") ([19, 0]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldMultiply "bls12-381.fr") ([11, 15]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldAdd "bls12-381.fr") ([21, 0]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.field "bls12-381.fr")]))
      (Domain.Correspondence.sequence (Domain.Correspondence.calculation (Zkc.Construction.Calculation.fieldEqual "bls12-381.fr") ([20, 22]) ([Zkc.Construction.ValueSort.data (Zkc.Source.Structured.Ty.boolean)]))
      (Domain.Correspondence.empty))))))))))))))))))))⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem normalized_schedule (program : Structured.Program) (x : F)
    (history : Domain.History (Structured.uniformCarriers F G)) :
    observation program ZkcExamples.Construction.DeferredRounds.context
      (Code.instructions lowered.code) lowered.returned
      [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history] =
    observation program ZkcExamples.Construction.DeferredRounds.context
      ZkcExamples.Construction.DeferredRounds.participant.instructions
      ZkcExamples.Construction.DeferredRounds.participant.returned
      [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history] := by
  rw [reading_instructions, reading_returned, reading_context]
  unfold DomainVM.observation outcome
  rw [(readingView (F := F) (G := G) program).property,
    (exportedView (F := F) (G := G) program).property]
  normalize_scalar_connection unfolding [readback, readingView, exportedView, readingContext,
    ZkcExamples.Construction.DeferredRounds.participant,
    ZkcExamples.Construction.DeferredRoundsParticipant.participant]

variable {m : Type → Type} [Monad m]
variable (program : Structured.Program) (key : Origin → Origin) (initial : History F G)
  (challenge : History F G → m F) (cost : String → List (Value F G) → Nat)
  (budget : Nat) (x : F) (history : Domain.History (Structured.uniformCarriers F G)) (proof : Proof F G)

theorem metered_normalized (sufficient : 35 ≤ budget) :
    DomainVM.metered program ZkcExamples.Construction.DeferredRounds.context key initial challenge cost budget
      lowered [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history] proof =
    Uniform.DomainAdapter.run key initial challenge
      (DomainVM.observation program ZkcExamples.Construction.DeferredRounds.context
        ZkcExamples.Construction.DeferredRounds.participant.instructions
        ZkcExamples.Construction.DeferredRounds.participant.returned
        [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history]) proof := by
  exact (metered_static_observation program _ key initial challenge cost budget
    (lowered := lowered) total sufficient _ proof).trans
      (congrArg (fun process => Uniform.DomainAdapter.run key initial challenge process proof)
        (normalized_schedule program x history))

theorem metered_prunes_normalized :
    Prunes Stopped
      (DomainVM.metered program ZkcExamples.Construction.DeferredRounds.context key initial challenge cost budget
        lowered [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history] proof)
      (Uniform.DomainAdapter.run key initial challenge
        (DomainVM.observation program ZkcExamples.Construction.DeferredRounds.context
          ZkcExamples.Construction.DeferredRounds.participant.instructions
          ZkcExamples.Construction.DeferredRounds.participant.returned
          [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history]) proof) := by
  have result := metered_prunes_observation program ZkcExamples.Construction.DeferredRounds.context
    key initial challenge cost budget lowered
    [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history] proof
  exact (congrArg (fun process => Prunes Stopped
    (DomainVM.metered program ZkcExamples.Construction.DeferredRounds.context key initial challenge cost budget
      lowered [.data (.field "bls12-381.fr" x), .transcript "merlin3.bls12-381.fr64be/0" history] proof)
    (Uniform.DomainAdapter.run key initial challenge process proof))
    (normalized_schedule program x history)).mp result

end ZkcExamples.Executable.DeferredRounds
