module

public import Zkc.Realization.QueryResumptionOutput
public import Tests.QueryResumption

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryResumptionOutput
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Realization QueryResumption

/-- Projection keeps both sides of the updated arena, even under an arbitrary
caller suffix. The values are read from actual SSA references. -/
theorem projected (model : DomainModel) (phase kind : Nat) (pending supplied : Coordinates)
    (answers : List Nat) (answer : Nat) (suffix : Domain.Environment model.toCarriers) :
    let frame :=
      Tests.QueryResumption.environment model phase kind pending supplied answers answer ++
      suffix
    Domain.read (frame ++ checkResults 0 ++ answerResults model .index rfl answers answer)
      (outputReferences (Tests.QueryResumption.placement frame.length) [7] [9]) =
        some (outputValues model .index rfl pending 0 answers answer
          [.data (.index 0)] [.data (.index answer)]) := by
  dsimp only
  apply read_output model .index rfl _ _ rfl
  · exact (RequiredIndices.Readback.cons rfl rfl
      (.cons rfl rfl (.cons rfl rfl (.cons rfl rfl (.cons rfl rfl .nil))))).extended suffix
  · exact RecordAllocator.read_extended _ suffix _ _ rfl
  · exact RecordAllocator.read_extended _ suffix _ _ rfl

/-- The returned answer index is the old length, not the phase or a coordinate
with the same type. Such a swap changes the actual output. -/
theorem wrong_answer_index (model : DomainModel) :
    Domain.read (checkResults (carriers := model.toCarriers) 0 ++
        answerResults model .index rfl [31, 37] 41) [11, 9] ≠
      Domain.read (checkResults (carriers := model.toCarriers) 0 ++
        answerResults model .index rfl [31, 37] 41) [9, 11] := by
  intro swapped
  have impossible : (1 : Nat) = 2 := by
    simpa [Domain.read, checkResults, RequiredIndices.results, answerResults,
      Domain.Value.decode, Domain.Payload.value] using congrArg (fun values ↦
        values.bind fun entries ↦ entries.head?.bind (Domain.Value.decode .index)) swapped
  contradiction

#print axioms projected
#print axioms wrong_answer_index
end Tests.QueryResumptionOutput
