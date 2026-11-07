module

public import Zkc.Realization.RecordAllocator

@[expose] public section

namespace Tests.RecordAllocator
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open Zkc.Realization.RecordAllocator

def layout : Layout := ⟨7, "record", "reference", .cons .index (.cons .index .nil)⟩

def record (model : DomainModel) : model.Value layout.recordType := (13, 29, ())

def inputs (model : DomainModel) : Domain.Environment model.toCarriers :=
  [.data ⟨.sequence layout.recordType, rfl, []⟩, .data (.index 13), .data (.index 29)]

/-- The same library rule works in any caller frame; its operands and every
intermediate result retain their actual offsets. -/
noncomputable def placed (model : DomainModel) (caller : Domain.Environment model.toCarriers) :
    Original.Simulation Eq (fun _ frame ↦ caller ++ inputs model <+: frame)
      (.done (result model layout rfl (caller ++ inputs model) [] (record model)))
      ((spine layout ⟨(caller ++ inputs model).length, caller.length,
        [caller.length + 1, caller.length + 2]⟩).block model (caller ++ inputs model)) := by
  apply simulation model layout rfl rfl
  · simp [inputs]
  · simp [inputs, Domain.read, layout, record, ProductFields.unpack]
    rfl
  · decide
  · change 0 < indexLimit
    decide

/-- Full instruction semantics, not a synthetic storage interpreter. -/
noncomputable def actual (model : DomainModel) (program : Program) (context : Context)
    (caller : Domain.Environment model.toCarriers) :
    Original.Simulation Eq (fun _ frame ↦ caller ++ inputs model <+: frame)
      (.done (result model layout rfl (caller ++ inputs model) [] (record model)))
      (Domain.evaluate model program context
        (instructions layout ⟨(caller ++ inputs model).length, caller.length,
          [caller.length + 1, caller.length + 2]⟩) (caller ++ inputs model)) := by
  rw [correspondence]
  exact placed model caller

/-- Two concrete placements select the same proof, with different caller sizes. -/
example (model : DomainModel) : Nonempty (Original.Simulation Eq
    (fun _ frame ↦ inputs model <+: frame)
    (.done (result model layout rfl (inputs model) [] (record model)))
    ((spine layout ⟨3, 0, [1, 2]⟩).block model (inputs model))) := ⟨placed model []⟩

example (model : DomainModel) : Nonempty (Original.Simulation Eq
    (fun _ frame ↦ [.data (.boolean true), .data (.index 5)] ++ inputs model <+: frame)
    (.done (result model layout rfl ([.data (.boolean true), .data (.index 5)] ++ inputs model)
      [] (record model)))
    ((spine layout ⟨5, 2, [3, 4]⟩).block model
      ([.data (.boolean true), .data (.index 5)] ++ inputs model))) := ⟨placed model _⟩

/-- Placement follows the admitted operand graph, not an external offset table. -/
example : (recognize (instructions layout ⟨19, 4, [8, 12]⟩)).isSome = true := by
  decide +kernel

example : (recognize ((instructions layout ⟨3, 0, [1, 2]⟩).set 4
    ⟨.calculate (.makeProduct layout.referenceIdentity "Record" referenceFields),
      [4, 3], [.data layout.referenceType], []⟩)).isSome = false := by decide +kernel

example : (recognize ((instructions layout ⟨3, 0, [1, 2]⟩).set 1
    ⟨.calculate (.sequenceLength layout.recordType), [0], [.data .index], []⟩)).isSome =
    false := by decide +kernel

/-- Same-typed field and reference swaps change the admitted instruction body. -/
example : instructions layout ⟨3, 0, [1, 2]⟩ ≠ instructions layout ⟨3, 0, [2, 1]⟩ := by decide +kernel

example : (instructions layout ⟨3, 0, [1, 2]⟩)[4]? ≠
    some ⟨.calculate (.makeProduct layout.referenceIdentity "Record" referenceFields),
      [4, 3], [.data layout.referenceType], []⟩ := by decide +kernel

example (model : DomainModel) :
    Domain.View.execute model (.indexConstant indexLimit) [] [.data .index] [] = .halt .refused := by
  have law := ConnectionPrimitives.view_execute model (.indexConstant indexLimit) .nil rfl rfl [] [] rfl
  simpa [Primitive.evaluateOn, Primitive.results, primitiveOutcome, PIR.Process.bind] using law

example (model : DomainModel) (environment : Domain.Environment model.toCarriers) :
    Nonempty (Original.Simulation (Eq (α := Domain.Environment model.toCarriers))
      (fun _ frame ↦ environment <+: frame) (.halt .refused)
      ((spine { layout with constructor := indexLimit } ⟨environment.length, 0, [1, 2]⟩).block
        model environment)) :=
  ⟨refused_constructor model _ _ environment (by simp)⟩

#print axioms Zkc.Realization.RecordAllocator.correspondence
#print axioms Zkc.Realization.RecordAllocator.simulation
#print axioms actual
#print axioms Zkc.Realization.RecordAllocator.Recognized.simulation
#print axioms Zkc.Realization.RecordAllocator.refused_constructor
end Tests.RecordAllocator
