module

public import Zkc.Construction.ConnectionCalculations
public import Zkc.Construction.DomainCorrespondence
public import Zkc.Executable.DomainSchema
public import Zkc.Executable.DomainNormalizationCheck
public import Zkc.Executable.Helpers

@[expose] public section

/-! Ordered immutable sequences keep exact element identities through the
shared evaluator. Storage budgets belong to the separate native model. -/
namespace Tests.ConstructionSequences
open Zkc.Source Zkc.Source.Structured Zkc.Construction

/-- This equation is independent of any protocol, element type or model. -/
theorem append_meaning (model : FieldModel) (element : Ty)
    (values : List (model.Value element)) (value : model.Value element) :
    Primitive.evaluateOn model (.sequenceAppend element) (.cons values (.cons value .nil)) =
      .returned (.cons (values ++ [value]) .nil) := rfl

theorem access_meaning (model : FieldModel) (element : Ty)
    (values : List (model.Value element)) (index : Nat) :
    Primitive.evaluateOn model (.sequenceAt element) (.cons values (.cons index .nil)) =
      match values[index]? with
      | some value => .returned (.cons value .nil)
      | none => .stopped .refused := rfl

def element : Ty := .product "oracle-reference" "Record" (.cons .index (.cons .index .nil))
private def records (model : DomainModel) : Domain.Value model.toCarriers :=
  .data ⟨.sequence element, rfl, [(5, 9, PUnit.unit), (9, 5, PUnit.unit)]⟩
private def record (model : DomainModel) : Domain.Value model.toCarriers :=
  .data ⟨element, rfl, (9, 5, PUnit.unit)⟩

example (model : DomainModel) : Domain.executePrimitive model (.sequenceAt element)
    [records model, .data (.index 1)] = .returned [record model] := rfl

/-- A failed read has no padding/default result, including at the exact boundary. -/
example (model : DomainModel) : Domain.executePrimitive model (.sequenceAt element)
    [records model, .data (.index 2)] = .stopped .refused := rfl

example (model : DomainModel) : Domain.executePrimitive model (.sequenceAppend element)
    [records model, record model] = .returned
      [.data ⟨.sequence element, rfl,
        [(5, 9, PUnit.unit), (9, 5, PUnit.unit), (9, 5, PUnit.unit)]⟩] := rfl

example (model : DomainModel) : Domain.executePrimitive model (.sequenceLength element)
    [records model] = .returned [.data (.index 2)] := rfl

example (model : DomainModel) : Domain.calculate model (.sequenceLength element)
    [records model] = .returned [.data (.index 2)] := rfl

example (model : DomainModel) : Domain.calculate model (.sequenceEmpty element) [] =
    .returned [.data ⟨.sequence element, rfl, []⟩] := rfl

example (model : DomainModel) : Domain.executePrimitive model
    (.sequenceAt (.product "another-reference" "Record" (.cons .index (.cons .index .nil))))
    [records model, .data (.index 1)] = .stopped .refused := rfl

/-- Empty collections do not erase forbidden handle types. -/
example : (Calculation.sequenceEmpty (.service "private")).total = false := rfl

example : checkClosedStep .local (fun _ _ _ _ => true) []
    ⟨.execute (.sequenceEmpty (.service "private")), [], [.data (.sequence (.service "private"))], []⟩ =
      .error "construction-local-primitive" := rfl

example : checkClosedStep .local (fun _ _ _ _ => true) [.data (.sequence (.service "private"))]
    ⟨.execute (.sequenceLength (.service "private")), [0], [.data .index], []⟩ =
      .error "construction-local-primitive" := rfl

/-- Checked reads remain ordered Local operations even with mathematical element data. -/
example : checkClosedStep .math (fun _ _ _ _ => true) [.data (.sequence element), .data .index]
    ⟨.execute (.sequenceAt element), [0, 1], [.data element], []⟩ =
      .error "construction-math-primitive" := rfl

example : checkClosedStep .math (fun _ _ _ _ => true) []
    ⟨.calculate (.sequenceEmpty element), [], [.data (.sequence element)], []⟩ =
      .ok [.data (.sequence element)] := rfl

/-- Stopping reads remain normalization anchors; total mathematical sequence
construction can move only with an ordinary element type. -/
example : Zkc.Executable.CanonicalNormalization.Instruction.movable
    ⟨.execute (.sequenceAt element), [0, 1], [.data element], []⟩ = false := rfl

example : Zkc.Executable.CanonicalNormalization.Instruction.movable
    ⟨.calculate (.sequenceEmpty element), [], [.data (.sequence element)], []⟩ = true := rfl

example : Zkc.Executable.CanonicalNormalization.Instruction.movable
    ⟨.calculate (.sequenceEmpty (.service "private")), [],
      [.data (.sequence (.service "private"))], []⟩ = false := rfl

/-- Reading a mathematical index does not certify a native index bound. -/
example (model : FieldModel) : Primitive.evaluateOn model (.sequenceAt .index)
    (.cons [indexLimit] (.cons 0 .nil)) = .returned (.cons indexLimit .nil) := rfl

example : Zkc.Executable.primitiveDataProfile (.sequenceAt .index) = false := rfl

example : Zkc.Executable.resultsBounded (.exec (.sequenceAt .index)) = false := rfl

end Tests.ConstructionSequences
