module

public import Zkc.Construction.ConnectionCalculations
public import Zkc.Executable.DomainSchema

@[expose] public section

/-! Installed primitives keep machine ingress checks and partial outcomes.
The same-typed mathematical word operations have their own distinct meaning. -/
namespace Tests.ConstructionPrimitives
open Zkc.Source Zkc.Construction

example (model : Structured.DomainModel) :
    Domain.executePrimitive model .indexEqual
      [.data (.index Structured.indexLimit), .data (.index Structured.indexLimit)] =
        .stopped .refused ∧
    Domain.calculate model .indexEqual
      [.data (.index Structured.indexLimit), .data (.index Structured.indexLimit)] =
        .returned [.data (.boolean true)] := by
  constructor
  · simp only [Domain.executePrimitive, Structured.Primitive.arguments, Domain.decodeValues,
      Domain.Value.decode, Domain.Payload.value, ↓reduceDIte,
      Structured.Primitive.evaluateOn, Structured.checkedIndices]
    norm_num [Structured.indexLimit]
    rfl
  · change PIR.Outcome.returned [Domain.Value.data (Domain.Payload.boolean
      (decide (Structured.indexLimit = Structured.indexLimit)))] = _
    simp

example (model : Structured.DomainModel) :
    Domain.executePrimitive model .indexAdd
      [.data (.index (Structured.indexLimit - 1)), .data (.index 1)] = .stopped .refused ∧
    Domain.calculate model .indexWrappingAdd
      [.data (.index (Structured.indexLimit - 1)), .data (.index 1)] =
        .returned [.data (.index 0)] := by
  constructor
  · simp only [Domain.executePrimitive, Structured.Primitive.arguments, Domain.decodeValues,
      Domain.Value.decode, Domain.Payload.value, ↓reduceDIte,
      Structured.Primitive.evaluateOn, Structured.checkedIndices]
    norm_num [Structured.indexLimit]
    rfl
  · change PIR.Outcome.returned [Domain.Value.data (Domain.Payload.index
      (Structured.wrappingAdd (Structured.indexLimit - 1) 1))] = _
    norm_num [Structured.wrappingAdd, Structured.indexLimit, Structured.wordModulus]

example (model : Structured.DomainModel) :
    Domain.executePrimitive model .indexLess
      [.data (.index 7), .data (.index 8)] = .returned [.data (.boolean true)] := rfl

example (model : Structured.DomainModel) :
    Domain.executePrimitive model .indexLess
      [.data (.index 7), .data (.index Structured.indexLimit)] = .stopped .refused := by
  simp only [Domain.executePrimitive, Structured.Primitive.arguments, Domain.decodeValues,
    Domain.Value.decode, Domain.Payload.value, ↓reduceDIte,
    Structured.Primitive.evaluateOn, Structured.checkedIndices]
  norm_num [Structured.indexLimit]
  rfl

example (model : Structured.DomainModel) :
    Domain.executePrimitive model .booleanNot [.data (.boolean false)] =
      .returned [.data (.boolean true)] := rfl

/-- An installed primitive inside an embedded Math body remains inadmissible. -/
example : checkClosedStep .math (fun _ _ _ _ => true) [.data .index, .data .index]
    ⟨.execute .indexLess, [0, 1], [.data .boolean], []⟩ =
      .error "construction-math-primitive" := rfl

example : checkClosedStep .local (fun _ _ _ _ => true) [.data .index, .data .index]
    ⟨.execute .indexLess, [0, 1], [.data .boolean], []⟩ =
      .ok [.data .index, .data .index, .data .boolean] := rfl

/-- The generic view theorem preserves both success and stopping outcomes. -/
example (model : Structured.DomainModel) (program : Structured.Program) (context : Context)
    (primitive : Structured.Primitive) (references : List Nat) (declared : List ValueSort) :
    Domain.Correspondence.Step (model := model) (program := program) (context := context)
      ⟨.execute primitive, references, declared, []⟩ (Domain.View.execute model primitive references declared) :=
  Domain.Correspondence.execute primitive references declared

end Tests.ConstructionPrimitives
