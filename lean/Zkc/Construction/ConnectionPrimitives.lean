module

public import Zkc.Construction.ConnectionCalculations

@[expose] public section

/-! A single nominal connection rule for installed checked primitives. It
uses the actual structured outcome, preserving arithmetic ingress, exhaustion
and refusal. Mathematical calculations keep their separate totality rules. -/

set_option autoImplicit false
namespace Zkc.Construction.ConnectionPrimitives
open Zkc.Source Zkc.Source.Structured

/-- Complete local types supply decoding and result encoding. The primitive's
actual outcome supplies the values or stop; no totality premise is introduced. -/
theorem execute_encoded (model : DomainModel) (primitive : Primitive)
    (arguments : Values model.Value primitive.arguments)
    (inputData : primitive.arguments.all Domain.localType = true)
    (outputData : primitive.results.all Domain.localType = true) :
    Domain.executePrimitive model primitive (Original.encodeHelperResult arguments) =
      (match primitive.evaluateOn model.toFieldModel arguments with
      | .returned results => .returned (Original.encodeHelperResult results)
      | .stopped reason => .stopped reason) := by
  have decoded := Domain.decodeValues_encodeValues (Original.encodeHelperResult_eq inputData arguments)
  simp only [Domain.executePrimitive, decoded]
  cases primitive.evaluateOn model.toFieldModel arguments with
  | stopped reason => rfl
  | returned results => simp only [Original.encodeHelperResult_eq outputData results]

/-- The view of any actual execute instruction follows from its typed operand
readback. Failed operations never append results or run the continuation. -/
theorem view_execute (model : DomainModel) (primitive : Primitive)
    (arguments : Values model.Value primitive.arguments)
    (inputData : primitive.arguments.all Domain.localType = true)
    (outputData : primitive.results.all Domain.localType = true)
    (environment : Domain.Environment model.toCarriers) (references : List Nat)
    (read : Domain.read environment references = Domain.encodeValues arguments) :
    Domain.View.execute model primitive references (primitive.results.map ValueSort.data) environment =
      (primitiveOutcome (I := Domain.effects model.toCarriers)
        (primitive.evaluateOn model.toFieldModel arguments)).bind
          (fun results ↦ .done (environment ++ Original.encodeHelperResult results)) := by
  simp only [Domain.View.execute, read, Original.encodeHelperResult_eq inputData arguments,
    execute_encoded model primitive arguments inputData outputData]
  cases primitive.evaluateOn model.toFieldModel arguments with
  | stopped reason => rfl
  | returned results =>
    simp only [Domain.View.append, Original.encodeHelperResult_sorts outputData results,
      ↓reduceIte, primitiveOutcome, PIR.Process.bind]

end Zkc.Construction.ConnectionPrimitives
