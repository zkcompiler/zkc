module

public import Zkc.Source.Structured.PrimitiveEvaluation
public import Zkc.Source.Finite

@[expose] public section

/-! Ordered shape admission and row invocation through the existing helper table.
Lengths are logical naturals; observer capacity is a separate boundary. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Evaluation

/-- Every row contributes a length, including unused helper operands. -/
def mapLengths {F G : Type} (field : String) : (mask : List Bool) →
    Values (assignment F G) (mask.map (fun row => if row then .vector field else .field field)) → List Nat
  | [], .nil => []
  | true :: rest, .cons row args => row.length :: mapLengths field rest args
  | false :: rest, .cons _ args => mapLengths field rest args

/-- Check each later row's representability and then equality before continuing. -/
def mapShapeRemaining (expected : Nat) : List Nat → PIR.Outcome Nat
  | [] => .returned expected
  | length :: rest =>
      if length < indexLimit then
        if length = expected then mapShapeRemaining expected rest else .stopped .refused
      else .stopped .exhausted

/-- A missing row is refused; admitted maps have at least one rowwise operand. -/
def mapShape : List Nat → PIR.Outcome Nat
  | [] => .stopped .refused
  | length :: rest =>
      if length < indexLimit then mapShapeRemaining length rest else .stopped .exhausted

/-- Construct the full scalar tuple in original argument order, retaining broadcasts. -/
def mapRowArguments {F G : Type} (field : String) : (mask : List Bool) →
    Values (assignment F G) (mask.map (fun row => if row then .vector field else .field field)) →
    Nat → Option (Values (assignment F G) (mask.map (fun _ => .field field)))
  | [], .nil, _ => some .nil
  | true :: rest, .cons row args, index => do
      let value ← (show List F from row)[index]?
      let values ← mapRowArguments field rest args index
      pure (.cons value values)
  | false :: rest, .cons value args, index => do
      let values ← mapRowArguments field rest args index
      pure (.cons value values)

/-- One reached row calls the exact computed Math signature in the shared table. -/
def mapRow {F G : Type} {I : PIR.Signature}
    (table : HelperTable (assignment F G) I) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments) (index : Nat) : PIR.Proc I F :=
  match mapRowArguments spec.field spec.rowwise args index with
  | none => .halt .refused
  | some values => (invoke table spec.helper values).bind fun result => .done (result.get .here)

/-- Ordered traversal uses ordinary process bind, preserving every effect prefix. -/
def mapRows {I : PIR.Signature} {F : Type} (row : Nat → PIR.Proc I F) :
    List Nat → PIR.Proc I (List F)
  | [] => .done []
  | index :: rest => (row index).bind fun value =>
      (mapRows row rest).bind fun values => .done (value :: values)

def denoteMap {F G : Type} {I : PIR.Signature}
    (table : HelperTable (assignment F G) I) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments) :
    PIR.Proc I (Values (assignment F G) [.vector spec.field]) :=
  Finite.admitThen (mapShape (mapLengths spec.field spec.rowwise args)) fun length =>
    (mapRows (mapRow table spec args) (List.range length)).bind fun values =>
      .done (.cons values .nil)

attribute [local simp] mapLengths mapRowArguments

end Zkc.Source.Structured.Evaluation
