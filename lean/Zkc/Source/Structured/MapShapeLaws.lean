module

public import Zkc.Source.Structured.MapEvaluation

@[expose] public section

/-! Constructor equations for ordered map-shape admission. Clients can rewrite
through this interface without generating their own recursive unfold proofs. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.Evaluation

theorem mapShapeRemaining_nil (expected : Nat) :
    mapShapeRemaining expected [] = .returned expected := rfl

theorem mapShapeRemaining_cons (expected length : Nat) (rest : List Nat) :
    mapShapeRemaining expected (length :: rest) =
      if length < indexLimit then
        if length = expected then mapShapeRemaining expected rest else .stopped .refused
      else .stopped .exhausted := rfl

theorem mapShape_nil : mapShape [] = .stopped .refused := rfl

theorem mapShape_cons (length : Nat) (rest : List Nat) :
    mapShape (length :: rest) =
      if length < indexLimit then mapShapeRemaining length rest else .stopped .exhausted := rfl

end Zkc.Source.Structured.Evaluation
