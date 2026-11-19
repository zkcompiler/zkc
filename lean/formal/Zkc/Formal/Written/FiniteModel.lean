module

public import Zkc.Formal.Written.StandardModel

@[expose] public section
namespace Zkc.Formal.Written.FiniteModel
open Core

/-- An executable instance in characteristic two. The dispatch, guards and correctness of
each typed row are shared with every other instance of the standard model. -/
def ops : Operations Bool Bool := ⟨false, xor, and, id, xor, and⟩

def data : StandardModel.Data Bool Bool where
  toOperations := ops
  scalarAdd := xor
  zeroPoint := false
  unit := ⟨true, by decide⟩
  literal n := n % 2 == 1
  literalZero := rfl
  invNonzero := by intro x h; exact h

abbrev model := StandardModel.model data
abbrev rows := StandardModel.groupRows data
abbrev functionRows := StandardModel.functionRows data

def laws : ActionLaws ops where
  one := true
  difference := xor
  sub_zero := by decide
  cancel_left := by decide
  scale_sub := by decide
  scale_mul := by decide
  scale_one := by decide
  mul_inv := by decide

end Zkc.Formal.Written.FiniteModel
