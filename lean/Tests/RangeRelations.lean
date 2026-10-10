import Zkc.Protocols.RangeProof.Relations
import Zkc.Protocols.RangeProof.Bits
import Mathlib.Tactic

set_option autoImplicit false

namespace Tests.RangeRelations

open Zkc.Protocols.RangeProof

example : ofBits [true, false, true, false, false, false, false, false] = 5 := by decide
example : ofBits [true, false, false] ≠ ofBits [false, false, true] := by decide

-- Removing the residual is wrong even for one coordinate and nonzero weights.
example :
    ((2 : ZMod 101) - 3) * (5 * (2 - 1 + 3) + 7) ≠
      (3 - 3 ^ 2) * 5 + (2 - 3) * 7 := by native_decide

example (a y d : Fin 16 → ZMod 101) (z : ZMod 101) :
    (∑ i, (a i - z) * (y i * (a i - 1 + z) + d i)) =
      (∑ i, y i * (a i * (a i - 1))) +
      (z - z ^ 2) * (∑ i, y i) +
      (∑ i, a i * d i) - z * (∑ i, d i) :=
  constant_term a y d z

example (value : ZMod 257)
    (h : value = (ofBits [true, false, true, false, false, false, false, false] : ZMod 257)) :
    value.val < 256 := reconstruction_range value _ (by decide) h

end Tests.RangeRelations
