import Zkc.Algebra.BoundedResidues

set_option autoImplicit false

namespace Tests.BoundedResidues

example : (255 + 1 : ZMod 65537) = 0 + 256 * 1 := by decide

example : 0 = (255 + 1) % 256 :=
  Zkc.Algebra.word_addition (p := 65537) (by decide) (by decide)
    (by decide) (Or.inr rfl) (by decide) (by decide)

-- Omitting the total bound really loses integer conservation.
example : (1 : ZMod 7) = (6 : ZMod 7) + 2 := by decide
example : (1 : Nat) ≠ 6 + 2 := by decide

-- Individual words fit this field, but their sum wraps before the word base.
example : (6 : ZMod 7) + 6 = 5 + 8 * 0 := by decide
example : (5 : Nat) ≠ (6 + 6) % 8 := by decide

example : 101 = 98 + 3 :=
  Zkc.Algebra.integer_conservation (p := 257) (by decide) (by decide) (by decide)

end Tests.BoundedResidues
