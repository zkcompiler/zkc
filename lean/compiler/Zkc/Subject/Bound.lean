module

@[expose] public section
set_option autoImplicit false

/-! The number that a goal claims. -/

namespace Zkc.Subject

/-- The number by which a goal bounds a probability: a rational that is not negative, as a
numerator over a positive denominator. It is the ceiling that the goal writes, and where the
goal writes none, the total of the charges of its contract. -/
structure Bound where
  numerator : Nat
  denominator : Nat
  positive : 0 < denominator

end Zkc.Subject
