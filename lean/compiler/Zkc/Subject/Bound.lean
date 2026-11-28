module

@[expose] public section
set_option autoImplicit false

/-! The number that a goal claims. -/

namespace Zkc.Subject

/-- The number by which a goal bounds a probability: a rational that is not negative, as a
numerator over a positive denominator. It is the ceiling that the goal writes, and where the
goal writes none, the total of the charges of its contract.

Two values are equal when their spellings are: `1/2` and `2/4` are different values that bound
by the same number. The issuer writes a bound in lowest terms. -/
structure Bound where
  numerator : Nat
  denominator : Nat
  positive : 0 < denominator

end Zkc.Subject
