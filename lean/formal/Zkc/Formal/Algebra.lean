module

public import Init.Grind

@[expose] public section

/-! The arithmetic that statements about protocols are proved over.

`Arithmetic` is a commutative ring of scalars, with equality decided, and a module of points
over it. A proof of a property of a protocol uses the laws of a commutative ring (the class
`Lean.Grind.CommRing` of Lean's library, whose identities `grind` decides) and the three laws
of the points stated here, and nothing else about the scalars and the points. It holds in every
such arithmetic; the arithmetic that runs is one of them (`Zkc.Formal.Bls12381`).
-/

set_option autoImplicit false

namespace Zkc.Formal

/-- A commutative ring of scalars and a module of points over it. -/
structure Arithmetic where
  Scalar : Type
  [ring : Lean.Grind.CommRing Scalar]
  [equality : DecidableEq Scalar]
  Point : Type
  identity : Point
  combine : Point → Point → Point
  scale : Point → Scalar → Point
  same : Point → Point → Bool
  same_self : ∀ point, same point point = true
  scale_add : ∀ point first second,
    scale point (first + second) = combine (scale point first) (scale point second)
  scale_scale : ∀ point first second,
    scale (scale point first) second = scale point (first * second)

attribute [instance] Arithmetic.ring Arithmetic.equality

namespace Arithmetic

variable (A : Arithmetic)

/-- The sum of scalars, from zero, the first one first. -/
def sum (values : List A.Scalar) : A.Scalar := values.foldl (· + ·) 0

/-- The sum from a start is the start plus the sum from zero. -/
theorem foldl_add (start : A.Scalar) (values : List A.Scalar) :
    values.foldl (· + ·) start = start + A.sum values := by
  unfold sum
  induction values generalizing start with
  | nil => exact (Lean.Grind.Semiring.add_zero start).symm
  | cons value rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (0 + value)]
    grind

theorem sum_nil : A.sum [] = 0 := rfl

theorem sum_cons (value : A.Scalar) (rest : List A.Scalar) :
    A.sum (value :: rest) = value + A.sum rest := by
  show rest.foldl (· + ·) (0 + value) = _
  rw [foldl_add]
  grind

/-- The sum of two lists, one after the other, is the sum of their sums. -/
theorem sum_append (first second : List A.Scalar) :
    A.sum (first ++ second) = A.sum first + A.sum second := by
  induction first with
  | nil => rw [List.nil_append, sum_nil]; grind
  | cons value rest ih => rw [List.cons_append, sum_cons, sum_cons, ih]; grind

end Arithmetic

end Zkc.Formal
