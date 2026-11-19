module

public import Zkc.Core.CanonicalLayoutValues
public import Zkc.Core.VocabularyArithmetic
public import Zkc.Formal.Algebra

@[expose] public section

/-! The scalar field and the group G1 of BLS12-381, as the model that runs computes them.

The model that runs computes on data: a scalar is a number, read modulo the order of the
field, and a point is a pair of coordinates. `arithmetic` makes of that an arithmetic in the
sense of `Zkc.Formal.Arithmetic`: its scalars are the residues modulo the order, and its points
are the points of the group G1.

The laws of the scalars are those of the residues, which Lean's library proves. The laws of
the curve are facts of its arithmetic, which nothing here proves: they are the named
hypotheses `Vocabulary.GroupClosedUnderMultiples`, of the core, and `CurveLaws`. A statement
that uses `arithmetic` names them, and a receipt carries their names. `CurveLaws.holdsAt` is
their executable check at given points and scalars.
-/

set_option autoImplicit false

namespace Zkc.Formal.Bls12381

open Zkc.Core Zkc.Core.Concrete

/-- The order of the group and of its scalar field. -/
abbrev order : Nat := Vocabulary.bls12381Order

instance : NeZero order := ⟨by decide⟩

/-- The laws of the arithmetic of the curve that proofs use, of the points of the group: the
sum of two points of the group is of the group, and the multiples of a point are a module over
the scalars. Each is a fact of the arithmetic of the curve as `Concrete.addPoints` and
`Concrete.scalePoint` compute it, which this package does not prove. -/
structure CurveLaws : Prop where
  sum_inGroup : ∀ first second : Concrete.Point, Vocabulary.inGroup first = true →
    Vocabulary.inGroup second = true → Vocabulary.inGroup (addPoints first second) = true
  scale_add : ∀ (point : Concrete.Point) (first second : Nat), Vocabulary.inGroup point = true →
    scalePoint point ((first + second) % order) =
      addPoints (scalePoint point first) (scalePoint point second)
  scale_scale : ∀ (point : Concrete.Point) (first second : Nat), Vocabulary.inGroup point = true →
    scalePoint (scalePoint point first) second = scalePoint point (first * second % order)

/-- The laws of the curve at one point and two scalars, as the arithmetic computes them: the
executable check of `CurveLaws` there. -/
def CurveLaws.holdsAt (point : Concrete.Point) (first second : Nat) : Bool :=
  Vocabulary.inGroup (addPoints (scalePoint point first) (scalePoint point second)) &&
    scalePoint point ((first + second) % order) ==
      addPoints (scalePoint point first) (scalePoint point second) &&
    scalePoint (scalePoint point first) second == scalePoint point (first * second % order)

/-- A point of the group G1. -/
structure GroupPoint where
  point : Concrete.Point
  inGroup : Vocabulary.inGroup point = true

theorem GroupPoint.ext {first second : GroupPoint} (same : first.point = second.point) :
    first = second := by
  cases first; cases second; cases same; rfl

/-- The residues modulo the order as scalars and the group G1 as points, under the laws of the
curve. -/
@[reducible] def arithmetic (closed : Vocabulary.GroupClosedUnderMultiples) (laws : CurveLaws) :
    Arithmetic where
  Scalar := Fin order
  Point := GroupPoint
  identity := ⟨none, Vocabulary.inGroup_infinity⟩
  combine first second :=
    ⟨addPoints first.point second.point, laws.sum_inGroup _ _ first.inGroup second.inGroup⟩
  scale point scalar :=
    ⟨scalePoint point.point scalar.val, closed.multiple_inGroup _ _ point.inGroup⟩
  same first second := first.point == second.point
  same_self point := beq_self_eq_true point.point
  scale_add point first second := by
    apply GroupPoint.ext
    show scalePoint point.point (first + second).val =
      addPoints (scalePoint point.point first.val) (scalePoint point.point second.val)
    rw [Fin.val_add, laws.scale_add _ _ _ point.inGroup]
  scale_scale point first second := by
    apply GroupPoint.ext
    show scalePoint (scalePoint point.point first.val) second.val =
      scalePoint point.point (first * second).val
    rw [Fin.val_mul, laws.scale_scale _ _ _ point.inGroup]

end Zkc.Formal.Bls12381
