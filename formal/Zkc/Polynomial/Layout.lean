import Zkc.Polynomial.Multilinear

/-! High-bit logical coordinates and low-bit storage for multilinear tables.

Bit reversal permutes storage positions, never the logical evaluation point.
The polynomial equality also preserves every ordered restriction and Boolean
sum. These are representation laws over any commutative ring, including arity
zero; they do not specify a codec or establish a native kernel refinement.
-/

set_option autoImplicit false

namespace Zkc.Polynomial.Layout

def bitReverse (n : Nat) (i : Fin (2 ^ n)) : Fin (2 ^ n) :=
  Multilinear.index n (Multilinear.vertex n i ∘ Fin.rev)

def lowIndex (n : Nat) (bits : Fin n → Bool) : Fin (2 ^ n) :=
  Multilinear.index n (bits ∘ Fin.rev)

theorem bitReverse_involutive (n : Nat) : Function.Involutive (bitReverse n) := by
  intro i
  simp [bitReverse, Multilinear.vertex_index, Function.comp_def,
    Multilinear.index_vertex]

theorem bitReverse_lowIndex (n : Nat) (bits : Fin n → Bool) :
    bitReverse n (lowIndex n bits) = Multilinear.index n bits := by
  simp [bitReverse, lowIndex, Multilinear.vertex_index, Function.comp_def]

variable {F : Type} {n : Nat}

/-- Store a logical high-bit vector in low-bit order. -/
def toLowStorage (values : Fin (2 ^ n) → F) : Fin (2 ^ n) → F :=
  values ∘ bitReverse n

/-- Interpret a low-bit storage vector at logical Boolean coordinates. -/
def ofLowStorage (values : Fin (2 ^ n) → F) : Multilinear.Table F n :=
  fun bits => values (lowIndex n bits)

theorem toLowStorage_involutive (values : Fin (2 ^ n) → F) :
    toLowStorage (toLowStorage values) = values := by
  funext i
  exact congrArg values (bitReverse_involutive n i)

theorem table_eq (values : Fin (2 ^ n) → F) :
    ofLowStorage (toLowStorage values) = Multilinear.ofVector values := by
  funext bits
  simp [ofLowStorage, toLowStorage, Multilinear.ofVector, bitReverse_lowIndex]

variable [CommRing F]

theorem extension_eq (values : Fin (2 ^ n) → F) (point : Fin n → F) :
    Multilinear.extension n (ofLowStorage (toLowStorage values)) point =
      Multilinear.extension n (Multilinear.ofVector values) point := by
  rw [table_eq]

theorem product_eq (left right : Fin (2 ^ n) → F) :
    Multilinear.productCoefficients n (ofLowStorage (toLowStorage left))
      (ofLowStorage (toLowStorage right)) =
    Multilinear.productCoefficients n (Multilinear.ofVector left)
      (Multilinear.ofVector right) := by
  rw [table_eq, table_eq]

theorem product_eval (left right : Fin (2 ^ n) → F) (point : Fin n → F) :
    (Multilinear.productCoefficients n (ofLowStorage (toLowStorage left))
      (ofLowStorage (toLowStorage right))).eval point =
    Multilinear.extension n (Multilinear.ofVector left) point *
      Multilinear.extension n (Multilinear.ofVector right) point := by
  rw [product_eq, Multilinear.productCoefficients_eval]

theorem product_booleanSum (left right : Fin (2 ^ n) → F) :
    (Multilinear.productCoefficients n (ofLowStorage (toLowStorage left))
      (ofLowStorage (toLowStorage right))).booleanSum =
    (Multilinear.productCoefficients n (Multilinear.ofVector left)
      (Multilinear.ofVector right)).booleanSum := by
  rw [product_eq]

end Zkc.Polynomial.Layout
