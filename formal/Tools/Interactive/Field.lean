import Tools.Interactive.Syntax
import Zkc.Polynomial.LinearInterpolation
import Zkc.Protocols.AlgebraicRounds.Scalar
import Mathlib.Data.ZMod.Basic

/-! Executable modular arithmetic and high-half-first table kernels. Polynomial
identities below hold over every commutative ring, without a primality axiom. -/

set_option autoImplicit false

namespace Tools.Interactive.Math

abbrev Fr := ZMod fieldModulus

instance : NeZero fieldModulus := ⟨by decide⟩

structure Round (F : Type) where
  constant : F
  linear : F
  quadratic : F
  deriving BEq, Repr

variable {F : Type} [CommRing F]

def Round.at (g : Round F) (r : F) : F :=
  Zkc.Protocols.AlgebraicRounds.Scalar.value ⟨g.constant, g.linear, g.quadratic, r⟩

def Round.boundary (g : Round F) : F :=
  Zkc.Protocols.AlgebraicRounds.Scalar.boundary ⟨g.constant, g.linear, g.quadratic, 0⟩

def interpolate (lo hi r : F) : F := (1 - r) * lo + r * hi

theorem interpolate_foldAt {n : Nat} (lo hi : Fin n → F) (r : F) (i : Fin n) :
    interpolate (lo i) (hi i) r = Zkc.Polynomial.LinearInterpolation.foldAt r lo hi i := rfl

def pairRound (x y : F × F) : Round F :=
  ⟨x.1 * y.1, x.1 * (y.2 - y.1) + (x.2 - x.1) * y.1,
    (x.2 - x.1) * (y.2 - y.1)⟩

theorem pairRound_at (x y : F × F) (r : F) :
    (pairRound x y).at r = interpolate x.1 x.2 r * interpolate y.1 y.2 r := by
  simp only [pairRound, Round.at, Zkc.Protocols.AlgebraicRounds.Scalar.value, interpolate]
  ring

theorem round_boundary (g : Round F) : g.boundary = g.at 0 + g.at 1 := by
  simp only [Round.boundary, Round.at, Zkc.Protocols.AlgebraicRounds.Scalar.boundary,
    Zkc.Protocols.AlgebraicRounds.Scalar.value]
  ring

def addRound (g h : Round F) : Round F :=
  ⟨g.constant + h.constant, g.linear + h.linear, g.quadratic + h.quadratic⟩

def productCoefficients : List ((F × F) × (F × F)) → Round F
  | [] => ⟨0, 0, 0⟩
  | (x, y) :: rest => addRound (pairRound x y) (productCoefficients rest)

/-- Actual coefficient materialization agrees with the independent sum of
pairwise restricted products, for every challenge, not only Boolean endpoints. -/
theorem productCoefficients_at (pairs : List ((F × F) × (F × F))) (r : F) :
    (productCoefficients pairs).at r =
      (pairs.map fun (x, y) => interpolate x.1 x.2 r * interpolate y.1 y.2 r).sum := by
  induction pairs with
  | nil => simp [productCoefficients, Round.at, Zkc.Protocols.AlgebraicRounds.Scalar.value]
  | cons pair rest ih =>
      rcases pair with ⟨x, y⟩
      have addLaw (g h : Round F) : (addRound g h).at r = g.at r + h.at r := by
        simp only [addRound, Round.at, Zkc.Protocols.AlgebraicRounds.Scalar.value]
        ring
      simp only [productCoefficients, List.map_cons, List.sum_cons, addLaw, pairRound_at, ih]

theorem productCoefficients_boundary (pairs : List ((F × F) × (F × F))) :
    (productCoefficients pairs).boundary =
      (pairs.map fun (x, y) => x.1 * y.1).sum + (pairs.map fun (x, y) => x.2 * y.2).sum := by
  rw [round_boundary, productCoefficients_at, productCoefficients_at]
  simp [interpolate]

structure Table where
  rank : Nat
  cells : List Fr
  deriving BEq, Repr

def Table.admit (rank : Nat) (cells : List Fr) : Result Table := do
  ensure (rank ≤ limits.rank) "table-rank-limit"
  ensure (cells.length == 2 ^ rank) "table-shape"
  return ⟨rank, cells⟩

def Table.halves (table : Table) : List (Fr × Fr) :=
  (table.cells.take (table.cells.length / 2)).zip (table.cells.drop (table.cells.length / 2))

def Table.fold (table : Table) (r : Fr) : Result Table := do
  ensure (table.rank > 0) "fold-exhausted"
  Table.admit (table.rank - 1) (table.halves.map fun (lo, hi) => interpolate lo hi r)

def Table.evaluate (table : Table) (point : List Fr) : Result Fr := do
  ensure (point.length == table.rank) "point-arity"
  let reduced ← point.foldlM (fun table r => table.fold r) table
  match reduced.cells with
  | [value] => return value
  | _ => throw "table-shape"

def productSum (left right : Table) : Result Fr := do
  ensure (left.rank == right.rank && left.cells.length == right.cells.length) "product-shape"
  return ((left.cells.zip right.cells).map fun (x, y) => x * y).sum

def productRound (left right : Table) : Result (Round Fr) := do
  ensure (left.rank == right.rank && left.rank > 0 && left.cells.length == right.cells.length) "round-shape"
  return productCoefficients (left.halves.zip right.halves)

end Tools.Interactive.Math
