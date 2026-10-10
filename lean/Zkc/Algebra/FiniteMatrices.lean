import Zkc.Algebra.FiniteVectors

/-! Executable matrix reference over an ordinary commutative ring. Sparse COO
is the input carrier, not a new mathematical type of scalar or a backend.
Each output coordinate is computed independently as a finite sum; native code
instead accumulates into an output array. No native correspondence theorem is
asserted by these executable definitions. -/
set_option autoImplicit false
namespace Zkc.Algebra.FiniteMatrices
open FiniteVectors (Result check)

def dimensionLimit : Nat := 65536
def nonzeroLimit : Nat := 1048576

structure Entry (F : Type) where
  row : Nat
  column : Nat
  coefficient : F
  deriving BEq, Repr

structure Matrix (F : Type) where
  rows : Nat
  columns : Nat
  entries : List (Entry F)
  deriving BEq, Repr

def Matrix.valid {F : Type} [Zero F] [BEq F] (m : Matrix F) : Bool :=
  m.rows ≤ dimensionLimit && m.columns ≤ dimensionLimit &&
  m.entries.length ≤ nonzeroLimit && m.entries.length ≤ m.rows * m.columns &&
  m.entries.all (fun e => e.row < m.rows && e.column < m.columns && e.coefficient != 0) &&
  (m.entries.zip m.entries.tail).all (fun (a,b) =>
    a.row < b.row || (a.row == b.row && a.column < b.column))

variable {F : Type} [CommRing F] [BEq F]

/-- Exact shape, including zero dimensions. No implicit zero padding. -/
def mulVector (m : Matrix F) (xs : List F) (transpose : Bool := false) : Result (List F) := do
  check m.valid "matrix-canonical"
  let input := if transpose then m.rows else m.columns
  let output := if transpose then m.columns else m.rows
  check (xs.length == input) "matrix-shape"
  let x := xs.toArray
  return (List.range output).map fun i =>
    (m.entries.filterMap fun e =>
      if (if transpose then e.column else e.row) == i then
        some (e.coefficient * (x[if transpose then e.row else e.column]?).getD 0)
      else none).sum

/-- Reference contraction via the row product and ordinary dot product. -/
def bilinear (m : Matrix F) (rowVector columnVector : List F) : Result F := do
  check (rowVector.length == m.rows) "matrix-shape"
  FiniteVectors.dot rowVector (← mulVector m columnVector)

end Zkc.Algebra.FiniteMatrices
