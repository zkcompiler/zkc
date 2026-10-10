import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Executable finite sequence arithmetic. Shape checks precede every zip,
index and allocation; coefficients are ascending and zero is the empty list.
These helpers require ring arithmetic, not a primality assumption. -/

set_option autoImplicit false

namespace Zkc.Algebra.FiniteVectors

abbrev Result := Except String

def limit : Nat := 1048576

def check (condition : Bool) (code : String) : Result Unit :=
  if condition then .ok () else .error code

def bounded {α : Type} (xs : List α) : Result Unit :=
  check (xs.length ≤ limit) "vector-limit"

def zipExact {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) : Result (List γ) := do
  bounded xs
  bounded ys
  check (xs.length == ys.length) "vector-shape"
  return (xs.zip ys).map fun (x, y) => f x y

def split {α : Type} (xs : List α) : Result (List α × List α) := do
  bounded xs
  check (!xs.isEmpty && xs.length % 2 == 0) "vector-split-shape"
  return (xs.take (xs.length / 2), xs.drop (xs.length / 2))

def concat {α : Type} (xs ys : List α) : Result (List α) := do
  check (xs.length + ys.length ≤ limit) "vector-limit"
  return xs ++ ys

def gather {α : Type} (xs : List α) (indices : List Nat) : Result (List α) := do
  bounded xs
  bounded indices
  check (indices.all (· < xs.length)) "vector-index"
  indices.mapM fun i => match xs[i]? with
    | some x => .ok x | none => .error "vector-index"

/-- Exact contiguous slice. Subtraction-based bounds avoid machine-addition
wraparound in consumers; Lean itself uses unbounded naturals. -/
def slice {α : Type} (xs : List α) (start count : Nat) : Result (List α) :=
  if xs.length ≤ limit then
    if start ≤ xs.length ∧ count ≤ xs.length - start then .ok ((xs.drop start).take count)
    else .error "vector-slice-bounds"
  else .error "vector-limit"

/-- Every successful slice retains the exact source order and requested length. -/
theorem slice_eq {α : Type} (xs ys : List α) (start count : Nat)
    (success : slice xs start count = .ok ys) :
    start ≤ xs.length ∧ count ≤ xs.length - start ∧ ys = (xs.drop start).take count := by
  unfold slice at success
  split at success
  · split at success
    · cases success
      exact ⟨(by omega), (by omega), rfl⟩
    · contradiction
  · contradiction

theorem slice_length {α : Type} (xs ys : List α) (start count : Nat)
    (success : slice xs start count = .ok ys) : ys.length = count := by
  obtain ⟨_, bound, rfl⟩ := slice_eq xs ys start count success
  simp [List.length_take, List.length_drop, Nat.min_eq_left bound]

theorem slice_coordinate {α : Type} (xs ys : List α) (start count i : Nat)
    (success : slice xs start count = .ok ys) (inside : i < count) :
    ys[i]? = xs[start + i]? := by
  obtain ⟨_, _, rfl⟩ := slice_eq xs ys start count success
  simp [List.getElem?_drop, inside]

variable {F : Type} [CommRing F]

/-- One index per input; repeated indices contribute additively. All shape
and index checks precede output allocation. Unlike the native indexed update,
this reference computes each output as the sum over its inverse image. -/
def scatterSum (xs : List F) (outputLength : Nat) (indices : List Nat) : Result (List F) := do
  bounded xs
  check (xs.length == indices.length) "vector-shape"
  check (indices.all (· < outputLength)) "vector-index"
  check (outputLength ≤ limit) "vector-limit"
  let contributions := xs.zip indices
  return (List.range outputLength).map fun row =>
    (contributions.filterMap fun (value, index) => if index == row then some value else none).sum

def powers (x : F) (n : Nat) : Result (List F) := do
  check (n ≤ limit) "vector-limit"
  return ((List.range n).foldl (fun (acc : List F × F) _ => (acc.2 :: acc.1, acc.2 * x)) ([], 1)).1.reverse

def dot (xs ys : List F) : Result F := do
  return (← zipExact (· * ·) xs ys).sum

def kronecker (xs ys : List F) : Result (List F) := do
  bounded xs
  bounded ys
  check (xs.length * ys.length ≤ limit) "vector-limit"
  return xs.flatMap fun x => ys.map (x * ·)

/-- Row-major matrix. Transpose changes the contracted axis, not storage order.
Zero dimensions are supported, subject to exact matrix/vector shapes. -/
def matvec (rows columns : Nat) (transpose : Bool) (matrix vector : List F) : Result (List F) := do
  check (rows ≤ limit && columns ≤ limit && rows * columns ≤ limit) "vector-limit"
  bounded matrix
  bounded vector
  check (matrix.length == rows * columns && vector.length == (if transpose then rows else columns)) "matrix-shape"
  let m := matrix.toArray
  let v := vector.toArray
  return (List.range (if transpose then columns else rows)).map fun i =>
    ((List.range v.size).map fun j =>
      (m[if transpose then j * columns + i else i * columns + j]?.getD 0) * (v[j]?.getD 0)).sum

def equalityWeights (point : List F) : List F :=
  point.foldl (fun weights r => weights.flatMap fun w => [w * (1 - r), w * r]) [1]

/-- Horner's recurrence for ascending coefficients. -/
def evaluate (coefficients : List F) (x : F) : F :=
  coefficients.foldr (fun a rest => a + x * rest) 0

def boundary (coefficients : List F) : F := evaluate coefficients 0 + evaluate coefficients 1

def normalize [BEq F] (coefficients : List F) : List F :=
  (coefficients.reverse.dropWhile (· == 0)).reverse

def degreeCheck (coefficients : List F) (maximum : Nat) : Bool :=
  coefficients.isEmpty || coefficients.length - 1 ≤ maximum

/-- Extended Euclid in Mathlib is executable. Check its result explicitly;
no Prime instance or new axiom is needed, even for a composite modulus. -/
def inverse {n : Nat} [NeZero n] (x : ZMod n) : Result (ZMod n) :=
  if x == 0 then .error "inverse-zero"
  else if x * x⁻¹ == 1 then .ok x⁻¹ else .error "inverse-nonunit"

theorem inverse_correct {n : Nat} [NeZero n] (x y : ZMod n)
    (h : inverse x = .ok y) : x * y = 1 := by
  unfold inverse at h
  split at h
  · contradiction
  · split at h
    · simp_all
    · contradiction

end Zkc.Algebra.FiniteVectors
