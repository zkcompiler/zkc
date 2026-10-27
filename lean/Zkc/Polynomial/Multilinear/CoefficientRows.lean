module

public import Zkc.Polynomial.Multilinear.Line
public import Zkc.Polynomial.Multilinear.ListRestriction

@[expose] public section

/-! Fixed-width, constant-first coefficient rows. Packing and shifting are
structural list operations; their laws hold over every commutative ring. -/

set_option autoImplicit false

namespace Zkc.Polynomial.Multilinear.CoefficientRows
open _root_.Polynomial
variable {F : Type} [CommRing F]

/-- Exactly `count` coefficients, including trailing zero coefficients. -/
noncomputable def row (count : Nat) (p : F[X]) : List F :=
  (List.range count).map p.coeff

noncomputable def pack (count : Nat) (ps : List F[X]) : List F :=
  ps.flatMap (row count)

@[simp] theorem row_length (count : Nat) (p : F[X]) : (row count p).length = count := by
  simp [row]

@[simp] theorem row_get (count : Nat) (p : F[X]) (i : Nat) (hi : i < count) :
    (row count p)[i]'(by simp [hi]) = p.coeff i := by simp [row]

@[simp] theorem pack_length (count : Nat) (ps : List F[X]) :
    (pack count ps).length = ps.length * count := by
  induction ps with
  | nil => simp [pack]
  | cons p ps ih =>
    simp only [pack, List.flatMap_cons, List.length_append, row_length, List.length_cons] at *
    rw [ih, Nat.succ_mul, Nat.add_comm]

@[simp] theorem pack_append (count : Nat) (ps qs : List F[X]) :
    pack count (ps ++ qs) = pack count ps ++ pack count qs := by simp [pack]

@[simp] theorem pack_cons (count : Nat) (p : F[X]) (ps : List F[X]) :
    pack count (p :: ps) = row count p ++ pack count ps := rfl

@[simp] theorem pack_nil (count : Nat) : pack (F := F) count [] = [] := rfl

theorem row_constant (width : Nat) (value : F) :
    row (width + 1) (C value) = value :: List.replicate width 0 := by
  apply List.ext_getElem
  · simp
  · intro i left right
    cases i <;> simp [row]

theorem pack_constants (width : Nat) (values : List F) :
    pack (width + 1) (values.map C) =
      values.flatMap (fun value => value :: List.replicate width 0) := by
  simp [pack, List.flatMap_map, row_constant]

theorem pack_take (count k : Nat) (ps : List F[X]) :
    (pack count ps).take (k * count) = pack count (ps.take k) := by
  induction ps generalizing k with
  | nil => simp
  | cons p ps ih =>
    cases k with
    | zero => simp
    | succ k => simp [Nat.succ_mul, List.take_append, ih]

theorem pack_drop (count k : Nat) (ps : List F[X]) :
    (pack count ps).drop (k * count) = pack count (ps.drop k) := by
  induction ps generalizing k with
  | nil => simp
  | cons p ps ih =>
    cases k with
    | zero => simp
    | succ k => simp [Nat.succ_mul, List.drop_append, ih]

/-- The exact reset-and-shift scan used by row-major coefficient producers. -/
def shiftAux (count offset : Nat) (previous : F) : List F → List F
  | [] => []
  | value :: rest => (if offset % count = 0 then 0 else previous) ::
      shiftAux count (offset + 1) value rest

@[simp] theorem shiftAux_length (count offset : Nat) (previous : F) (xs : List F) :
    (shiftAux count offset previous xs).length = xs.length := by
  induction xs generalizing offset previous with
  | nil => rfl
  | cons x xs ih => simp [shiftAux, ih]

theorem shiftAux_append (count offset : Nat) (previous : F) (xs ys : List F) :
    shiftAux count offset previous (xs ++ ys) =
      shiftAux count offset previous xs ++
        shiftAux count (offset + xs.length) (xs.getLastD previous) ys := by
  induction xs generalizing offset previous with
  | nil => simp [shiftAux]
  | cons x xs ih =>
    simp only [List.cons_append, shiftAux, ih, List.length_cons]
    rw [show offset + 1 + xs.length = offset + (xs.length + 1) by omega]
    cases xs <;> rfl

theorem shiftAux_get (count offset : Nat) (previous : F) (xs : List F)
    (i : Nat) (hi : i < xs.length) :
    (shiftAux count offset previous xs)[i]'(by simpa using hi) =
      if (offset + i) % count = 0 then 0
      else if i = 0 then previous else xs[i - 1]'(by omega) := by
  induction xs generalizing offset previous i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [shiftAux]
    | succ i =>
      rw [show (shiftAux count offset previous (x :: xs))[i + 1]'_ =
        (shiftAux count (offset + 1) x xs)[i]'_ from rfl,
        ih (offset + 1) x i (by simpa using hi)]
      cases i <;> simp [Nat.add_comm, Nat.add_left_comm]

/-- Resetting each row makes the scan multiplication by `X`, with fixed-width
readout. This coefficient identity itself needs no degree bound. -/
theorem shiftAux_row (count offset : Nat) (previous : F) (p : F[X])
    (_positive : 0 < count) (boundary : offset % count = 0) :
    shiftAux count offset previous (row count p) = row count (X * p) := by
  apply List.ext_getElem
  · simp
  · intro i left right
    have hi : i < count := by simpa using right
    rw [shiftAux_get count offset previous _ i (by simpa using hi)]
    have rem : (offset + i) % count = i := by
      rw [Nat.add_mod, boundary, Nat.zero_add, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    rw [rem]
    cases i with
    | zero => simp [row]
    | succ i => simp [row, coeff_X_mul]

theorem shiftAux_pack (count offset : Nat) (previous : F) (ps : List F[X])
    (positive : 0 < count) (boundary : offset % count = 0) :
    shiftAux count offset previous (pack count ps) = pack count (ps.map (X * ·)) := by
  induction ps generalizing offset previous with
  | nil => rfl
  | cons p ps ih =>
    rw [pack_cons, shiftAux_append, shiftAux_row count offset previous p positive boundary]
    simpa only [row_length, List.map_cons, pack_cons, List.append_cancel_left_eq] using
      (ih (offset + count) ((row count p).getLastD previous) (by simpa [Nat.add_mod] using boundary))

/-- Coefficientwise interpolation commutes with fixed-width encoding. -/
theorem row_interpolate (count : Nat) (p q : F[X]) (r : F) :
    List.zipWith (fun a b => a + (b - a) * r) (row count p) (row count q) =
      row count (p + (q - p) * C r) := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp [row, coeff_add, coeff_mul_C, coeff_sub]

theorem row_slope (count : Nat) (p q : F[X]) (r : F) :
    List.zipWith (fun a b => (b - a) * r) (row count p) (row count q) =
      row count ((q - p) * C r) := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp [row, coeff_mul_C, coeff_sub]

theorem row_add (count : Nat) (p q : F[X]) :
    List.zipWith (· + ·) (row count p) (row count q) = row count (p + q) := by
  apply List.ext_getElem
  · simp
  · intro i left right
    simp [row, coeff_add]

/-- Equal row widths prevent a checked zip from crossing row boundaries. -/
theorem pack_zipWith (count : Nat) (ps qs : List F[X])
    (same : qs.length = ps.length) (f : F → F → F) (g : F[X] → F[X] → F[X])
    (rows : ∀ p q, List.zipWith f (row count p) (row count q) = row count (g p q)) :
    List.zipWith f (pack count ps) (pack count qs) =
      pack count (List.zipWith g ps qs) := by
  induction ps generalizing qs with
  | nil => cases qs <;> simp_all
  | cons p ps ih =>
    cases qs with
    | nil => simp at same
    | cons q qs =>
      rw [pack_cons, pack_cons, List.zipWith_append (by simp), rows, ih qs (by simpa using same)]
      rfl

/-- Reading a list as a polynomial has exactly the advertised coefficients. -/
theorem coefficientPolynomial_coeff (xs : List F) (i : Nat) :
    (coefficientPolynomial xs).coeff i = xs[i]?.getD 0 := by
  induction xs generalizing i with
  | nil => simp [coefficientPolynomial]
  | cons x xs ih =>
    cases i <;> simp [coefficientPolynomial, coeff_X_mul, ih]

/-- Omitted coefficients are justified by an explicit degree bound. -/
theorem coefficientPolynomial_row (count : Nat) (p : F[X])
    (fits : p.natDegree < count) : coefficientPolynomial (row count p) = p := by
  ext i
  rw [coefficientPolynomial_coeff]
  by_cases hi : i < count
  · simp [row, hi]
  · rw [List.getElem?_eq_none (by simpa using (show count ≤ i by omega)), Option.getD_none]
    exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

end Zkc.Polynomial.Multilinear.CoefficientRows
