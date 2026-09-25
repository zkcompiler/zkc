import Examples.OpeningReduction.Polynomial

/-! A concrete two-point reduction using a public equality-weight table.

This is the algebraic identity consumed by Sumcheck, not an assertion that a
random linear combination certifies either original claim without freshness.
The public weight is a derived object; it need not acquire a PCS commitment.
-/

set_option autoImplicit false

namespace Examples.OpeningReduction.MultiplePoints
open Zkc.Polynomial

variable {F : Type} [CommRing F]

def equalityTable : (n : Nat) → (Fin n → F) → Table F n
  | 0, _ => .scalar 1
  | n + 1, point =>
      let tail := equalityTable n (point ∘ Fin.succ)
      .node (tail.scale (1 - point 0)) (tail.scale (point 0))

theorem reproduces (n : Nat) (table : Table F n) (point : Fin n → F) :
    cubeSum n (fun x => (equalityTable n point).eval x * table.eval x) = table.eval point := by
  induction n with
  | zero => cases table; simp [cubeSum, equalityTable, Table.eval]
  | succ n ih =>
      cases table with
      | node lo hi =>
          simp only [cubeSum, equalityTable, Table.eval, Fin.cons_zero, Table.eval_scale,
            zero_mul, sub_zero, one_mul, sub_self, zero_add, add_zero]
          change
            cubeSum n (fun x => ((1 - point 0) * (equalityTable n (point ∘ Fin.succ)).eval x) * lo.eval x) +
            cubeSum n (fun x => (point 0 * (equalityTable n (point ∘ Fin.succ)).eval x) * hi.eval x) = _
          simp only [mul_assoc, cubeSum_scale, ih]

def weight {n : Nat} (alpha : F) (u v : Fin n → F) : Table F n :=
  (equalityTable n u).add ((equalityTable n v).scale alpha)

theorem two_points {n : Nat} (table : Table F n) (alpha : F) (u v : Fin n → F) :
    cubeSum n (fun x => (weight alpha u v).eval x * table.eval x) =
      table.eval u + alpha * table.eval v := by
  simp only [weight, Table.eval_add, Table.eval_scale, add_mul, mul_assoc,
    cubeSum_add, cubeSum_scale, reproduces]

def one : (n : Nat) → Table F n
  | 0 => .scalar 1
  | n + 1 => .node (one n) (one n)

theorem one_eval (n : Nat) (point : Fin n → F) : (one n : Table F n).eval point = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [one, Table.eval, ih]; ring

/-- Instantiates the same three-factor engine; its generic bound is conservative
because this particular product has per-coordinate degree at most two. -/
def reduction {n : Nat} (table : Table F n) (alpha : F) (u v : Fin n → F) : Factors F n :=
  ⟨weight alpha u v, table, one n⟩

theorem reduction_sum {n : Nat} (table : Table F n) (alpha : F) (u v : Fin n → F) :
    (reduction table alpha u v).booleanSum = table.eval u + alpha * table.eval v := by
  change cubeSum n (fun x => (weight alpha u v).eval x * table.eval x * (one n).eval x) = _
  simpa only [one_eval, mul_one] using two_points table alpha u v

end Examples.OpeningReduction.MultiplePoints
