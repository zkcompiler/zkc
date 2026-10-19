import Zkc.Protocols.Sumcheck.Multilinear
import Mathlib.Algebra.Field.ZMod

/-! Kernel-checked regressions for the independent multilinear model.
These witnesses test algebraic distinctions, not native or security claims.
-/

set_option autoImplicit false

namespace MultilinearSumcheckTests

open Zkc.Polynomial Zkc.Polynomial.Multilinear
open Zkc.Protocols.Sumcheck.Multilinear

def table : Table ℚ 2 := ofVector ![0, 1, 2, 3]

-- Endpoint values, not coefficients; order matters away from the midpoint.
example : evaluate ((2, 5) : ℚ × ℚ) 3 = 11 := by decide +kernel
example : evaluate ((2, 5) : ℚ × ℚ) 3 ≠ 2 + 5 * 3 := by decide +kernel
example : evaluate ((2, 5) : ℚ × ℚ) 3 ≠ evaluate (5, 2) 3 := by decide +kernel
example : honestMessage table = (1, 5) := by decide +kernel
example : honestMessage (fixFirst table 2) = (4, 5) := by decide +kernel
example : honestMessage (fixFirst table 7) = (14, 15) := by decide +kernel

-- The flat vector denotes 2*x₀+x₁: the first coordinate is MSB-first.
example : extension 2 table ![2, 3] = 7 := by decide +kernel
example : extension 2 table ![3, 2] = 8 := by decide +kernel
example : fixPrefix (n := 0) 2 table ![2, 3] Fin.elim0 = 7 := by decide +kernel
example : fixPrefix (n := 0) 2 table ![7, 11] Fin.elim0 = 25 := by decide +kernel

-- A partial claim is a remaining Boolean sum, not evaluation at a padded point.
example : ResidualClaim (n := 1) 1 table ![2] 9 := by unfold ResidualClaim; decide +kernel
example : extension 2 table ![2, 0] ≠ 9 := by decide +kernel
example : ResidualClaim (n := 2) 0 table Fin.elim0 6 := by unfold ResidualClaim; decide +kernel
example : check [0, 1, 2, 3] (Fin.elim0 : Fin 0 → ℚ) 6 = false := by decide +kernel

-- Marginalizing the suffix preserves the ordered residual truth in the core.
example : extension 1 (sumRemaining 1 1 table) ![2] = 9 := by
  rw [extension_sumRemaining]
  decide +kernel

example : booleanSum (sumRemaining 2 0 table) = 6 := by
  rw [booleanSum_sumRemaining]
  decide +kernel

-- Faithful round messages do not identify independent challenge deliveries.
example : evaluate (honestMessage table) 2 = 9 := by decide +kernel
example : booleanSum (fixFirst table 7) = 29 := by decide +kernel
example : booleanSum (fixFirst table 7) ≠ evaluate (honestMessage table) 2 := by decide +kernel
example : boundary ((0, 6) : ℚ × ℚ) = booleanSum table := by decide +kernel
example : booleanSum (fixFirst table 2) ≠ evaluate ((0, 6) : ℚ × ℚ) 2 := by decide +kernel
example : check [0, 1, 2, 3] (![2, 3] : Fin 2 → ℚ) 7 = true := by decide +kernel
example : check [0, 1, 2, 3] (![7, 11] : Fin 2 → ℚ) 7 = false := by decide +kernel
example : check [0, 1, 2, 4] (![2, 3] : Fin 2 → ℚ) 7 = false := by decide +kernel

-- Exact shape: neither padding nor truncation; zero rounds require one entry.
example : (ofList? 2 ([0, 1, 2, 3] : List ℚ)).isSome = true := by decide +kernel
example : (ofList? 2 ([0, 1, 2] : List ℚ)).isNone = true := by decide +kernel
example : (ofList? 2 ([0, 1, 2, 3, 4] : List ℚ)).isNone = true := by decide +kernel
example : check [7] (Fin.elim0 : Fin 0 → ℚ) 7 = true := by decide +kernel
example : check [7] (Fin.elim0 : Fin 0 → ℚ) 8 = false := by decide +kernel
example : check [] (Fin.elim0 : Fin 0 → ℚ) 0 = false := by decide +kernel
example : check [7, 8] (Fin.elim0 : Fin 0 → ℚ) 7 = false := by decide +kernel

-- Positive, arbitrary-dimensional clients ensure the contracts are inhabitable.
example {F : Type} [Ring F] {n : Nat} (values : Table F (n + 1)) (r : F) :
    boundary (honestMessage values) = booleanSum values ∧
      booleanSum (fixFirst values r) = evaluate (honestMessage values) r :=
  ⟨boundary_honestMessage values, honest_update values _ rfl r r rfl⟩

example {F : Type} [CommRing F] {n k : Nat} (values : Table F (n + k)) (point : Fin k → F) :
    ResidualClaim k values point (booleanSum (fixPrefix k values point)) := rfl

example {F : Type} [CommRing F] [DecidableEq F] {n : Nat}
    (values : Fin (2 ^ n) → F) (point : Fin n → F) :
    check (List.ofFn values) point (extension n (ofVector values) point) = true := by
  apply (check_eq_true_iff _ _ _).mpr
  exact ⟨ofVector values, ofList?_ofFn values, rfl⟩

example {F : Type} [CommRing F] [DecidableEq F] {k : Nat}
    (values : Fin (2 ^ (0 + k)) → F) (point : Fin k → F) :
    check (List.ofFn values) (Quadratic.point k point Fin.elim0)
      (booleanSum (fixPrefix (n := 0) k (ofVector values) point)) = true :=
  check_of_residual _ (ofVector values) (ofVector values) point point _
    (ofList?_ofFn values) rfl rfl rfl

-- If the challenge is already known, this pair forges claim 1 for the zero table.
-- This is an algebraic witness, not a probability or interactive soundness theorem.
theorem earlyChallenge_pair {F : Type} [Field F] (r : F) (denominator : 2 * r - 1 ≠ 0) :
    boundary (r / (2 * r - 1), (r - 1) / (2 * r - 1)) = 1 ∧
      evaluate (r / (2 * r - 1), (r - 1) / (2 * r - 1)) r = 0 := by
  constructor
  · dsimp [boundary]
    rw [← add_div, div_eq_one_iff_eq denominator]
    ring
  · dsimp [evaluate]
    ring

local instance : Fact (Nat.Prime 97) := ⟨by decide⟩

theorem earlyChallenge_denominator (r : ZMod 97) : 2 * r - 1 ≠ 0 ↔ r ≠ 49 := by
  constructor
  · intro nonzero same
    subst r
    exact nonzero (by decide)
  · intro different zero
    apply different
    apply mul_left_cancel₀ (show (2 : ZMod 97) ≠ 0 by decide)
    calc
      2 * r = 1 := sub_eq_zero.mp zero
      _ = 2 * 49 := by decide +kernel

theorem earlyChallenge_F97 (r : ZMod 97) (different : r ≠ 49) :
    boundary (r / (2 * r - 1), (r - 1) / (2 * r - 1)) = 1 ∧
      evaluate (r / (2 * r - 1), (r - 1) / (2 * r - 1)) r = 0 :=
  earlyChallenge_pair r ((earlyChallenge_denominator r).mpr different)

theorem earlyChallenge_exception (message : Message (ZMod 97)) (valid : boundary message = 1) :
    evaluate message 49 = 49 := by
  unfold evaluate
  rw [show (1 - 49 : ZMod 97) = 49 by decide, ← mul_add]
  change 49 * boundary message = 49
  rw [valid, mul_one]

example : booleanSum (fun _ : Fin 1 → Bool => (0 : ZMod 97)) ≠ 1 := by decide +kernel
example : (49 : ZMod 97) ≠ 0 := by decide +kernel

end MultilinearSumcheckTests
