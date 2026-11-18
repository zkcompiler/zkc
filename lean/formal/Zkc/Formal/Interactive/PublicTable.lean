module

public import Zkc.Formal.Interactive.Multilinear

@[expose] public section
namespace Zkc.Formal.Interactive.Sumcheck.Cube
variable {F : Type}

def flatten : (n : Nat) → Cube F n → List F
  | 0, v => [v]
  | n+1, table => flatten n table.1 ++ flatten n table.2

theorem flatten_length (n : Nat) (table : Cube F n) : (flatten n table).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [flatten,List.length_append,ih,Nat.pow_succ,Nat.mul_two]

/-- Construct a Boolean-cube representation of every flat input of the declared length. -/
theorem exists_flatten_of_length {F : Type} (n : Nat) (xs : List F) (size : xs.length = 2^n) :
    ∃ x : Cube F n, Cube.flatten n x = xs := by
  induction n generalizing xs with
  | zero =>
    cases xs with
    | nil => contradiction
    | cons a tail =>
      have empty : tail.length = 0 := Nat.succ.inj size
      exact ⟨a,by rw [List.eq_nil_of_length_eq_zero empty]; rfl⟩
  | succ n ih =>
    rw [Nat.pow_succ,Nat.mul_two] at size
    obtain ⟨a,ha⟩ := ih (xs.take (2^n)) (by simp [size])
    obtain ⟨b,hb⟩ := ih (xs.drop (2^n)) (by simp [size])
    exact ⟨(a,b),by rw [Cube.flatten,ha,hb,List.take_append_drop]⟩

theorem sum_flatten {F : Type} [Lean.Grind.Field F] (n : Nat) (x : Cube F n) :
    (Cube.flatten n x).sum = Cube.sum n x := by
  induction n with
  | zero => simp [Cube.flatten,Cube.sum,Lean.Grind.AddCommMonoid.add_zero]
  | succ n ih =>
    have append (as bs : List F) : (as ++ bs).sum = as.sum + bs.sum := by
      induction as with
      | nil => simp [Lean.Grind.AddCommMonoid.zero_add]
      | cons a as h => simp [h,Lean.Grind.Semiring.add_assoc]
    simp only [Cube.flatten,Cube.sum,append,ih]

variable [Lean.Grind.Field F]

/-- The three rows in the source table restriction apply subtraction, scaling and addition
at each position, with the first variable indexing the two adjacent halves. -/
theorem flatten_interpolate (r : F) (n : Nat) (lo hi : Cube F n) :
    List.zipWith (·+·) (flatten n lo) ((List.zipWith (·-·) (flatten n hi) (flatten n lo)).map (·*r)) =
    flatten n (interpolate r n lo hi) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [flatten,interpolate,List.zipWith_append (show (flatten n hi.1).length = (flatten n lo.1).length by simp [flatten_length]),
      List.map_append]
    rw [List.zipWith_append (show (flatten n lo.1).length =
      ((List.zipWith (·-·) (flatten n hi.1) (flatten n lo.1)).map (·*r)).length by simp [flatten_length])]
    rw [ih,ih]

#print axioms flatten_interpolate
end Zkc.Formal.Interactive.Sumcheck.Cube
