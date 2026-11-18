module

public import Init.Data.Nat.Lemmas

@[expose] public section

namespace Zkc.Formal.Interactive

/-- A representative of a nonnegative rational. Denominators are strictly positive. -/
structure Mass.Fraction where
  num : Nat
  den : Nat
  positive : 0 < den

namespace Mass.Fraction

def Equivalent (a b : Fraction) : Prop := a.num * b.den = b.num * a.den

def Below (a b : Fraction) : Prop := a.num * b.den ≤ b.num * a.den

theorem below_trans {a b c : Fraction} (hab : Below a b) (hbc : Below b c) : Below a c := by
  apply Nat.le_of_mul_le_mul_right (c := b.den) _ b.positive
  calc
    a.num * c.den * b.den = a.num * b.den * c.den := by ac_rfl
    _ ≤ b.num * a.den * c.den := Nat.mul_le_mul_right _ hab
    _ = b.num * c.den * a.den := by ac_rfl
    _ ≤ c.num * b.den * a.den := Nat.mul_le_mul_right _ hbc
    _ = c.num * a.den * b.den := by ac_rfl

instance setoid : Setoid Fraction where
  r := Equivalent
  iseqv := ⟨fun _ => rfl, Eq.symm, fun hab hbc =>
    Nat.le_antisymm (below_trans (Nat.le_of_eq hab) (Nat.le_of_eq hbc))
      (below_trans (Nat.le_of_eq hbc.symm) (Nat.le_of_eq hab.symm))⟩

instance (a b : Fraction) : Decidable (a ≈ b) :=
  inferInstanceAs (Decidable (a.num * b.den = b.num * a.den))

def ofNat (n : Nat) : Fraction := ⟨n, 1, Nat.zero_lt_one⟩

def add (a b : Fraction) : Fraction :=
  ⟨a.num * b.den + b.num * a.den, a.den * b.den, Nat.mul_pos a.positive b.positive⟩

def mul (a b : Fraction) : Fraction :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.positive b.positive⟩

theorem add_congr {a b c d : Fraction} (hac : Equivalent a c) (hbd : Equivalent b d) :
    Equivalent (add a b) (add c d) := by
  unfold Equivalent add
  dsimp only
  rw [Nat.add_mul, Nat.add_mul]
  congr 1
  · calc
      _ = (a.num * c.den) * (b.den * d.den) := by ac_rfl
      _ = (c.num * a.den) * (b.den * d.den) := congrArg (· * _) hac
      _ = _ := by ac_rfl
  · calc
      _ = (b.num * d.den) * (a.den * c.den) := by ac_rfl
      _ = (d.num * b.den) * (a.den * c.den) := congrArg (· * _) hbd
      _ = _ := by ac_rfl

theorem mul_congr {a b c d : Fraction} (hac : Equivalent a c) (hbd : Equivalent b d) :
    Equivalent (mul a b) (mul c d) := by
  calc
    _ = (a.num * c.den) * (b.num * d.den) := by unfold mul; dsimp only; ac_rfl
    _ = (c.num * a.den) * (d.num * b.den) := congr (congrArg Nat.mul hac) hbd
    _ = _ := by unfold mul; dsimp only; ac_rfl

def inv (a : Fraction) : Fraction :=
  if h : a.num = 0 then ofNat 0 else ⟨a.den, a.num, Nat.pos_of_ne_zero h⟩

theorem inv_congr {a b : Fraction} (h : Equivalent a b) : Equivalent (inv a) (inv b) := by
  have sameZero : a.num = 0 ↔ b.num = 0 := by
    have eq : a.num * b.den = b.num * a.den := h
    constructor
    · intro ha
      exact (Nat.mul_eq_zero.mp (by simpa only [ha, Nat.zero_mul] using eq.symm)).resolve_right
        (Nat.ne_of_gt a.positive)
    · intro hb
      exact (Nat.mul_eq_zero.mp (by simpa only [hb, Nat.zero_mul] using eq)).resolve_right
        (Nat.ne_of_gt b.positive)
  by_cases ha : a.num = 0
  · rw [inv, dite_eq_left ha, inv, dite_eq_left (sameZero.mp ha)]
    rfl
  · simp only [inv, dite_eq_right ha, dite_eq_right (fun hb => ha (sameZero.mpr hb)), Equivalent]
    simpa only [Nat.mul_comm] using h.symm

theorem below_congr {a b c d : Fraction} (hac : Equivalent a c) (hbd : Equivalent b d) :
    Below a b ↔ Below c d :=
  ⟨fun h => below_trans (Nat.le_of_eq hac.symm) (below_trans h (Nat.le_of_eq hbd)),
   fun h => below_trans (Nat.le_of_eq hac) (below_trans h (Nat.le_of_eq hbd.symm))⟩

end Mass.Fraction

/-- Exact, unbounded nonnegative rational weights and payoffs, modulo cross multiplication. -/
def Mass := Quotient Mass.Fraction.setoid

namespace Mass

def ofFraction (a : Fraction) : Mass := Quotient.mk _ a

theorem ofFraction_eq {a b : Fraction} :
    ofFraction a = ofFraction b ↔ a.num * b.den = b.num * a.den :=
  ⟨Quotient.exact, fun h => Quotient.sound (s := Fraction.setoid) (a := a) (b := b) h⟩

instance : DecidableEq Mass := Quotient.decidableEq

def ofNat (n : Nat) : Mass := ofFraction (.ofNat n)

instance : NatCast Mass := ⟨ofNat⟩
instance (n : Nat) : OfNat Mass n := ⟨ofNat n⟩

instance : Add Mass := ⟨Quotient.lift₂ (fun a b => ofFraction (a.add b))
  fun _ _ _ _ h k => Quotient.sound (Fraction.add_congr h k)⟩

instance : Mul Mass := ⟨Quotient.lift₂ (fun a b => ofFraction (a.mul b))
  fun _ _ _ _ h k => Quotient.sound (Fraction.mul_congr h k)⟩

instance : Inv Mass := ⟨Quotient.lift (fun a => ofFraction a.inv)
  fun _ _ h => Quotient.sound (Fraction.inv_congr h)⟩

instance : Div Mass := ⟨fun a b => a * b⁻¹⟩

theorem div_def (a b : Mass) : a / b = a * b⁻¹ := rfl

/-- Division of natural casts represents the specified numerator and denominator exactly. -/
theorem natCast_div (n d : Nat) (hd : 0 < d) :
    (n : Mass) / (d : Mass) = ofFraction ⟨n, d, hd⟩ := by
  apply ofFraction_eq.mpr
  simp [Fraction.mul, Fraction.inv, Fraction.ofNat, Nat.ne_of_gt hd]

@[simp] theorem inv_zero : (0 : Mass)⁻¹ = 0 := rfl

instance : LE Mass := ⟨Quotient.lift₂ Fraction.Below
  fun _ _ _ _ h k => propext (Fraction.below_congr h k)⟩

instance (a b : Mass) : Decidable (a ≤ b) :=
  Quotient.recOnSubsingleton₂ (motive := fun x y : Mass => Decidable (x ≤ y)) a b
    fun x y => inferInstanceAs (Decidable (x.num * y.den ≤ y.num * x.den))

instance : LT Mass := ⟨fun a b => ¬ b ≤ a⟩
instance (a b : Mass) : Decidable (a < b) := inferInstanceAs (Decidable (¬ b ≤ a))

theorem ofFraction_le {a b : Fraction} :
    ofFraction a ≤ ofFraction b ↔ a.num * b.den ≤ b.num * a.den := Iff.rfl

theorem ofFraction_lt {a b : Fraction} :
    ofFraction a < ofFraction b ↔ a.num * b.den < b.num * a.den := Nat.not_le

@[simp] theorem le_refl {a : Mass} : a ≤ a :=
  Quotient.inductionOn a fun _ => Nat.le_refl _

theorem le_trans {a b c : Mass} : a ≤ b → b ≤ c → a ≤ c :=
  Quotient.inductionOn₃ a b c fun _ _ _ => Fraction.below_trans

theorem le_antisymm {a b : Mass} : a ≤ b → b ≤ a → a = b :=
  Quotient.inductionOn₂ a b fun _ _ hab hba => ofFraction_eq.mpr (Nat.le_antisymm hab hba)

theorem le_total (a b : Mass) : a ≤ b ∨ b ≤ a :=
  Quotient.inductionOn₂ a b fun _ _ => Nat.le_total _ _

theorem le_of_lt {a b : Mass} (h : a < b) : a ≤ b := (le_total a b).resolve_right h

theorem ne_of_gt {a b : Mass} (h : a < b) : b ≠ a :=
  fun e => h (e ▸ le_refl)

@[simp] theorem zero_le (a : Mass) : 0 ≤ a := by
  induction a using Quotient.inductionOn with
  | _ x =>
    change 0 * x.den ≤ x.num * 1
    rw [Nat.zero_mul]
    exact Nat.zero_le _

theorem eq_zero_of_not_pos {a : Mass} (h : ¬ 0 < a) : a = 0 := by
  by_cases ha : a ≤ 0
  · exact le_antisymm ha (zero_le _)
  · exact False.elim (h ha)

theorem ofFraction_pos {a : Fraction} : 0 < ofFraction a ↔ 0 < a.num := by
  change (¬ a.num * 1 ≤ 0 * a.den) ↔ 0 < a.num
  simp only [Nat.mul_one, Nat.zero_mul, Nat.not_le]

@[simp] theorem natCast_pos {n : Nat} : 0 < (n : Mass) ↔ 0 < n :=
  ofFraction_pos (a := .ofNat n)

@[simp] theorem natCast_nonneg {n : Nat} : 0 ≤ (n : Mass) := zero_le _

@[simp] theorem natCast_le_natCast {m n : Nat} : (m : Mass) ≤ (n : Mass) ↔ m ≤ n := by
  change m * 1 ≤ n * 1 ↔ _
  simp only [Nat.mul_one]

@[simp] theorem natCast_zero : ((0 : Nat) : Mass) = 0 := rfl

@[simp] theorem natCast_one : ((1 : Nat) : Mass) = 1 := rfl

theorem natCast_add (m n : Nat) : ((m + n : Nat) : Mass) = (m : Mass) + (n : Mass) := by
  apply ofFraction_eq.mpr
  simp [Fraction.ofNat, Fraction.add]

@[simp] theorem add_zero (a : Mass) : a + 0 = a := by
  induction a using Quotient.inductionOn with
  | _ x =>
    apply ofFraction_eq.mpr
    simp [Fraction.add, Fraction.ofNat]

theorem add_comm (a b : Mass) : a + b = b + a := by
  induction a, b using Quotient.inductionOn₂ with
  | _ x y =>
    apply ofFraction_eq.mpr
    simp only [Fraction.add, Nat.add_comm, Nat.mul_comm]

@[simp] theorem zero_add (a : Mass) : 0 + a = a := (add_comm ..).trans (add_zero a)

theorem add_assoc (a b c : Mass) : a + b + c = a + (b + c) := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ x y z =>
    apply ofFraction_eq.mpr
    simp only [Fraction.add, Nat.mul_add, Nat.add_assoc,
      Nat.mul_comm, Nat.mul_left_comm]

theorem add_left_comm (a b c : Mass) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

theorem mul_comm (a b : Mass) : a * b = b * a := by
  induction a, b using Quotient.inductionOn₂ with
  | _ x y =>
    apply ofFraction_eq.mpr
    simp only [Fraction.mul, Nat.mul_comm]

theorem mul_assoc (a b c : Mass) : a * b * c = a * (b * c) := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ x y z =>
    apply ofFraction_eq.mpr
    simp only [Fraction.mul, Nat.mul_assoc]

@[simp] theorem mul_one (a : Mass) : a * 1 = a := by
  induction a using Quotient.inductionOn with
  | _ x =>
    apply ofFraction_eq.mpr
    simp [Fraction.mul, Fraction.ofNat]

@[simp] theorem one_mul (a : Mass) : 1 * a = a := (mul_comm ..).trans (mul_one a)

@[simp] theorem mul_zero (a : Mass) : a * 0 = 0 := by
  induction a using Quotient.inductionOn with
  | _ x =>
    apply ofFraction_eq.mpr
    simp [Fraction.mul, Fraction.ofNat]

@[simp] theorem zero_mul (a : Mass) : 0 * a = 0 := (mul_comm ..).trans (mul_zero a)

theorem mul_add (a b c : Mass) : a * (b + c) = a * b + a * c := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ x y z =>
    apply ofFraction_eq.mpr
    simp only [Fraction.add, Fraction.mul, Nat.mul_add,
      Nat.mul_comm, Nat.mul_left_comm]

theorem add_mul (a b c : Mass) : (a + b) * c = a * c + b * c := by
  rw [mul_comm (a + b), mul_add, mul_comm c a, mul_comm c b]

theorem mul_nonneg {a b : Mass} (_ : 0 ≤ a) (_ : 0 ≤ b) : 0 ≤ a * b := zero_le _

theorem inv_pos {a : Mass} : 0 < a⁻¹ ↔ 0 < a := by
  induction a using Quotient.inductionOn with
  | _ x =>
    change 0 < ofFraction x.inv ↔ 0 < ofFraction x
    rw [ofFraction_pos, ofFraction_pos]
    by_cases h : x.num = 0
    · simp [Fraction.inv, Fraction.ofNat, h]
    · simp only [Fraction.inv, dite_eq_right h]
      exact ⟨fun _ => Nat.pos_of_ne_zero h, fun _ => x.positive⟩

theorem mul_inv_cancel (a : Mass) : a ≠ 0 → a * a⁻¹ = 1 := by
  induction a using Quotient.inductionOn with
  | _ x =>
    intro h
    have hn : x.num ≠ 0 := by
      intro hz
      apply h
      apply ofFraction_eq.mpr
      simp [Fraction.ofNat, hz]
    apply ofFraction_eq.mpr
    simp [Fraction.mul, Fraction.inv, Fraction.ofNat, hn, Nat.mul_comm]

theorem mul_le_mul_of_nonneg_right {a b c : Mass} (hab : a ≤ b) (_ : 0 ≤ c) :
    a * c ≤ b * c := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ x y z =>
    change x.num * z.num * (y.den * z.den) ≤ y.num * z.num * (x.den * z.den)
    have scaled := Nat.mul_le_mul_right (z.num * z.den)
      (show x.num * y.den ≤ y.num * x.den from hab)
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using scaled

theorem mul_le_mul_of_nonneg_left {a b c : Mass} (hab : a ≤ b) (hc : 0 ≤ c) :
    c * a ≤ c * b := by
  rw [mul_comm c a, mul_comm c b]
  exact mul_le_mul_of_nonneg_right hab hc

theorem add_le_add_right {a b : Mass} (hab : a ≤ b) (c : Mass) : a + c ≤ b + c := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ x y z =>
    change (x.num * z.den + z.num * x.den) * (y.den * z.den) ≤
      (y.num * z.den + z.num * y.den) * (x.den * z.den)
    have scaled := Nat.mul_le_mul_right (z.den * z.den)
      (show x.num * y.den ≤ y.num * x.den from hab)
    rw [Nat.add_mul, Nat.add_mul]
    simp only [Nat.mul_comm, Nat.mul_left_comm] at scaled ⊢
    exact Nat.add_le_add_right scaled _

theorem add_le_add {a b c d : Mass} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d := by
  apply le_trans (add_le_add_right hab c)
  rw [add_comm b c, add_comm b d]
  exact add_le_add_right hcd b

end Mass
end Zkc.Formal.Interactive
