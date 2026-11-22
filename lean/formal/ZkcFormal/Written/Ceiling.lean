module

public import Zkc.Frontend.Written.ChargeData
public import ZkcFormal.FiniteService

@[expose] public section
namespace ZkcFormal.Written
open Zkc.Core Interactive FiniteService ProbabilisticProcess OracleComp
open Zkc.Frontend.Written (DrawCharge)
open scoped NNReal ENNReal

noncomputable def total (charge : DrawCharge) : ℝ≥0∞ :=
  charge.draws.length * ((charge.numerator : ℝ≥0∞) / charge.denominator)

/-- The total of a charge is within a ceiling given as a fraction, when the comparison of the two
fractions holds over the naturals: what a module states of a goal that has a ceiling, the
comparison being decided by the kernel. -/
theorem total_le_div (charge : DrawCharge) (p q : ℕ) (positive : 0 < q)
    (denPositive : 0 < charge.denominator)
    (cross : charge.draws.length * charge.numerator * q ≤ p * charge.denominator) :
    total charge ≤ (p : ℝ≥0∞) / q := by
  have hq : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast positive.ne'
  have hd : (charge.denominator : ℝ≥0∞) ≠ 0 := by exact_mod_cast denPositive.ne'
  unfold total
  rw [← mul_div_assoc, ENNReal.div_le_iff hd (ENNReal.natCast_ne_top _),
    ← ENNReal.mul_div_right_comm,
    ENNReal.le_div_iff_mul_le (Or.inl hq) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast cross

/-- Transfer an already established finite-process bound to a written per-occurrence
ceiling. The family supplies its event, its finite lemma and the occurrence count.
A closed execution with zero occurrences needs no unit ceiling comparison. -/
theorem writtenCeiling {S : Sig} {σ H A : Type}
    (t : Slots S σ) (p : Process S H A) (s : σ) (event : A → σ → Bool)
    (charge : DrawCharge) (n degree order : Nat) (positive : 0 < order)
    (count : charge.draws.length = n) (denPositive : 0 < charge.denominator)
    (covers : 0 < n → degree * charge.denominator ≤ charge.numerator * order)
    (bounded : (finite t).probability p s event ≤ (n : Mass) * ((degree : Mass) / (order : Mass))) :
    prEvent (observed event <$> run (service t) p s) ≤ total charge := by
  rw [finite_slots_probability]
  apply (embed_le.mpr bounded).trans
  rw [embed_mul, Mass.natCast_div _ _ positive, embed_fraction]
  have coeCount : embed (n : Mass) = (n : ℝ≥0∞) :=
    (embed_fraction (.ofNat n)).trans (by simp [Mass.Fraction.ofNat])
  rw [coeCount]
  by_cases zero : n = 0
  · simp [total, count, zero]
  · have within : (degree : Mass) / (order : Mass) ≤ (charge.numerator : Mass) / (charge.denominator : Mass) := by
      rw [Mass.natCast_div _ _ positive, Mass.natCast_div _ _ denPositive]
      exact Mass.ofFraction_le.mpr (covers (Nat.pos_of_ne_zero zero))
    have lifted := embed_le.mpr within
    rw [Mass.natCast_div _ _ positive, Mass.natCast_div _ _ denPositive, embed_fraction, embed_fraction] at lifted
    have nonzero : (charge.denominator : ℝ≥0) ≠ 0 := by exact_mod_cast denPositive.ne'
    simp only [total, count]
    gcongr
    simpa [ENNReal.coe_div nonzero] using lifted

end ZkcFormal.Written
