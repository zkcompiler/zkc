module

public import Zkc.Frontend.Written.ChargeData
public import Zkc.Formal.FiniteService

@[expose] public section
namespace Zkc.Formal.Written
open Core Interactive FiniteService ProbabilisticProcess OracleComp
open Frontend.Written (DrawCharge)
open scoped NNReal ENNReal

noncomputable def total (charge : DrawCharge) : ℝ≥0∞ :=
  charge.draws.length * ((charge.numerator : ℝ≥0∞) / charge.denominator)

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

end Zkc.Formal.Written
