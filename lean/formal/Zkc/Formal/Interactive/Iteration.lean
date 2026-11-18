module

public import Zkc.Formal.Interactive.Experiment

@[expose] public section

namespace Zkc.Formal.Interactive
open Core

/-- Sum of the charges of the next `count` steps starting at `index`. -/
def charges (cost : Nat → Mass) : (count index : Nat) → Mass
  | 0, _ => 0
  | n + 1, i => cost i + charges cost n (i + 1)

theorem charges_nonnegative (cost : Nat → Mass) (nonnegative : ∀ i, 0 ≤ cost i)
    (count index : Nat) : 0 ≤ charges cost count index := by
  induction count generalizing index with
  | zero => exact Mass.le_refl
  | succ n ih =>
    simpa only [Mass.zero_add, charges] using Mass.add_le_add (nonnegative index) (ih (index + 1))

/-- A reduction rule for the core iterator. The hypothesis for a new round is required
only on an authorized state with a false current claim. Reachable, positive-weight replies
carry the authorization to the next round. -/
theorem Experiment.reduction_iterate {S : Sig} {σ H A : Type} (K : Experiment S σ)
    (step : Nat → A → Process S H A) (claim : Nat → A → σ → Bool)
    (authorized : Nat → A → σ → Prop) (cost : Nat → Mass) (nonnegative : ∀ i, 0 ≤ cost i)
    (next : ∀ i a s, authorized i a s → ∀ b t, K.Reaches (step i a) s b t → authorized (i+1) b t)
    (round : ∀ i a s, authorized i a s → claim i a s = false →
      K.probability (step i a) s (claim (i+1)) ≤ cost i)
    (count i : Nat) (a : A) (s : σ) (auth : authorized i a s) (wrong : claim i a s = false) :
    K.probability (Process.iterate count step i a) s (claim (i+count)) ≤ charges cost count i := by
  induction count generalizing i a s with
  | zero =>
    simp only [Process.iterate, probability, expect, Nat.add_zero, wrong, Bool.false_eq_true,
      ite_false, charges]
    exact Mass.le_refl
  | succ n ih =>
    simp only [Process.iterate, charges]
    apply K.reduction_bind _ _ _ (claim (i+1)) _ (round i a s auth wrong)
      (charges_nonnegative cost nonnegative n (i+1))
    intro b t reached falseAt
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using
      ih (i+1) b t (next i a s auth b t reached) falseAt

end Zkc.Formal.Interactive
