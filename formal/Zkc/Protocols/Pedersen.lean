import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Module

/-! The excess-commitment equation for actual shared openings.

An existential opening of each group element does not by itself establish that
independent proofs use compatible openings. These are algebraic identities;
binding, extraction and joint witness consistency remain separate premises.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Pedersen

open scoped BigOperators

variable {F G I O : Type*} [CommRing F] [AddCommGroup G] [Module F G]

def commit (base blind : G) (amount randomness : F) : G :=
  amount • base + randomness • blind

theorem excess [Fintype I] [Fintype O]
    (base blind : G) (inputs inputRandomness : I → F)
    (outputs outputRandomness : O → F) (fee : F) :
    (∑ i, commit base blind (inputs i) (inputRandomness i)) -
      (∑ i, commit base blind (outputs i) (outputRandomness i)) - fee • base =
    ((∑ i, inputs i) - (∑ i, outputs i) - fee) • base +
      ((∑ i, inputRandomness i) - (∑ i, outputRandomness i)) • blind := by
  simp only [commit, Finset.sum_add_distrib, ← Finset.sum_smul]
  module

/-- For balanced amounts, the actual excess is a commitment to the difference
of blindings. The difference, and hence the excess point, may legitimately be
zero. Rejecting every identity excess would lose these honest transactions. -/
theorem balanced_excess [Fintype I] [Fintype O]
    (base blind : G) (inputs inputRandomness : I → F)
    (outputs outputRandomness : O → F) (fee : F)
    (balanced : (∑ i, inputs i) = (∑ i, outputs i) + fee) :
    (∑ i, commit base blind (inputs i) (inputRandomness i)) -
      (∑ i, commit base blind (outputs i) (outputRandomness i)) - fee • base =
    ((∑ i, inputRandomness i) - (∑ i, outputRandomness i)) • blind := by
  rw [excess, balanced]
  simp

end Zkc.Protocols.Pedersen
