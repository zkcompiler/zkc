module

@[expose] public section

/-! Kernel-reducible decisions for source admission. The Boolean computation
must remain visible across module boundaries: admission certificates are
checked by kernel reduction, independently of the compiled evaluator. -/

namespace Zkc.Source

/-- Equality of admission results, with exposed computation in both branches.
This avoids relying on an imported derived instance's implementation visibility. -/
instance (priority := high) instDecidableEqExcept {ε : Type _} {α : Type _}
    [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .error left, .error right => decidable_of_iff (left = right) (by simp)
  | .ok left, .ok right => decidable_of_iff (left = right) (by simp)
  | .error _, .ok _ => isFalse (by simp)
  | .ok _, .error _ => isFalse (by simp)

end Zkc.Source
