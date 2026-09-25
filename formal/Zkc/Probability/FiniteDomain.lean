import Mathlib.Data.ZMod.Basic

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Probability.FiniteDomain
/-- Canonical representatives: no primality premise is needed for this embedding. -/
def intervalEmbed {M q : Nat} (h : M ≤ q) (d : Fin M) : Fin q :=
  ⟨d.val,lt_of_lt_of_le d.isLt h⟩

theorem interval_injective {M q : Nat} (h : M ≤ q) :
    Function.Injective (intervalEmbed h) := by
  intro x y eq
  exact Fin.ext (congrArg (fun z : Fin q => z.val) eq)

def scalarEmbed {M q : Nat} (h : M ≤ q) (d : Fin M) : ZMod q :=
  ((intervalEmbed h d).val : ZMod q)

theorem scalar_canonical {M q : Nat} [NeZero q] (h : M ≤ q) (d : Fin M) :
    (scalarEmbed h d).val = d.val := by
  simp [scalarEmbed,intervalEmbed,ZMod.val_natCast,Nat.mod_eq_of_lt (lt_of_lt_of_le d.isLt h)]

theorem scalar_injective {M q : Nat} [NeZero q] (h : M ≤ q) :
    Function.Injective (scalarEmbed h) := by
  intro x y eq
  apply Fin.ext
  simpa only [scalar_canonical] using congrArg ZMod.val eq


end Zkc.Probability.FiniteDomain
