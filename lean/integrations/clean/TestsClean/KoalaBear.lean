import Clean.Utils.FiniteField
import Clean.Circuit.Expression
import Mathlib.Tactic.NormNum.Prime

/-! The KoalaBear prime field `F p`, p = 2^31 - 2^24 + 1, used by the controls. -/

set_option autoImplicit false

namespace TestsClean

abbrev koalaBear : Nat := 2130706433

example : koalaBear = 2 ^ 31 - 2 ^ 24 + 1 := by norm_num

set_option maxRecDepth 100000 in
instance koalaBear_prime : Fact (Nat.Prime koalaBear) := ⟨by norm_num⟩

instance koalaBear_gt_two : Fact (koalaBear > 2) := ⟨by norm_num⟩

instance koalaBear_gt_512 : Fact (koalaBear > 512) := ⟨by norm_num⟩

abbrev KoalaBear := F koalaBear

/-- `Environment.data` for controls whose constraints read no prover data. -/
def noData : ProverData KoalaBear := fun _ _ => #[]

def noPublic : Fin 0 → KoalaBear := Fin.elim0

end TestsClean
