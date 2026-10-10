import Zkc.Protocols.LinearRelation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Tests.LinearRelation

open Zkc.Protocols.LinearRelation

instance : Fact (Nat.Prime 23) := ⟨by decide⟩

/-- Completeness covers singular maps and zero challenges, without injectivity. -/
example (L : (Fin 4 → ZMod 23) →ₗ[ZMod 23] (ZMod 23 × (Fin 3 → ZMod 23)))
    (x r : Fin 4 → ZMod 23) : accepts L (L x) (L r) (0 : ZMod 23) r := by
  simpa using complete L x r (0 : ZMod 23)

/-- The general theorem is applicable to the module-valued combined map. -/
example (bases : Fin 4 → ZMod 23) (matrix : Fin 3 → Fin 4 → ZMod 23)
    (x r : Fin 4 → ZMod 23) (c : ZMod 23) :
    accepts (relationMap bases matrix)
      ((msmMap bases) x, (matrixMap matrix) x)
      ((msmMap bases) r, (matrixMap matrix) r) c (r + c • x) :=
  complete (relationMap bases matrix) x r c

/-- At zero challenge a response need not open the public image. -/
example : accepts (LinearMap.id : ZMod 23 →ₗ[ZMod 23] ZMod 23)
    (1 : ZMod 23) 0 (0 : ZMod 23) 0 ∧
    (0 : ZMod 23) ≠ 1 := by
  norm_num [accepts]

end Tests.LinearRelation
