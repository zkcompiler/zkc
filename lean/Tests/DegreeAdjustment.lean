import Zkc.Polynomial.DegreeAdjustment
import Mathlib.Algebra.Field.ZMod
import Tools.DeclarationAudit

set_option autoImplicit false

namespace Tests.DegreeAdjustment
open Polynomial Zkc.Polynomial.DegreeAdjustment
private abbrev F := ZMod 17
private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

example (p : F[X]) (hp : p ≠ 0) :
    (X * p).natDegree < 8 ↔ p.natDegree + 1 < 8 := degree_iff p hp 8

example (p : F[X]) : X - C (3 : F) ∣ X * p ↔ X - C (3 : F) ∣ p :=
  opening_divisor_iff p 3 (by decide)

-- Zero is genuinely excluded: multiplying by X can add a root there.
example : (X : F[X]) ∣ X * 1 ∧ ¬ (X : F[X]) ∣ 1 := by
  constructor
  · simp
  · intro h
    have : IsRoot (1 : F[X]) 0 := dvd_iff_isRoot.mp (by simpa using h)
    simp [IsRoot] at this

example (a b : F) : (3 : F) * a = 3 * b ↔ a = b :=
  agreement_iff 3 a b (by decide)

end Tests.DegreeAdjustment

-- A module is not in its own environment while it elaborates, so it cannot
-- audit itself; Tests/Audit.lean covers the Tests family from a module that
-- imports them all.
run_cmd Tools.DeclarationAudit.check [
  `Zkc.Polynomial.DegreeAdjustment] "DEGREE-ADJUSTMENT-AUDIT-PASS"
