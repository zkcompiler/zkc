import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds.Scalar
structure Round (F : Type) where
  a : F
  b : F
  c : F
  r : F
deriving DecidableEq

variable {F : Type} [CommRing F]
def boundary (g : Round F) : F := g.a + g.a + g.b + g.c
def value (g : Round F) : F := g.a + g.b * g.r + g.c * (g.r * g.r)
def run [DecidableEq F] : F → List (Round F) → Option F
  | s, [] => some s
  | s, g :: gs => if boundary g = s then run (value g) gs else none

-- An operationally useful characterization, quantified over malicious rounds.
def equations : F → List (Round F) → F → Prop
  | s, [], z => s = z
  | s, g :: gs, z => boundary g = s ∧ equations (value g) gs z
theorem run_iff_equations [DecidableEq F] (s z : F) (gs : List (Round F)) :
    run s gs = some z ↔ equations s gs z := by
  induction gs generalizing s with
  | nil => simp [run, equations]
  | cons g gs ih =>
    by_cases h : boundary g = s <;> simp [run, equations, h, ih]

theorem horner_value (g : Round F) :
    value g = g.a + g.r * (g.b + g.r * g.c) := by simp [value]; ring


end Zkc.Protocols.AlgebraicRounds.Scalar
