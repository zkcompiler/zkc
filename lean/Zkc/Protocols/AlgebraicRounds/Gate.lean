module

public import Zkc.Protocols.AlgebraicRounds.Source
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Arithmetic obligations for the retained gate-message helper. The cubic
remainder is explicit: producing three coefficients does not itself establish
a degree-two reference. Actual helper/body association is a separate equation.
-/

namespace Zkc.Protocols.AlgebraicRounds.Gate

variable {F : Type} [CommRing F]

def value (add mul left right : F) : F := add * (left + right) + mul * left * right

def interpolate (low high challenge : F) : F := low + (high - low) * challenge

def quadratic (a0 a1 m0 m1 l0 l1 r0 r1 : F) : F :=
  (a1 - a0) * ((l1 - l0) + (r1 - r0)) +
    (m1 - m0) * ((l1 - l0) * r0 + l0 * (r1 - r0)) +
    m0 * (l1 - l0) * (r1 - r0)

def cubic (m0 m1 l0 l1 r0 r1 : F) : F := (m1 - m0) * (l1 - l0) * (r1 - r0)

def message (a0 a1 m0 m1 l0 l1 r0 r1 : F) : Zkc.Protocols.AlgebraicRounds.Message F :=
  let atZero := value a0 m0 l0 r0
  let atOne := value a1 m1 l1 r1
  let c2 := quadratic a0 a1 m0 m1 l0 l1 r0 r1
  ⟨atZero, atOne - atZero - c2, c2⟩

theorem evaluation_remainder (a0 a1 m0 m1 l0 l1 r0 r1 challenge : F) :
    value (interpolate a0 a1 challenge) (interpolate m0 m1 challenge)
      (interpolate l0 l1 challenge) (interpolate r0 r1 challenge) =
    (message a0 a1 m0 m1 l0 l1 r0 r1).evaluate challenge +
      cubic m0 m1 l0 l1 r0 r1 * (challenge ^ 3 - challenge) := by
  simp only [value, interpolate, message, quadratic, cubic,
    Zkc.Protocols.AlgebraicRounds.Message.evaluate]
  ring

/-- The caller proves that the right factor is independent of this variable.
This is the left-variable phase of a gate reference, not a property of a name. -/
theorem evaluation_of_right_independent (a0 a1 m0 m1 l0 l1 r0 r1 challenge : F)
    (independent : r1 = r0) :
    (message a0 a1 m0 m1 l0 l1 r0 r1).evaluate challenge =
      value (interpolate a0 a1 challenge) (interpolate m0 m1 challenge)
        (interpolate l0 l1 challenge) (interpolate r0 r1 challenge) := by
  rw [evaluation_remainder, independent]
  simp only [cubic, sub_self, mul_zero, zero_mul, add_zero]

/-- The complementary phase requires independence of the left factor. -/
theorem evaluation_of_left_independent (a0 a1 m0 m1 l0 l1 r0 r1 challenge : F)
    (independent : l1 = l0) :
    (message a0 a1 m0 m1 l0 l1 r0 r1).evaluate challenge =
      value (interpolate a0 a1 challenge) (interpolate m0 m1 challenge)
        (interpolate l0 l1 challenge) (interpolate r0 r1 challenge) := by
  rw [evaluation_remainder, independent]
  simp only [cubic, sub_self, mul_zero, zero_mul, add_zero]

end Zkc.Protocols.AlgebraicRounds.Gate
