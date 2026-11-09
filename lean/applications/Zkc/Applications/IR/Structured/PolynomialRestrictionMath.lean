module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Fixed coefficient storage for the source restriction helper. The four
slots are coefficients, not evaluations at the four Boolean vertices. -/

set_option autoImplicit false
namespace ZkcExamples.Structured.PolynomialRestrictionMath

structure Bilinear (F : Type) where
  c00 : F
  c10 : F
  c01 : F
  c11 : F

structure Affine (F : Type) where
  constant : F
  linear : F

variable {F : Type} [CommRing F]

def Bilinear.evaluate (p : Bilinear F) (x y : F) : F :=
  p.c00 + p.c10 * x + p.c01 * y + p.c11 * x * y

def Affine.evaluate (p : Affine F) (y : F) : F := p.constant + p.linear * y

def restrictFirst (p : Bilinear F) (x : F) : Affine F :=
  ⟨p.c00 + p.c10 * x, p.c01 + p.c11 * x⟩

/-- Every remaining challenge is allowed, including values outside {0,1}. -/
theorem restriction_evaluation (p : Bilinear F) (x y : F) :
    (restrictFirst p x).evaluate y = p.evaluate x y := by
  simp only [restrictFirst, Affine.evaluate, Bilinear.evaluate]
  ring

/-- A second restriction returns the scalar; there is no degree reduction by
re-interpolating a non-multilinear polynomial on its Boolean evaluations. -/
theorem complete_restriction (p : Bilinear F) (x y : F) :
    (restrictFirst p x).constant + (restrictFirst p x).linear * y = p.evaluate x y :=
  restriction_evaluation p x y

omit [CommRing F] in
def Bilinear.slots (p : Bilinear F) : List F := [p.c00, p.c10, p.c01, p.c11]

omit [CommRing F] in
def Affine.slots (p : Affine F) : List F := [p.constant, p.linear]

/-- Exact capacity closure: zero coefficients retain their slots. Restriction
never allocates new supports or aggregates duplicate monomials. -/
theorem restriction_storage (p : Bilinear F) (x : F) :
    p.slots.length = 4 ∧ (restrictFirst p x).slots.length = 2 ∧
      (restrictFirst p x).slots.length < p.slots.length := by
  exact ⟨rfl, rfl, by change 2 < 4; decide⟩

end ZkcExamples.Structured.PolynomialRestrictionMath
