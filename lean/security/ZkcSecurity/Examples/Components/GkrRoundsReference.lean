module

public import ZkcSecurity.Families.Sumcheck.FactorReference
public import Zkc.Protocols.AlgebraicRounds.Gate

@[expose] public section

/-! The gate reference retains all four factors. Its admissibility obligation
explicitly requires independence of the inactive wire factor at each arbitrary
future restriction. Initializing this invariant from GKR's split-variable
layout and realizing the imported list helpers are separate client laws. -/

namespace ZkcSecurity.Examples.Components.GkrRoundsReference
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.Families.Sumcheck
open Zkc.Protocols.AlgebraicRounds

variable {F : Type} [Field F]

structure State (F : Type) (n : Nat) where
  add : Table F n
  mul : Table F n
  left : Table F n
  right : Table F n

def restrict {n : Nat} (s : State F (n + 1)) (r : F) : State F n :=
  ⟨fixFirst s.add r, fixFirst s.mul r, fixFirst s.left r, fixFirst s.right r⟩

def total {n : Nat} (s : State F n) : F :=
  booleanSum (fun bits => Gate.value (s.add bits) (s.mul bits) (s.left bits) (s.right bits))

def independent {n : Nat} (s : State F (n + 1)) : Prop :=
  FactorReference.ActiveIndependent (fun r => fixFirst s.left r) ∨
  FactorReference.ActiveIndependent (fun r => fixFirst s.right r)

/-- This obligation quantifies over every challenge, including off-cube
challenges and prefixes shorter than the full number of rounds. -/
def admissible : {n : Nat} → State F n → Prop
  | 0, _ => True
  | _ + 1, s => independent s ∧ ∀ r, admissible (restrict s r)

def pointMessage {n : Nat} (s : State F (n + 1)) (bits : Fin n → Bool) :=
  Gate.message (half s.add false bits) (half s.add true bits)
    (half s.mul false bits) (half s.mul true bits)
    (half s.left false bits) (half s.left true bits)
    (half s.right false bits) (half s.right true bits)

def message {n : Nat} (s : State F (n + 1)) : Zkc.Protocols.AlgebraicRounds.Message F :=
  ⟨booleanSum (fun bits => (pointMessage s bits).constant),
    booleanSum (fun bits => (pointMessage s bits).linear),
    booleanSum (fun bits => (pointMessage s bits).quadratic)⟩

theorem point_evaluation {n : Nat} (s : State F (n + 1)) (r : F)
    (allowed : independent s) (bits : Fin n → Bool) :
    (pointMessage s bits).evaluate r =
      Gate.value ((restrict s r).add bits) ((restrict s r).mul bits)
        ((restrict s r).left bits) ((restrict s r).right bits) := by
  have endpoints (table : Table F (n + 1))
      (h : FactorReference.ActiveIndependent (fun r => fixFirst table r)) :
      half table true bits = half table false bits := by
    simpa only [fixFirst_one, fixFirst_zero] using h 1 bits
  change (Gate.message _ _ _ _ _ _ _ _).evaluate r = _
  rcases allowed with h | h
  · rw [Gate.evaluation_of_left_independent _ _ _ _ _ _ _ _ r (endpoints s.left h)]
    simp only [restrict, fixFirst_apply, Gate.interpolate]
  · rw [Gate.evaluation_of_right_independent _ _ _ _ _ _ _ _ r (endpoints s.right h)]
    simp only [restrict, fixFirst_apply, Gate.interpolate]

theorem evaluation {n : Nat} (s : State F (n + 1)) (r : F)
    (allowed : independent s) : (message s).evaluate r = total (restrict s r) := by
  simp only [message, Zkc.Protocols.AlgebraicRounds.Message.evaluate]
  rw [mul_comm _ r, mul_comm _ (r * r)]
  rw [← booleanSum_scale, ← booleanSum_scale, ← booleanSum_add, ← booleanSum_add]
  calc
    _ = booleanSum (fun bits => (pointMessage s bits).evaluate r) := by
      congr 1
      funext bits
      simp only [Zkc.Protocols.AlgebraicRounds.Message.evaluate]
      ring
    _ = total (restrict s r) := by
      congr 1
      funext bits
      exact point_evaluation s r allowed bits

noncomputable def data (F : Type) [Field F] : Reference F where
  State := State F
  total := total
  restrict := restrict
  polynomial s := Zkc.Protocols.Sumcheck.messagePolynomial (message s)
  admissible := admissible

theorem laws : ReferenceLaws (data F) 2 where
  degree_le _ _ := Zkc.Protocols.Sumcheck.messagePolynomial_degree _
  boundary_eq s allowed := by
    rw [boundaryPoly]
    change (Zkc.Protocols.Sumcheck.messagePolynomial (message s)).eval 0 +
      (Zkc.Protocols.Sumcheck.messagePolynomial (message s)).eval 1 = _
    rw [Zkc.Protocols.Sumcheck.messagePolynomial_eval, Zkc.Protocols.Sumcheck.messagePolynomial_eval,
      evaluation s 0 allowed.1, evaluation s 1 allowed.1]
    simp only [total, restrict, fixFirst_zero, fixFirst_one]
    rfl
  evaluation_eq s r allowed := by
    change (Zkc.Protocols.Sumcheck.messagePolynomial (message s)).eval r = _
    rw [Zkc.Protocols.Sumcheck.messagePolynomial_eval]
    exact evaluation s r allowed.1
  restriction_closed _ r allowed := allowed.2 r

theorem prefix_admissible {n : Nat} (count : Nat) (s : State F (n + count))
    (challenges : Fin count → F) (allowed : admissible s) :
    (data F).admissible ((data F).restrictPrefix count s challenges) :=
  Reference.admissible_restrictPrefix laws count s challenges allowed

/-- The representation keeps each original factor after every prefix. It
never replaces the gate by a multilinear table of pointwise products. -/
theorem prefix_factors {n : Nat} (count : Nat) (s : State F (n + count))
    (challenges : Fin count → F) :
    (data F).restrictPrefix count s challenges =
      ⟨fixPrefix count s.add challenges, fixPrefix count s.mul challenges,
        fixPrefix count s.left challenges, fixPrefix count s.right challenges⟩ := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih (restrict s (challenges 0)) (challenges ∘ Fin.succ)

theorem prefix_extension {n : Nat} (count : Nat) (s : State F (n + count))
    (challenges : Fin count → F) (tail : Fin n → F) :
    let current := (data F).restrictPrefix count s challenges
    Gate.value (extension n current.add tail) (extension n current.mul tail)
      (extension n current.left tail) (extension n current.right tail) =
    Gate.value (extension (n + count) s.add (Quadratic.point count challenges tail))
      (extension (n + count) s.mul (Quadratic.point count challenges tail))
      (extension (n + count) s.left (Quadratic.point count challenges tail))
      (extension (n + count) s.right (Quadratic.point count challenges tail)) := by
  simp only [prefix_factors]
  rw [extension_fixPrefix, extension_fixPrefix, extension_fixPrefix, extension_fixPrefix]

end ZkcSecurity.Examples.Components.GkrRoundsReference
