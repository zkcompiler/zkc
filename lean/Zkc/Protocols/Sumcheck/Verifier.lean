module

public import Zkc.Protocols.Sumcheck.Polynomial
public import Zkc.Semantics.AdaptiveTape

@[expose] public section

/-! Complete ordinary interactive Sumcheck for fixed degree-two polynomials.

A strategy chooses its message before receiving the next challenge. Each
continuation may depend arbitrarily on that challenge and earlier history.
The terminal test evaluates the fixed statement after all coordinates have
been substituted. No honesty restriction is imposed in the soundness theorem.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck

open Zkc.Polynomial Zkc.Probability AlgebraicRounds
open AdaptiveTape (Tape)
open scoped BigOperators

/-- A bounded adaptive prover. Fixed private randomness can be included in the
choice of this entire strategy; the fresh verifier tape is separate. -/
inductive Strategy (F : Type) : Nat → Type where
  | done : Strategy F 0
  | send {n : Nat} : Message F → (F → Strategy F n) → Strategy F (n + 1)

variable {F : Type} {n : Nat}

section Semiring
variable [CommSemiring F] [DecidableEq F]

def verify : {n : Nat} → Quadratic F n → F → Strategy F n → Tape F n → Bool
  | 0, .constant value, claim, .done, _ => decide (claim = value)
  | _ + 1, p, claim, .send message next, (challenge, tail) =>
      if message.boundary = claim then
        verify (p.restrict challenge) (message.evaluate challenge) (next challenge) tail
      else false

def honest : {n : Nat} → Quadratic F n → Strategy F n
  | 0, _ => .done
  | _ + 1, p => .send (roundPolynomial p) (fun r => honest (p.restrict r))

theorem completeness (p : Quadratic F n) (coins : Tape F n) :
    verify p p.booleanSum (honest p) coins = true := by
  induction n with
  | zero => cases p; simp [verify, honest, Quadratic.booleanSum, cubeSum, Quadratic.eval]
  | succ n ih =>
      rcases coins with ⟨r, tail⟩
      simp only [honest, verify, round_boundary, round_evaluate]
      exact ih _ tail

end Semiring


end Zkc.Protocols.Sumcheck
