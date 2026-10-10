import Zkc.Protocols.Sumcheck.Verifier
import Zkc.Polynomial.Coordinates

/-! Connect the residual-polynomial verifier to one fixed statement and the
actual complete challenge sequence. -/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck

open Zkc.Polynomial Zkc.Probability AlgebraicRounds
open AdaptiveTape (Tape)

variable {F : Type} {n : Nat}

def tapePoint : (n : Nat) → Tape F n → Fin n → F
  | 0, _ => fun index => Fin.elim0 index
  | n + 1, (r, tail) => Fin.cons r (tapePoint n tail)

def tapeList : (n : Nat) → Tape F n → List F
  | 0, _ => []
  | n + 1, (r, tail) => r :: tapeList n tail

theorem tapeList_length (n : Nat) (coins : Tape F n) : (tapeList n coins).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg Nat.succ (ih coins.2)

theorem tapeList_ofFn (n : Nat) (coins : Tape F n) :
    tapeList n coins = List.ofFn (tapePoint n coins) := by
  induction n with
  | zero => simp [tapeList]
  | succ n ih =>
      rcases coins with ⟨r, tail⟩
      simp [tapeList, tapePoint, List.ofFn_succ, ih]

variable [CommSemiring F] [DecidableEq F]

/-- Round rejection remains distinct from a scalar produced for the terminal test. -/
def finalClaim : {n : Nat} → Strategy F n → F → Tape F n → Option F
  | 0, .done, claim, _ => some claim
  | _ + 1, .send message next, claim, (r, tail) =>
      if message.boundary = claim then finalClaim (next r) (message.evaluate r) tail else none

theorem verify_iff_final (p : Quadratic F n) (claim : F) (strategy : Strategy F n)
    (coins : Tape F n) :
    verify p claim strategy coins = true ↔
      finalClaim strategy claim coins = some (p.eval (tapePoint n coins)) := by
  induction n generalizing claim with
  | zero => cases p; cases strategy; simp [verify, finalClaim, Quadratic.eval]
  | succ n ih =>
      cases strategy with
      | send message next =>
          rcases coins with ⟨r, tail⟩
          by_cases passes : message.boundary = claim
          · simp only [verify, finalClaim, if_pos passes]
            rw [ih, Quadratic.eval_restrict]
            rfl
          · simp [verify, finalClaim, passes]

end Zkc.Protocols.Sumcheck
