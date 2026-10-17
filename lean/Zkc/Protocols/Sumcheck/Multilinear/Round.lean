module

public import Zkc.Polynomial.Multilinear.Marginal
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-! Algebra of endpoint messages for the multilinear Sumcheck library.
These are values at zero and one, not polynomial coefficients. This module
does not prescribe an interaction or identify independently delivered values.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Multilinear

open Zkc.Polynomial.Multilinear

variable {F : Type} {n : Nat}

abbrev Message (F : Type) := F × F

def boundary [Add F] (message : Message F) : F := message.1 + message.2

def evaluate [Ring F] (message : Message F) (r : F) : F :=
  (1 - r) * message.1 + r * message.2

def honestMessage [Add F] (table : Table F (n + 1)) : Message F :=
  (booleanSum (half table false), booleanSum (half table true))

theorem boundary_honestMessage [Add F] (table : Table F (n + 1)) :
    boundary (honestMessage table) = booleanSum table := rfl

theorem evaluate_zero [Ring F] (message : Message F) : evaluate message 0 = message.1 := by
  simp [evaluate]

theorem evaluate_one [Ring F] (message : Message F) : evaluate message 1 = message.2 := by
  simp [evaluate]

theorem evaluate_honestMessage [Ring F] (table : Table F (n + 1)) (r : F) :
    evaluate (honestMessage table) r = booleanSum (fixFirst table r) :=
  (booleanSum_fixFirst table r).symm

theorem honestMessage_sumRemaining [Add F] {remaining count : Nat} (table : Table F (remaining + (count + 1))) :
    honestMessage (sumRemaining remaining (count + 1) table) = honestMessage table := by
  change (booleanSum (sumRemaining remaining count (half table false)),
    booleanSum (sumRemaining remaining count (half table true))) = _
  rw [booleanSum_sumRemaining, booleanSum_sumRemaining]
  rfl

/-- Each role uses its own challenge. Faithful message delivery alone does not
identify the verifier's next claim with the prover's residual sum. -/
theorem role_local_update [Ring F] (table : Table F (n + 1))
    (received : Message F) (messageDelivery : received = honestMessage table)
    (proverChallenge verifierChallenge : F) :
    booleanSum (fixFirst table proverChallenge) - evaluate received verifierChallenge =
      (proverChallenge - verifierChallenge) *
        ((honestMessage table).2 - (honestMessage table).1) := by
  subst received
  rw [← evaluate_honestMessage]
  simp only [evaluate]
  noncomm_ring

/-- Honest update under an explicit challenge-delivery agreement. The boundary
premise is separate: this equation says nothing about when a challenge is drawn. -/
theorem honest_update [Ring F] (table : Table F (n + 1)) (received : Message F)
    (messageDelivery : received = honestMessage table)
    (proverChallenge verifierChallenge : F) (challengeDelivery : proverChallenge = verifierChallenge) :
    booleanSum (fixFirst table proverChallenge) = evaluate received verifierChallenge := by
  subst received
  subst proverChallenge
  exact (evaluate_honestMessage table verifierChallenge).symm

/-- The optional polynomial adapter uses `C a0 + C (a1-a0) * X`.
This equation is independent of any polynomial/security package. -/
theorem evaluate_affine [Ring F] (message : Message F) (r : F) :
    evaluate message r = message.1 + r * (message.2 - message.1) := by
  simp only [evaluate]
  noncomm_ring

end Zkc.Protocols.Sumcheck.Multilinear
