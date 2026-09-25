import Zkc.Protocols.AlgebraicRounds.BlockEvaluation

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds.Early
open Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Protocols.AlgebraicRounds.BlockEvaluation Zkc.Compiler.Blocks

open Zkc.Protocols.AlgebraicRounds.Scalar Zkc.Compiler.Blocks

abbrev Message (F : Type) := F × F × F
def roundOf {F : Type} (msg : Message F) (r : F) : Round F :=
  ⟨msg.1, msg.2.1, msg.2.2, r⟩

inductive Event (F : Type)
  | message : Message F → Event F
  | challenge : F → Event F
  | reject : Event F
  deriving DecidableEq

structure Execution (F S Q : Type) where
  trace : List (Event F)
  result : Option F
  proverState : S
  oracleState : Q

-- Private prover state is only supplied to send/react. The draw handler owns
-- Q; the prover never receives Q or a future challenge. No probabilistic law,
-- independence claim or efficient-adversary model is implicit in these types.
def early {F S Q : Type} [CommRing F] [DecidableEq F]
    (evaluate : Round F → F) (send : S → Message F × S)
    (react : S → F → S) (draw : Q → F × Q) :
    Nat → F → S → Q → Execution F S Q
  | 0, claim, ps, qs => ⟨[], some claim, ps, qs⟩
  | k+1, claim, ps, qs =>
    let (msg, ps') := send ps
    if boundary (roundOf msg 0) = claim then
      let (r, qs') := draw qs
      let out := early evaluate send react draw k (evaluate (roundOf msg r)) (react ps' r) qs'
      { out with trace := .message msg :: .challenge r :: out.trace }
    else ⟨[.message msg, .reject], none, ps', qs⟩

-- Complete every scheduled interaction without checks. This deliberately
-- follows the order of ArkLib's default prover-run-then-verifier execution.
def complete {F S Q : Type} (send : S → Message F × S)
    (react : S → F → S) (draw : Q → F × Q) : Nat → S → Q → List (Round F) × S × Q
  | 0, ps, qs => ([], ps, qs)
  | k+1, ps, qs =>
    let (msg, ps') := send ps
    let (r, qs') := draw qs
    let out := complete send react draw k (react ps' r) qs'
    (roundOf msg r :: out.1, out.2)

def replay {F : Type} [CommRing F] [DecidableEq F] (evaluate : Round F → F) :
    F → List (Round F) → Option F
  | claim, [] => some claim
  | claim, g :: gs => if boundary g = claim then replay evaluate (evaluate g) gs else none

theorem early_completed_verdict {F S Q : Type} [CommRing F] [DecidableEq F]
    (evaluate : Round F → F) (send : S → Message F × S)
    (react : S → F → S) (draw : Q → F × Q) (k : Nat) (claim : F) (ps : S) (qs : Q) :
    (early evaluate send react draw k claim ps qs).result =
    replay evaluate claim (complete send react draw k ps qs).1 := by
  induction k generalizing claim ps qs with
  | zero => rfl
  | succ k ih =>
    simp only [early, complete, replay, boundary, roundOf]
    by_cases h : (send ps).1.1 + (send ps).1.1 + (send ps).1.2.1 +
        (send ps).1.2.2 = claim
    · simp only [h, ↓reduceIte]
      exact ih _ _ _
    · simp only [h, ↓reduceIte]

theorem replay_source {F : Type} [CommRing F] [DecidableEq F]
    (claim : F) (gs : List (Round F)) : replay value claim gs = Zkc.Protocols.AlgebraicRounds.Scalar.run claim gs := by
  induction gs generalizing claim with
  | nil => rfl
  | cons g gs ih => simp only [replay, Zkc.Protocols.AlgebraicRounds.Scalar.run, ih]

-- Equality is required only after all boundary checks pass; on rejected runs
-- the source legitimately omits suffix messages and oracle state transitions.
theorem early_success_state {F S Q : Type} [CommRing F] [DecidableEq F]
    (evaluate : Round F → F) (send : S → Message F × S)
    (react : S → F → S) (draw : Q → F × Q)
    (k : Nat) (claim z : F) (ps : S) (qs : Q)
    (ok : (early evaluate send react draw k claim ps qs).result = some z) :
    (early evaluate send react draw k claim ps qs).proverState =
      (complete send react draw k ps qs).2.1 ∧
    (early evaluate send react draw k claim ps qs).oracleState =
      (complete send react draw k ps qs).2.2 := by
  induction k generalizing claim ps qs with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    simp only [early] at ok ⊢
    split at ok
    · rename_i h
      simp only [h, ↓reduceIte, complete]
      exact ih _ _ _ ok
    · contradiction

-- A checked replacement preserves the full stopping execution, including
-- failure location, observed messages/challenges and residual states.
theorem checked_early {F S Q : Type} [CommRing F] [DecidableEq F]
    (source target : Block F) (ss ts : Nat)
    (ok : Zkc.Compiler.Blocks.hornerCheck source target ss ts = true)
    (send : S → Message F × S) (react : S → F → S) (draw : Q → F × Q)
    (k : Nat) (claim : F) (ps : S) (qs : Q) :
    early (moduleValue target ts) send react draw k claim ps qs =
    early value send react draw k claim ps qs := by
  have h : moduleValue target ts = value := by
    funext g; exact (checked_values source target ss ts ok g).2
  rw [h]

def badSend (_ : Unit) : Message Int × Unit := ((0,0,0), ())
def ignoreChallenge (_ : Unit) (_ : Int) : Unit := ()
def counterDraw (q : Nat) : Int × Nat := (q, q+1)

theorem early_failure_draws_zero :
    (early value badSend ignoreChallenge counterDraw 1 1 () 0).result = none ∧
    (early value badSend ignoreChallenge counterDraw 1 1 () 0).oracleState = 0 := by decide

theorem deferred_failure_draws_one :
    replay value 1 (complete badSend ignoreChallenge counterDraw 1 () 0).1 = none ∧
    (complete badSend ignoreChallenge counterDraw 1 () 0).2.2 = 1 := by decide

-- A subsequent call observes the difference although both first calls reject.
theorem verdict_erasure_not_contextual :
    (counterDraw (early value badSend ignoreChallenge counterDraw 1 1 () 0).oracleState).1 ≠
    (counterDraw (complete badSend ignoreChallenge counterDraw 1 () 0).2.2).1 := by decide


end Zkc.Protocols.AlgebraicRounds.Early
