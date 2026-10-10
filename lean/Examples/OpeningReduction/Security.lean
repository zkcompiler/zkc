import Examples.OpeningReduction.Openings

/-! Conditional terminal soundness for the actual composed source execution.

The opening error is the probability of accepting a false returned bundle in
this same experiment. No independence between the two bad events is required.
Supplying this bound for a cryptographic PCS remains a separate obligation.
-/

set_option autoImplicit false

namespace Examples.OpeningReduction.Openings
open PIR Zkc.Probability
open AdaptiveTape (Tape)
open Zkc.Protocols.Sumcheck (tapeList)

variable {Id F S : Type} {n : Nat}

section OpeningValidity
variable [CommRing F] [DecidableEq F]

def valid (env : Id → Table F n) (claims : Bundle Id F n) : Bool :=
  claims.all fun claim => decide ((env claim.object).eval claim.point = claim.value)

theorem valid_iff (env : Id → Table F n) (claims : Bundle Id F n) :
    valid env claims = true ↔ AllHold env claims := by
  simp [valid, List.all_eq_true, AllHold]

def accepted (verify : Bundle Id F n → Bool) : Outcome (Bundle Id F n) → Bool
  | .returned claims => verify claims
  | .stopped _ => false

def falseOpening (env : Id → Table F n) (verify : Bundle Id F n → Bool) :
    Outcome (Bundle Id F n) → Bool
  | .returned claims => verify claims && !valid env claims
  | .stopped _ => false

end OpeningValidity

private theorem average_add [Fintype F] (count : Nat) (f g : Tape F count → ℚ) :
    UniformTape.average count (fun coins => f coins + g coins) =
      UniformTape.average count f + UniformTape.average count g := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [UniformTape.average, ih, Finset.sum_add_distrib, add_div]

variable [Field F] [Fintype F] [DecidableEq F]

theorem acceptance_split (env : Id → Table F n) (objects : Objects Id)
    (send : S → Message F × S) (react : S → F → S)
    (report : S → Source.Accumulator F → Values F × S)
    (claim : F) (state : S) (verify : Bundle Id F n → Bool) :
    UniformTape.average n (fun coins =>
      if accepted verify (run send react report objects n claim state (tapeList n coins)).outcome
      then 1 else 0) ≤
    Rounds.acceptance (factors env objects) claim (Execution.strategy send react n state) +
      UniformTape.average n (fun coins =>
        if falseOpening env verify (run send react report objects n claim state (tapeList n coins)).outcome
        then 1 else 0) := by
  rw [Rounds.acceptance, ← average_add]
  apply UniformTape.monotone
  intro coins
  cases h : (run send react report objects n claim state (tapeList n coins)).outcome with
  | stopped reason =>
      simp only [accepted, falseOpening, Bool.false_eq_true, if_false, add_zero]
      split <;> norm_num
  | returned claims =>
      by_cases accepts : verify claims = true
      · by_cases holds : valid env claims = true
        · have good := returned_true_implies_verify env objects send react report claim state coins claims h
            ((valid_iff env claims).mp holds)
          simp [accepted, falseOpening, accepts, holds, good]
        · simp only [accepted, accepts, if_true, falseOpening, Bool.true_and, Bool.not_eq_true',
            Bool.eq_false_iff.mpr holds, if_true]
          split <;> norm_num
      · simp only [accepted, accepts, if_false, falseOpening,
          Bool.false_and, Bool.false_eq_true, if_false, add_zero]
        split <;> norm_num

/-- Ordinary soundness for actual returned bundles and a supplied terminal.
The premise bounds the terminal's false-opening event on the reached bundles,
including adaptively selected points. It is not a bound for an unrelated PCS game. -/
theorem soundness (env : Id → Table F n) (objects : Objects Id)
    (send : S → Message F × S) (react : S → F → S)
    (report : S → Source.Accumulator F → Values F × S)
    (claim : F) (state : S) (verify : Bundle Id F n → Bool) (error : ℚ)
    (falseClaim : claim ≠ (factors env objects).booleanSum)
    (terminalBound : UniformTape.average n (fun coins =>
      if falseOpening env verify (run send react report objects n claim state (tapeList n coins)).outcome
      then 1 else 0) ≤ error) :
    UniformTape.average n (fun coins =>
      if accepted verify (run send react report objects n claim state (tapeList n coins)).outcome
      then 1 else 0) ≤ (3 * (n : ℚ)) / Fintype.card F + error :=
  (acceptance_split env objects send react report claim state verify).trans
    (add_le_add (Rounds.soundness _ _ _ falseClaim) terminalBound)

end Examples.OpeningReduction.Openings
