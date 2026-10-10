import Examples.OpeningReduction.Execution
import Zkc.Semantics.Relation

/-! Ordered opening obligations for the original factors at the delivered point.

The environment is used only by propositions. The executable consumer knows
object identifiers, the residual scalar/point, and reported values. Returning a
bundle does not discharge it or establish commitment binding.
-/

set_option autoImplicit false

namespace Examples.OpeningReduction.Openings
open PIR Zkc.Probability
open AdaptiveTape (Tape)
open Zkc.Protocols.Sumcheck (tapePoint tapeList tapeList_length tapeList_ofFn)
open Zkc.Polynomial (coordinates coordinates_ofFn)

structure Objects (Id : Type) where
  first : Id
  second : Id
  third : Id
  deriving Repr, DecidableEq

structure Values (F : Type) where
  first : F
  second : F
  third : F
  deriving Repr, DecidableEq

structure Claim (Id F : Type) (n : Nat) where
  object : Id
  point : Fin n → F
  value : F

abbrev Bundle (Id F : Type) (n : Nat) := List (Claim Id F n)

variable {Id F S : Type} {n : Nat} [CommRing F]

def factors (env : Id → Table F n) (objects : Objects Id) : Factors F n :=
  ⟨env objects.first, env objects.second, env objects.third⟩

def bundle (objects : Objects Id) (point : Fin n → F) (values : Values F) : Bundle Id F n :=
  [⟨objects.first, point, values.first⟩, ⟨objects.second, point, values.second⟩,
    ⟨objects.third, point, values.third⟩]

def AllHold (env : Id → Table F n) (claims : Bundle Id F n) : Prop :=
  ∀ claim ∈ claims, (env claim.object).eval claim.point = claim.value

theorem allHold_append (env : Id → Table F n) (a b : Bundle Id F n) :
    AllHold env (a ++ b) ↔ AllHold env a ∧ AllHold env b := by
  simp only [AllHold, List.mem_append, or_imp, forall_and]

theorem bundle_holds (env : Id → Table F n) (objects : Objects Id)
    (point : Fin n → F) (values : Values F) :
    AllHold env (bundle objects point values) ↔
      (env objects.first).eval point = values.first ∧
      (env objects.second).eval point = values.second ∧
      (env objects.third).eval point = values.third := by
  simp [AllHold, bundle]

variable [DecidableEq F]

def close (objects : Objects Id) (acc : Source.Accumulator F) (values : Values F) :
    Outcome (Bundle Id F n) :=
  if acc.challenges.length = n then
    if values.first * values.second * values.third = acc.claim then
      .returned (bundle objects (coordinates n acc.challenges) values)
    else .stopped .reject
  else .stopped .refused

theorem close_returned (objects : Objects Id) (acc : Source.Accumulator F)
    (values : Values F) (claims : Bundle Id F n) :
    close objects acc values = .returned claims ↔
      acc.challenges.length = n ∧ values.first * values.second * values.third = acc.claim ∧
      bundle objects (coordinates n acc.challenges) values = claims := by
  unfold close
  split <;> simp_all
  split <;> simp_all

/-- Truth of every returned obligation, not just the product check, is needed. -/
theorem close_sound (env : Id → Table F n) (objects : Objects Id)
    (acc : Source.Accumulator F) (values : Values F) (claims : Bundle Id F n)
    (returned : close objects acc values = .returned claims) (holds : AllHold env claims) :
    acc.claim = (factors env objects).eval (coordinates n acc.challenges) := by
  obtain ⟨_, checked, same⟩ := (close_returned objects acc values claims).mp returned
  subst claims
  obtain ⟨ha, hb, hc⟩ := (bundle_holds env objects _ values).mp holds
  simpa only [factors, Factors.eval, ha, hb, hc] using checked.symm

def run (send : S → Message F × S) (react : S → F → S)
    (report : S → Source.Accumulator F → Values F × S) (objects : Objects Id)
    (count : Nat) (claim : F) (state : S) (coins : List F) :
    PIR.Execution (S × List F) (Execution.Event F) (Bundle Id F count) :=
  (Execution.run send react count claim state coins).follow fun acc state =>
    let (values, next) := report state.1 acc
    ⟨close objects acc values, (next, state.2),
      [.openingValues [values.first, values.second, values.third]]⟩

/-- Identify the actual prefix return from a successful joined execution. -/
theorem run_returned (send : S → Message F × S) (react : S → F → S)
    (report : S → Source.Accumulator F → Values F × S) (objects : Objects Id)
    (count : Nat) (claim : F) (state : S) (coins : List F) (claims : Bundle Id F count)
    (returned : (run send react report objects count claim state coins).outcome = .returned claims) :
    ∃ acc, (Execution.run send react count claim state coins).outcome = .returned acc ∧
      close objects acc (report (Execution.run send react count claim state coins).state.1 acc).1 =
        .returned claims := by
  unfold run at returned
  cases h : (Execution.run send react count claim state coins).outcome with
  | stopped reason => simp [PIR.Execution.follow, h] at returned
  | returned acc => exact ⟨acc, rfl, by simpa only [PIR.Execution.follow, h] using returned⟩

theorem returned_true_implies_verify (env : Id → Table F n) (objects : Objects Id)
    (send : S → Message F × S) (react : S → F → S)
    (report : S → Source.Accumulator F → Values F × S)
    (claim : F) (state : S) (coins : Tape F n) (claims : Bundle Id F n)
    (returned : (run send react report objects n claim state (tapeList n coins)).outcome = .returned claims)
    (holds : AllHold env claims) :
    Rounds.verify (factors env objects) claim (Execution.strategy send react n state) coins = true := by
  obtain ⟨acc, sourceResult, closed⟩ := run_returned send react report objects n claim state _ claims returned
  have truth := close_sound env objects acc _ claims closed holds
  rw [Execution.source_outcome] at sourceResult
  cases h : Execution.finalClaim (Execution.strategy send react n state) claim coins with
  | none => simp [h] at sourceResult
  | some value =>
      simp only [h, Outcome.returned.injEq] at sourceResult
      subst acc
      simp only [tapeList_ofFn, coordinates_ofFn] at truth
      rw [Execution.verify_iff_final, h, truth]

/-- A perfect logical terminal contract is one option; probabilistic PCS
soundness is handled by the separate error-event theorem in `Security`. -/
theorem terminal_sound (env : Id → Table F n) (objects : Objects Id)
    (send : S → Message F × S) (react : S → F → S)
    (report : S → Source.Accumulator F → Values F × S)
    (claim : F) (state : S) (coins : Tape F n) (claims : Bundle Id F n)
    (returned : (run send react report objects n claim state (tapeList n coins)).outcome = .returned claims)
    (verify : Bundle Id F n → PIR.Continuation.Terminal Unit)
    (contract : PIR.Relation.TerminalContract (AllHold env) verify)
    (accepted : verify claims = .accepted ()) :
    Rounds.verify (factors env objects) claim (Execution.strategy send react n state) coins = true :=
  returned_true_implies_verify env objects send react report claim state coins claims returned
    (contract.sound claims () accepted)

end Examples.OpeningReduction.Openings
