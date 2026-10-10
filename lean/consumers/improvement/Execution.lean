import Improvement.Claims
import Zkc.Semantics.Interaction

/-! An executable cubic verifier prefix returning explicit opening obligations.

Messages precede the challenge; the program sees reported scalar values only.
Returning a bundle is not terminal cryptographic acceptance. The receipt theorem
connects this prefix to the algebraic contracts in Claims.
-/

set_option autoImplicit false

namespace Improvement.Execution

open PIR
open Improvement.Claims

structure Message (F : Type) where
  constant : F
  linear : F
  quadratic : F
  cubic : F

def parse {F : Type} : List F → Option (Message F)
  | [a, b, c, d] => some ⟨a, b, c, d⟩
  | _ => none

def Message.words {F : Type} (m : Message F) : List F :=
  [m.constant, m.linear, m.quadratic, m.cubic]

def Message.eval {F : Type} [Semiring F] (m : Message F) (r : F) : F :=
  m.constant + (m.linear + (m.quadratic + m.cubic * r) * r) * r

noncomputable def Message.polynomial {F : Type} [CommSemiring F] (m : Message F) : Polynomial F :=
  Polynomial.C m.constant +
    (Polynomial.C m.linear +
      (Polynomial.C m.quadratic + Polynomial.C m.cubic * Polynomial.X) * Polynomial.X) * Polynomial.X

theorem Message.evaluation_law {F : Type} [CommSemiring F] (m : Message F) (r : F) :
    m.polynomial.eval r = m.eval r := by
  simp only [Message.polynomial, Message.eval, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

theorem Message.degree_law {F : Type} [CommSemiring F] (m : Message F) :
    m.polynomial.natDegree ≤ 3 := by
  have step {p : Polynomial F} {n : Nat} (a : F) (h : p.natDegree ≤ n) :
      (Polynomial.C a + p * Polynomial.X).natDegree ≤ n + 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le (by simp)
    exact Polynomial.natDegree_mul_le_of_le h Polynomial.natDegree_X_le
  exact step (n := 2) m.constant
    (step (n := 1) m.linear (step (n := 0) m.quadratic (by simp)))

inductive Op where
  | message
  | challenge
  | values
  deriving DecidableEq

def interface (F : Type) : Signature where
  Op := Op
  Reply
    | .message | .values => List F
    | .challenge => F

def program {Id F : Type} [Semiring F] [DecidableEq F] (a b c : Id) (sum : F) :
    Proc (interface F) (List (Claim (Object Id) (fun _ => F) F)) :=
  .call .message fun raw =>
    match parse raw with
    | none => .halt .refused
    | some message =>
      if message.eval 0 + message.eval 1 = sum then
        .call .challenge fun r =>
          .call .values fun payload =>
            match payload with
            | [x, y, z] =>
              if x * y * z = message.eval r then .done (openings a b c r x y z)
              else .halt .reject
            | _ => .halt .refused
      else .halt .reject

/-- Uniform over every supplied message, challenge and opening payload. -/
theorem within_three {Id F : Type} [Semiring F] [DecidableEq F]
    (a b c : Id) (sum : F) : Within 3 (program a b c sum) := by
  simp only [program, Within]
  intro raw
  split
  · trivial
  · split
    · intro r payload
      dsimp only
      split
      · split <;> trivial
      · trivial
    · trivial

/-- The fixture handler records operation order and counts delivered challenges.
It retains failure events and leaves an exhausted challenge undelivered. -/
def handler {F : Type} (raw : List F) (coin : Option F) (values : List F) :
    Handler (interface F) Nat Op
  | .message, count => ⟨.returned raw, count, [.message]⟩
  | .values, count => ⟨.returned values, count, [.values]⟩
  | .challenge, count => match coin with
    | none => ⟨.stopped .exhausted, count, [.challenge]⟩
    | some r => ⟨.returned r, count + 1, [.challenge]⟩

/-- Exact execution characterization with the actual supplied message and values.
No environment of private polynomials is supplied to the program or handler. -/
theorem receipt_iff {Id F : Type} [Semiring F] [DecidableEq F]
    (a b c : Id) (sum : F) (m : Message F) (r x y z : F) (count : Nat) :
    (program a b c sum).run (handler m.words (some r) [x, y, z]) count =
        ⟨.returned (openings a b c r x y z), count + 1, [.message, .challenge, .values]⟩ ↔
      m.eval 0 + m.eval 1 = sum ∧ x * y * z = m.eval r := by
  by_cases boundary : m.eval 0 + m.eval 1 = sum <;>
    by_cases product : x * y * z = m.eval r <;>
      simp [program, Message.words, parse, Proc.run, handler, Execution.follow, boundary, product]

/-- A successful actual prefix supplies both checks of the composed reduction.
Its residual list is the exact returned list, and still needs terminal discharge. -/
theorem receipt_contract {Id F : Type} [Field F] [DecidableEq F]
    (env : Id → Polynomial F) (a b c : Id) (sum : F) (m : Message F) (r x y z : F)
    (receipt : (program a b c sum).run (handler m.words (some r) [x, y, z]) 0 =
      ⟨.returned (openings a b c r x y z), 1, [.message, .challenge, .values]⟩) :
    PIR.Relation.ReductionContract
      (fun s => booleanSum (productPolynomial env a b c) = s)
      (AllHold (evaluate env)) sum (openings a b c r x y z)
      (Collision (productPolynomial env a b c) m.polynomial r ∨ False) := by
  have checks := (receipt_iff a b c sum m r x y z 0).mp receipt
  apply composed_reduction
  · exact ⟨m.degree_law, by simpa only [booleanSum, Message.evaluation_law] using checks.1⟩
  · simpa only [productCheck, decide_eq_true_eq, Message.evaluation_law] using checks.2

def cubic : Message Nat := ⟨0, 2, 3, 1⟩

theorem successful_cubic_prefix :
    (program 0 1 2 6).run (handler cubic.words (some 2) [2, 3, 4]) 0 =
      ⟨.returned (openings 0 1 2 2 2 3 4), 1, [.message, .challenge, .values]⟩ := by rfl

theorem boundary_failure_preserves_challenge :
    (program 0 1 2 7).run (handler cubic.words (some 2) [2, 3, 4]) 0 =
      ⟨.stopped .reject, 0, [.message]⟩ := by rfl

theorem malformed_message_preserves_challenge :
    (program 0 1 2 6).run (handler ([0, 2, 3] : List Nat) (some 2) [2, 3, 4]) 0 =
      ⟨.stopped .refused, 0, [.message]⟩ := by rfl

theorem rejects_trailing_coefficient :
    (program 0 1 2 6).run (handler ([0, 2, 3, 1, 0] : List Nat) (some 2) [2, 3, 4]) 0 =
      ⟨.stopped .refused, 0, [.message]⟩ := by rfl

theorem missing_opening_retains_consumed_challenge :
    (program 0 1 2 6).run (handler cubic.words (some 2) [2, 3]) 0 =
      ⟨.stopped .refused, 1, [.message, .challenge, .values]⟩ := by rfl

theorem wrong_opening_retains_consumed_challenge :
    (program 0 1 2 6).run (handler cubic.words (some 2) [2, 3, 5]) 0 =
      ⟨.stopped .reject, 1, [.message, .challenge, .values]⟩ := by rfl

theorem exhausted_challenge_is_distinct :
    (program 0 1 2 6).run (handler cubic.words none [2, 3, 4]) 0 =
      ⟨.stopped .exhausted, 0, [.message, .challenge]⟩ := by rfl

end Improvement.Execution
