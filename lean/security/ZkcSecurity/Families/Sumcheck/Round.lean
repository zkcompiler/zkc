module

public import ZkcSecurity.Families.Sumcheck.Reference
public import ZkcSecurity.Algebra.Polynomial
public import VCVio.EvalDist.ProbabilityBounds

@[expose] public section

/-! Honest equality and arbitrary-message escape use the same reference laws.
The local uniform theorem fixes the state and message before drawing a fresh
challenge. Actual conditional distributions and causal execution are supplied
by clients; no native sampler or Fiat–Shamir assertion is made here. -/

set_option autoImplicit false

namespace ZkcSecurity.Families.Sumcheck

open Polynomial OracleComp OracleSpec
open ZkcSecurity.Algebra.Polynomial
open scoped ENNReal

variable {F : Type} [Field F]
variable {reference : Reference F} {message : Message F}
variable {referenceDegree messageDegree n : Nat}

/-- Completeness algebra for an actually delivered message. Successful producer
execution and delivery are additional obligations of the implementation. -/
theorem honest_round (referenceLaws : ReferenceLaws reference referenceDegree)
    (messageLaws : MessageLaws message messageDegree)
    (s : reference.State (n + 1)) (allowed : reference.admissible s)
    (m : message.Carrier) (delivered : message.polynomial m = reference.polynomial s)
    (proverChallenge verifierChallenge : F) (challengeDelivered : proverChallenge = verifierChallenge) :
    message.boundary m = reference.total s ∧
      message.evaluate m verifierChallenge = reference.total (reference.restrict s proverChallenge) ∧
      reference.admissible (reference.restrict s proverChallenge) := by
  subst proverChallenge
  exact ⟨by rw [messageLaws.boundary_eq, delivered, referenceLaws.boundary_eq s allowed],
    by rw [messageLaws.evaluate_eq, delivered, referenceLaws.evaluation_eq s _ allowed],
    referenceLaws.restriction_closed s _ allowed⟩

/-- A passed check on a false claim forces different polynomials. This does not
assume the attacker followed any producer or supplied an honest message. -/
theorem checked_polynomial_ne (referenceLaws : ReferenceLaws reference referenceDegree)
    (messageLaws : MessageLaws message messageDegree)
    (s : reference.State (n + 1)) (allowed : reference.admissible s)
    (claim : F) (wrong : claim ≠ reference.total s) (m : message.Carrier)
    (checked : message.boundary m = claim) :
    message.polynomial m ≠ reference.polynomial s := by
  intro same
  apply wrong
  rw [← checked, messageLaws.boundary_eq, same, referenceLaws.boundary_eq s allowed]

theorem escape_iff (referenceLaws : ReferenceLaws reference referenceDegree)
    (messageLaws : MessageLaws message messageDegree)
    (s : reference.State (n + 1)) (allowed : reference.admissible s)
    (m : message.Carrier) (r : F) :
    (message.evaluate m r = reference.total (reference.restrict s r)) ↔
      (message.polynomial m).eval r = (reference.polynomial s).eval r := by
  rw [messageLaws.evaluate_eq, referenceLaws.evaluation_eq s r allowed]

/-- Outside the collision event, falsehood and admissibility are both preserved. -/
theorem false_round (referenceLaws : ReferenceLaws reference referenceDegree)
    (messageLaws : MessageLaws message messageDegree)
    (s : reference.State (n + 1)) (allowed : reference.admissible s)
    (m : message.Carrier) (r : F)
    (noCollision : (message.polynomial m).eval r ≠ (reference.polynomial s).eval r) :
    message.evaluate m r ≠ reference.total (reference.restrict s r) ∧
      reference.admissible (reference.restrict s r) :=
  ⟨fun escaped => noCollision ((escape_iff referenceLaws messageLaws s allowed m r).mp escaped),
    referenceLaws.restriction_closed s r allowed⟩

/-- Transport a proved bound for the actual conditional challenge distribution.
The distribution premise is an obligation, never an authorized assumption or a
substitute for freshness. It need not be uniform or lossless. -/
theorem escape_probability_le (referenceLaws : ReferenceLaws reference referenceDegree)
    (messageLaws : MessageLaws message messageDegree)
    (s : reference.State (n + 1)) (allowed : reference.admissible s)
    (m : message.Carrier) (challenge : ProbComp F) (error : ℝ≥0∞)
    (collisionBound : Pr{let r ← challenge}[
      (message.polynomial m).eval r = (reference.polynomial s).eval r] ≤ error) :
    Pr{let r ← challenge}[message.evaluate m r = reference.total (reference.restrict s r)] ≤
      error :=
  (prEvent_congr challenge _ _ (escape_iff referenceLaws messageLaws s allowed m)).trans_le
    collisionBound

/-- Actual-distribution soundness from a sampling theorem for unequal bounded
polynomials. This quantifies the sampling premise independently of any target
or honest producer; a client discharges it in the actual conditional history. -/
theorem escape_actual_le (referenceLaws : ReferenceLaws reference referenceDegree)
    (messageLaws : MessageLaws message messageDegree)
    (s : reference.State (n + 1)) (allowed : reference.admissible s)
    (claim : F) (wrong : claim ≠ reference.total s) (m : message.Carrier)
    (checked : message.boundary m = claim) (challenge : ProbComp F) (error : ℝ≥0∞)
    (sampling : ∀ p q : Polynomial F, p ≠ q → p.natDegree ≤ messageDegree →
      q.natDegree ≤ referenceDegree → Pr{let r ← challenge}[p.eval r = q.eval r] ≤ error) :
    Pr{let r ← challenge}[message.evaluate m r = reference.total (reference.restrict s r)] ≤
      error :=
  escape_probability_le referenceLaws messageLaws s allowed m challenge error
    (sampling _ _
      (checked_polynomial_ne referenceLaws messageLaws s allowed claim wrong m checked)
      (messageLaws.degree_le m) (referenceLaws.degree_le s allowed))

/-- Local soundness for every admitted attacker message fixed before the fresh
uniform draw. Reference truth and honest-message equality are absent. If both
degrees are at most `d`, `max d d = d` gives the usual `d / |F|` charge. -/
theorem escape_uniform_le [Fintype F] [DecidableEq F] [SampleableType F]
    (referenceLaws : ReferenceLaws reference referenceDegree)
    (messageLaws : MessageLaws message messageDegree)
    (s : reference.State (n + 1)) (allowed : reference.admissible s)
    (claim : F) (wrong : claim ≠ reference.total s) (m : message.Carrier)
    (checked : message.boundary m = claim) :
    Pr{let r ← $ᵗ F}[message.evaluate m r = reference.total (reference.restrict s r)] ≤
      ((max messageDegree referenceDegree : Nat) : ℝ≥0∞) / Fintype.card F :=
  escape_actual_le referenceLaws messageLaws s allowed claim wrong m checked ($ᵗ F) _
    (fun p q different left right => agreement_uniform_le p q different left right)

omit [Field F] in
/-- Two bad events on one challenge are charged by a union bound. Sharing a
challenge supplies no justification for replacing this sum by a maximum. -/
theorem shared_challenge_union_le (challenge : ProbComp F) (left right : F → Prop)
    (leftError rightError : ℝ≥0∞)
    (leftBound : Pr{let r ← challenge}[left r] ≤ leftError)
    (rightBound : Pr{let r ← challenge}[right r] ≤ rightError) :
    Pr{let r ← challenge}[left r ∨ right r] ≤ leftError + rightError :=
  (prEvent_or_le challenge left right).trans (add_le_add leftBound rightBound)

end ZkcSecurity.Families.Sumcheck
