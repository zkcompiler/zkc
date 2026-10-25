module

public import ZkcSecurity.Families.Sumcheck.Message

@[expose] public section

/-! A mathematical reference exists independently of the current scalar claim
and of honest execution. Its index counts remaining rounds. Root anchoring and
the meaning of a terminal state remain caller obligations. -/

set_option autoImplicit false

namespace ZkcSecurity.Families.Sumcheck

variable {F : Type} [Field F]

structure Reference (F : Type) [Field F] where
  State : Nat → Type
  total : {n : Nat} → State n → F
  restrict : {n : Nat} → State (n + 1) → F → State n
  polynomial : {n : Nat} → State (n + 1) → Polynomial F
  admissible : {n : Nat} → State n → Prop

structure ReferenceLaws (reference : Reference F) (degree : Nat) : Prop where
  degree_le : ∀ {n} (s : reference.State (n + 1)), reference.admissible s →
    (reference.polynomial s).natDegree ≤ degree
  boundary_eq : ∀ {n} (s : reference.State (n + 1)), reference.admissible s →
    boundaryPoly (reference.polynomial s) = reference.total s
  evaluation_eq : ∀ {n} (s : reference.State (n + 1)) r, reference.admissible s →
    (reference.polynomial s).eval r = reference.total (reference.restrict s r)
  restriction_closed : ∀ {n} (s : reference.State (n + 1)) r, reference.admissible s →
    reference.admissible (reference.restrict s r)

namespace Reference

/-- Every challenge prefix of the indicated length is permitted mathematically;
no message, target-truth or future-challenge premise occurs here. -/
def restrictPrefix (reference : Reference F) {n : Nat} :
    (count : Nat) → reference.State (n + count) → (Fin count → F) → reference.State n
  | 0, s, _ => s
  | count + 1, s, challenges =>
      reference.restrictPrefix count (reference.restrict s (challenges 0))
        (challenges ∘ Fin.succ)

theorem admissible_restrictPrefix {reference : Reference F} {degree n : Nat}
    (laws : ReferenceLaws reference degree) (count : Nat)
    (s : reference.State (n + count)) (challenges : Fin count → F)
    (allowed : reference.admissible s) :
    reference.admissible (reference.restrictPrefix count s challenges) := by
  induction count with
  | zero => exact allowed
  | succ count ih =>
      exact ih (reference.restrict s (challenges 0)) (challenges ∘ Fin.succ)
        (laws.restriction_closed s (challenges 0) allowed)

/-- Update simulation must preserve observations after every future restriction.
Initial-sum equality alone cannot supply these hypotheses. -/
theorem restrictPrefix_total_eq {left right : Reference F}
    (represent : {n : Nat} → left.State n → right.State n)
    (observation : ∀ {n} (s : left.State n),
      right.total (represent s) = left.total s)
    (update : ∀ {n} (s : left.State (n + 1)) r,
      represent (left.restrict s r) = right.restrict (represent s) r)
    {n : Nat} (count : Nat) (s : left.State (n + count)) (challenges : Fin count → F) :
    right.total (right.restrictPrefix count (represent s) challenges) =
      left.total (left.restrictPrefix count s challenges) := by
  induction count with
  | zero => exact observation s
  | succ count ih =>
      simp only [restrictPrefix, ← update]
      exact ih (left.restrict s (challenges 0)) (challenges ∘ Fin.succ)

end Reference
end ZkcSecurity.Families.Sumcheck
