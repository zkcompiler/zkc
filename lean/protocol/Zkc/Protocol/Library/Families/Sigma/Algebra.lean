module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Ring.Defs

@[expose] public section

/-! Honest Sigma equations, independent of source layout, encodings and
probability. The same module law applies to independent witnesses and a shared
challenge. Freshness and the actual sampler are separate execution obligations. -/
set_option autoImplicit false
namespace ZkcSecurity.Families.Sigma

variable {K H : Type} [CommRing K] [AddCommGroup H] [Module K H]

/-- The installed source sends nonce + challenge * witness. Scalar
commutativity aligns that operand order with the verifier's group action. -/
theorem response_equation (base : H) (witness nonce challenge : K) :
    (nonce + challenge * witness) • base = nonce • base + challenge • (witness • base) := by
  rw [add_smul, mul_smul]

/-- A retained discrete-log relation supplies precisely the public point
needed by the verifier equation; nonce and challenge are arbitrary. -/
theorem honest_equation (base point : H) (witness nonce challenge : K)
    (related : point = witness • base) :
    (nonce + challenge * witness) • base = nonce • base + challenge • point := by
  rw [related, response_equation]

/-- Independent witnesses and private nonces share the actual public challenge. -/
theorem and_equation (firstBase firstPoint secondBase secondPoint : H)
    (firstWitness secondWitness firstNonce secondNonce challenge : K)
    (firstRelated : firstPoint = firstWitness • firstBase)
    (secondRelated : secondPoint = secondWitness • secondBase) :
    (firstNonce + challenge * firstWitness) • firstBase =
      firstNonce • firstBase + challenge • firstPoint ∧
    (secondNonce + challenge * secondWitness) • secondBase =
      secondNonce • secondBase + challenge • secondPoint :=
  ⟨honest_equation _ _ _ _ _ firstRelated, honest_equation _ _ _ _ _ secondRelated⟩

end ZkcSecurity.Families.Sigma
