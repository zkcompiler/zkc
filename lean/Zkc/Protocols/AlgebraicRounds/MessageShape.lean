import Mathlib.Algebra.Ring.Defs

set_option autoImplicit false

namespace Zkc.Protocols.AlgebraicRounds.MessageShape
structure PublicIndex where
  fieldName : String
  instanceName : String
  dimension : Nat
  degree : Fin dimension → Nat

-- Protocol legality carries shape only. In particular there is no endpoint-sum
-- equality, truth of a claim, or honest degree refinement in this type.
structure Scalar (fieldName : String) (F : Type) where
  value : F

structure LegalMessage (p : PublicIndex) (F : Type) (round : Fin p.dimension) where
  coefficients : Fin (p.degree round + 1) → Scalar p.fieldName F

theorem every_coefficients_legal (p : PublicIndex) (F : Type)
    (round : Fin p.dimension) (a : Fin (p.degree round + 1) → F) :
    ∃ m : LegalMessage p F round, ∀ i, (m.coefficients i).value = a i :=
  ⟨⟨fun i => ⟨a i⟩⟩, fun _ => rfl⟩


-- A Plan's proved equation permits replacement inside any pure consumer.
-- This does NOT grant the equation for messages supplied by an open strategy.
theorem honest_endpoint_substitution {F : Type} [CommRing F]
    (a b d claim : F) (k : F → F) (h : 2*a+b+d = claim) :
    k (2*a+b+d) = k claim := congrArg k h

end Zkc.Protocols.AlgebraicRounds.MessageShape
