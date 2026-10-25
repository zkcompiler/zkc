module

public import Zkc.Protocols.Sumcheck.Polynomial
public import Zkc.Protocols.Sumcheck.Multilinear.Round

@[expose] public section

/-! Polynomial meanings of wire messages. Endpoint values and coefficients
have different decoders, even when their host representations look alike. -/

set_option autoImplicit false

namespace ZkcSecurity.Families.Sumcheck

open Polynomial

variable {F : Type} [Field F]

def boundaryPoly (p : Polynomial F) : F := p.eval 0 + p.eval 1

/-- Explicit wire operations; law proofs do not select an implementation. -/
structure Message (F : Type) [Field F] where
  Carrier : Type
  polynomial : Carrier → Polynomial F
  boundary : Carrier → F
  evaluate : Carrier → F → F

/-- All inhabitants are admitted attacker messages. A partial wire decoder must
separately prove that every successfully received value has this meaning. -/
structure MessageLaws (message : Message F) (degree : Nat) : Prop where
  degree_le : ∀ m, (message.polynomial m).natDegree ≤ degree
  boundary_eq : ∀ m, message.boundary m = boundaryPoly (message.polynomial m)
  evaluate_eq : ∀ m r, message.evaluate m r = (message.polynomial m).eval r

namespace Message

noncomputable def endpointPolynomial (m : F × F) : Polynomial F :=
  C m.1 + C (m.2 - m.1) * X

theorem endpointPolynomial_eval (m : F × F) (r : F) :
    (endpointPolynomial m).eval r =
      Zkc.Protocols.Sumcheck.Multilinear.evaluate m r := by
  rw [Zkc.Protocols.Sumcheck.Multilinear.evaluate_affine]
  simp only [endpointPolynomial, eval_add, eval_mul, eval_C, eval_X]
  ring

theorem endpointPolynomial_degree (m : F × F) :
    (endpointPolynomial m).natDegree ≤ 1 := by
  apply natDegree_add_le_of_degree_le
  · simp
  · exact (natDegree_C_mul_le _ _).trans natDegree_X_le

/-- The two entries are values at zero and one, not coefficients. -/
noncomputable abbrev endpoints (F : Type) [Field F] : Message F where
  Carrier := F × F
  polynomial := endpointPolynomial
  boundary := Zkc.Protocols.Sumcheck.Multilinear.boundary
  evaluate := Zkc.Protocols.Sumcheck.Multilinear.evaluate

theorem endpoints_laws : MessageLaws (endpoints F) 1 where
  degree_le := endpointPolynomial_degree
  boundary_eq := by
    change ∀ m : F × F, m.1 + m.2 = (endpointPolynomial m).eval 0 + (endpointPolynomial m).eval 1
    intro m
    rw [endpointPolynomial_eval, endpointPolynomial_eval,
      Zkc.Protocols.Sumcheck.Multilinear.evaluate_zero,
      Zkc.Protocols.Sumcheck.Multilinear.evaluate_one]
  evaluate_eq m r := (endpointPolynomial_eval m r).symm

/-- Coefficient order is constant, linear, quadratic. The evaluator is the
existing core evaluator; Horner implementations need their own equality to it. -/
noncomputable abbrev coefficients (F : Type) [Field F] : Message F where
  Carrier := Zkc.Protocols.AlgebraicRounds.Message F
  polynomial := Zkc.Protocols.Sumcheck.messagePolynomial
  boundary := Zkc.Protocols.AlgebraicRounds.Message.boundary
  evaluate := Zkc.Protocols.AlgebraicRounds.Message.evaluate

theorem coefficients_laws : MessageLaws (coefficients F) 2 where
  degree_le := Zkc.Protocols.Sumcheck.messagePolynomial_degree
  boundary_eq := by
    change ∀ m : Zkc.Protocols.AlgebraicRounds.Message F,
      m.boundary = (Zkc.Protocols.Sumcheck.messagePolynomial m).eval 0 +
        (Zkc.Protocols.Sumcheck.messagePolynomial m).eval 1
    intro m
    rw [Zkc.Protocols.Sumcheck.messagePolynomial_eval, Zkc.Protocols.Sumcheck.messagePolynomial_eval]
    rfl
  evaluate_eq m r := (Zkc.Protocols.Sumcheck.messagePolynomial_eval m r).symm

/-- A plain nested triple is decoded in the declared coefficient order. -/
def ofTriple (m : F × F × F) : Zkc.Protocols.AlgebraicRounds.Message F :=
  ⟨m.1, m.2.1, m.2.2⟩

noncomputable abbrev coefficientTriples (F : Type) [Field F] : Message F where
  Carrier := F × F × F
  polynomial m := (coefficients F).polynomial (ofTriple m)
  boundary m := (coefficients F).boundary (ofTriple m)
  evaluate m r := (coefficients F).evaluate (ofTriple m) r

theorem coefficientTriples_laws : MessageLaws (coefficientTriples F) 2 where
  degree_le m := coefficients_laws.degree_le (ofTriple m)
  boundary_eq m := coefficients_laws.boundary_eq (ofTriple m)
  evaluate_eq m r := coefficients_laws.evaluate_eq (ofTriple m) r

end Message
end ZkcSecurity.Families.Sumcheck
