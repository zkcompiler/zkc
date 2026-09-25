import Zkc.Polynomial.Layout

/-! The fixed-table, honest-commitment experiment boundary.

A setup selects a paired prover/verifier key. Commit receives low-bit storage;
check receives an unchanged logical point. All external operations are opaque
parameters, with no assumed cryptographic laws. An instantiation must justify
the adaptive false-opening bound in Security. Setup and commitment randomness,
if any, are part of the selected setup, fixed before the challenge tape.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Committed

open Zkc.Polynomial

/-- An external PCS interface, not an extraction or binding axiom. A concrete
positive-arity PCS may provide this interface only when `0 < n`. -/
structure Scheme (F : Type) (n : Nat) where
  Setup : Type
  ProverKey : Type
  VerifierKey : Type
  Commitment : Type
  Proof : Type
  proverKey : Setup → ProverKey
  verifierKey : Setup → VerifierKey
  commit : ProverKey → (Fin (2 ^ n) → F) → Commitment
  check : VerifierKey → Commitment → (Fin n → F) → F → Proof → Bool

/-- Originals and setup are selected before future verifier coins. Advertised
commitments are derived below, never supplied as arbitrary adversarial values. -/
structure Statement {F : Type} {n : Nat} (scheme : Scheme F n) where
  setup : scheme.Setup
  left : Fin (2 ^ n) → F
  right : Fin (2 ^ n) → F

variable {F : Type} {n : Nat} {scheme : Scheme F n}

def Statement.leftCommitment (statement : Statement scheme) : scheme.Commitment :=
  scheme.commit (scheme.proverKey statement.setup) (Layout.toLowStorage statement.left)

def Statement.rightCommitment (statement : Statement scheme) : scheme.Commitment :=
  scheme.commit (scheme.proverKey statement.setup) (Layout.toLowStorage statement.right)

variable [CommRing F]

def Statement.polynomial (statement : Statement scheme) : Quadratic F n :=
  Multilinear.productCoefficients n (Multilinear.ofVector statement.left)
    (Multilinear.ofVector statement.right)

def Statement.leftValue (statement : Statement scheme) (point : Fin n → F) : F :=
  Multilinear.extension n (Multilinear.ofVector statement.left) point

def Statement.rightValue (statement : Statement scheme) (point : Fin n → F) : F :=
  Multilinear.extension n (Multilinear.ofVector statement.right) point

theorem Statement.polynomial_eval (statement : Statement scheme) (point : Fin n → F) :
    statement.polynomial.eval point = statement.leftValue point * statement.rightValue point :=
  Multilinear.productCoefficients_eval n _ _ point

/-- The subjects passed to commit denote the same full polynomial used by
Sumcheck. No factor, multiplicity, or coordinate is replaced. -/
theorem Statement.stored_polynomial (statement : Statement scheme) :
    Multilinear.productCoefficients n (Layout.ofLowStorage (Layout.toLowStorage statement.left))
      (Layout.ofLowStorage (Layout.toLowStorage statement.right)) = statement.polynomial :=
  Layout.product_eq statement.left statement.right

end Zkc.Protocols.Sumcheck.Committed
