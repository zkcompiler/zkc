import ArkLib.OracleReduction.OracleInterface
import Zkc.Protocols.Sumcheck.Polynomial

/-! The selected coefficient messages expose the same scalar evaluation query
as ArkLib's actual polynomial OracleInterface. This is an answer correspondence,
not an identification of whole Sumcheck reductions or security experiments. -/

set_option autoImplicit false
namespace ZkcArkLib.Mathematical
open Zkc.Protocols.AlgebraicRounds Zkc.Protocols.Sumcheck

variable {F : Type} [CommSemiring F]

theorem round_query_answer (message : Message F) (point : F) :
    OracleInterface.answer (messagePolynomial message) point = message.evaluate point :=
  messagePolynomial_eval message point

/-- An explicit service identity remains outside the point query. Sharing that
identity shares its handler; a polynomial query shape alone does not supply
capability permissions, initialization or state independence. -/
structure EvaluationRequest (Identity F : Type) (n : Nat) where
  service : Identity
  point : Fin n → F

noncomputable def polynomialAnswer {Identity : Type} {n : Nat}
    (polynomials : Identity → MvPolynomial (Fin n) F) (request : EvaluationRequest Identity F n) : F :=
  OracleInterface.answer (polynomials request.service) request.point

theorem polynomial_query_answer {Identity : Type} {n : Nat}
    (polynomials : Identity → MvPolynomial (Fin n) F) (request : EvaluationRequest Identity F n) :
    polynomialAnswer polynomials request =
      MvPolynomial.eval request.point (polynomials request.service) := rfl

end ZkcArkLib.Mathematical
