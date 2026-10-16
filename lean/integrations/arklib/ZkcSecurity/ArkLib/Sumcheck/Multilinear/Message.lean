module

public import Zkc.Protocols.Sumcheck.Multilinear.Round
public import ArkLib.ProofSystem.Sumcheck.Interaction.Protocol
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

@[expose] public section

/-! Endpoint messages are values at zero and one, not monomial coefficients. -/

namespace ZkcSecurity.ArkLib.Sumcheck.Multilinear

open Zkc.Protocols.Sumcheck.Multilinear
open Polynomial

variable {F : Type} [CommRing F]

noncomputable def messagePolynomial (endpoints : Message F) : Polynomial F :=
  C endpoints.1 + C (endpoints.2 - endpoints.1) * X

theorem messagePolynomial_degree (endpoints : Message F) :
    (messagePolynomial endpoints).degree ≤ 1 := by
  apply degree_add_le_of_degree_le
  · exact degree_C_le.trans (by decide)
  · exact degree_C_mul_X_le _

noncomputable def message (endpoints : Message F) :
    _root_.Sumcheck.Interaction.SingleRound.Message F 1 :=
  ⟨messagePolynomial endpoints, mem_degreeLE.mpr (messagePolynomial_degree endpoints)⟩

theorem message_evaluate (endpoints : Message F) (point : F) :
    (message endpoints).val.eval point = evaluate endpoints point := by
  simp only [message, messagePolynomial, eval_add, eval_mul, eval_C, eval_X, evaluate]
  ring

theorem message_zero (endpoints : Message F) : (message endpoints).val.eval 0 = endpoints.1 := by
  rw [message_evaluate, evaluate_zero]

theorem message_one (endpoints : Message F) : (message endpoints).val.eval 1 = endpoints.2 := by
  rw [message_evaluate, evaluate_one]

theorem message_boundary (endpoints : Message F) :
    (message endpoints).val.eval 0 + (message endpoints).val.eval 1 = boundary endpoints := by
  rw [message_zero, message_one]
  rfl

/-- Every degree-one message is determined by its endpoints, in every
characteristic. This reverse interpretation is useful for honest strategies. -/
noncomputable def endpoints (polynomial : _root_.Sumcheck.Interaction.SingleRound.Message F 1) :
    Message F := (polynomial.val.eval 0, polynomial.val.eval 1)

theorem endpoints_evaluate (polynomial : _root_.Sumcheck.Interaction.SingleRound.Message F 1)
    (point : F) : evaluate (endpoints polynomial) point = polynomial.val.eval point := by
  have linear := eq_X_add_C_of_degree_le_one (mem_degreeLE.mp polynomial.property)
  unfold endpoints evaluate
  rw [linear]
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add, mul_one]
  ring

theorem endpoints_message (pair : Message F) : endpoints (message pair) = pair := by
  simp only [endpoints, message_zero, message_one]

theorem message_endpoints (polynomial : _root_.Sumcheck.Interaction.SingleRound.Message F 1) :
    message (endpoints polynomial) = polynomial := by
  apply Subtype.ext
  have linear := eq_X_add_C_of_degree_le_one (mem_degreeLE.mp polynomial.property)
  change messagePolynomial (endpoints polynomial) = polynomial.val
  unfold messagePolynomial endpoints
  rw [linear]
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_zero, zero_add, mul_one,
    add_sub_cancel_right]
  exact add_comm _ _

end ZkcSecurity.ArkLib.Sumcheck.Multilinear
