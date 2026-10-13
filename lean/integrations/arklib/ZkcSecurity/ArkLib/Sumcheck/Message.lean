module

public import Zkc.Protocols.Sumcheck.Common.Program
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolSoundness

@[expose] public section

namespace ZkcSecurity.ArkLib.Sumcheck
open Zkc.Protocols.AlgebraicRounds
open Zkc.Protocols.Sumcheck.Common
open Polynomial

variable {F : Type} [Field F]

noncomputable def messagePolynomial (message : Message F) : Polynomial F :=
  C message.constant + C message.linear * X + C message.quadratic * X ^ 2

theorem messagePolynomial_degree (message : Message F) :
    (messagePolynomial message).degree ≤ 2 := by
  unfold messagePolynomial
  apply degree_add_le_of_degree_le
  · apply degree_add_le_of_degree_le
    · exact degree_C_le.trans (by decide)
    · exact (degree_C_mul_X_le _).trans (by decide)
  · exact degree_C_mul_X_pow_le 2 _

noncomputable def message (source : Message F) :
    _root_.Sumcheck.Interaction.SingleRound.Message F 2 :=
  ⟨messagePolynomial source, Polynomial.mem_degreeLE.mpr (messagePolynomial_degree source)⟩

theorem message_evaluate (source : Message F) (point : F) :
    (message source).val.eval point = wireEvaluate source point := by
  simp only [message, messagePolynomial, eval_add, eval_mul, eval_C, eval_X, eval_pow,
    wireEvaluate]
  ring

end ZkcSecurity.ArkLib.Sumcheck
