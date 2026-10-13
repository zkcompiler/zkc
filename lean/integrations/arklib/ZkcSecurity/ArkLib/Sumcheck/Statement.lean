module

public import ZkcSecurity.ArkLib.Sumcheck.Message
public import ArkLib.ProofSystem.Sumcheck.Domain

@[expose] public section

namespace ZkcSecurity.ArkLib.Sumcheck
open Zkc.Protocols.AlgebraicRounds
open Zkc.Protocols.Sumcheck.Common
open MvPolynomial

variable {F : Type} [Field F]

noncomputable def row (coefficients : Message F) : MvPolynomial (Fin 2) F :=
  C coefficients.constant + C coefficients.linear * X 1 + C coefficients.quadratic * X 1 ^ 2

noncomputable def statement (coefficients : Coefficients F) : MvPolynomial (Fin 2) F :=
  row coefficients.constant + X 0 * row coefficients.linear + X 0 ^ 2 * row coefficients.quadratic

theorem row_degree (coefficients : Message F) (i : Fin 2) :
    (row coefficients).degreeOf i ≤ if i = 1 then 2 else 0 := by
  unfold row
  apply (degreeOf_add_le _ _ _).trans
  apply max_le
  · apply (degreeOf_add_le _ _ _).trans
    apply max_le
    · simp
    · apply (degreeOf_C_mul_le _ _ _).trans
      simp only [degreeOf_X]
      split_ifs <;> decide
  · apply (degreeOf_C_mul_le _ _ _).trans
    apply (degreeOf_pow_le _ _ _).trans
    simp only [degreeOf_X]
    split_ifs <;> decide

theorem statement_degree (coefficients : Coefficients F) (i : Fin 2) :
    (statement coefficients).degreeOf i ≤ 2 := by
  unfold statement
  apply (degreeOf_add_le _ _ _).trans
  apply max_le
  · apply (degreeOf_add_le _ _ _).trans
    apply max_le
    · exact (row_degree _ _).trans (by split_ifs <;> decide)
    · apply (degreeOf_mul_le _ _ _).trans
      apply (Nat.add_le_add_left (row_degree _ _) _).trans
      fin_cases i <;> simp [degreeOf_X]
  · apply (degreeOf_mul_le _ _ _).trans
    apply (Nat.add_le_add (degreeOf_pow_le _ _ _) (row_degree _ _)).trans
    fin_cases i <;> simp [degreeOf_X]

noncomputable def oracleStatement (coefficients : Coefficients F) :
    _root_.Sumcheck.Spec.OracleStatement F 2 2 () :=
  ⟨statement coefficients, (mem_restrictDegree_iff_sup (Fin 2) _ _).mpr (fun i => by rw [← degreeOf_def]; exact statement_degree coefficients i)⟩

theorem statement_evaluate (coefficients : Coefficients F) (first second : F) :
    MvPolynomial.eval ![first, second] (statement coefficients) = evaluate coefficients first second := by
  simp only [statement, row, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, MvPolynomial.eval_pow, Matrix.cons_val_zero, Matrix.cons_val_one,
    evaluate, wireEvaluate]
  ring

end ZkcSecurity.ArkLib.Sumcheck
