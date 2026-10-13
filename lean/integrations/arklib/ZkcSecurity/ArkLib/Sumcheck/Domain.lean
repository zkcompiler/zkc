module

public import ZkcSecurity.ArkLib.Sumcheck.Statement
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProjectionTransport

@[expose] public section

namespace ZkcSecurity.ArkLib.Sumcheck
open Zkc.Protocols.AlgebraicRounds Zkc.Protocols.Sumcheck.Common
open _root_.Sumcheck.Interaction
open scoped BigOperators

variable {F : Type} [Field F]

noncomputable def booleanDomain : List F := (Finset.univ.map (boolEmbedding F)).toList

theorem booleanDomain_sum (q : Message F) :
    ((booleanDomain (F := F)).map (wireEvaluate q)).sum = wireBoundary q := by
  have bridge := Multiset.sum_map_toList (Finset.univ.map (boolEmbedding F)).1 (wireEvaluate q)
  change _ = ∑ a ∈ Finset.univ.map (boolEmbedding F), wireEvaluate q a at bridge
  apply bridge.trans
  simp only [Finset.sum_map, Fin.sum_univ_two, boolEmbedding_zero, boolEmbedding_one,
    wireEvaluate, wireBoundary]
  ring

/-- The Boolean sum is a statement interpretation obligation, independent of
any verifier or prover strategy. -/
theorem statement_sum (coefficients : Coefficients F) :
    (∑ point ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ 2,
      MvPolynomial.eval point (statement coefficients)) =
      (polynomial coefficients).booleanSum := by
  rw [_root_.Sumcheck.Interaction.SingleRound.sum_cube_cons F _ 1]
  simp_rw [_root_.Sumcheck.Interaction.SingleRound.sum_cube_cons F _ 0]
  simp [Finset.sum_map, Fin.sum_univ_two, Zkc.Polynomial.Quadratic.booleanSum,
    Zkc.Polynomial.cubeSum, polynomial, rowPolynomial, Zkc.Polynomial.Quadratic.eval,
    statement, row, boolEmbedding_zero, boolEmbedding_one, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_pow]

end ZkcSecurity.ArkLib.Sumcheck
