module

public import Zkc.Polynomial.Multilinear.Prefix
public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.ProofSystem.Sumcheck.Domain
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProjectionTransport

@[expose] public section

/-! The existing MSB table, embedded using explicit Boolean assignments.
No flat-index convention from upstream `MLE'` is used. -/

namespace ZkcSecurity.ArkLib.Sumcheck.Multilinear

open Zkc.Polynomial.Multilinear
open scoped BigOperators

variable {F : Type} [CommRing F] {n : Nat}

/-- Pointwise conversion only; coordinate positions are unchanged. -/
def booleanAssignment (point : Fin n → Fin 2) : Fin n → Bool :=
  fun i => decide (point i = 1)

theorem booleanAssignment_cons (first : Fin 2) (rest : Fin n → Fin 2) :
    booleanAssignment ((Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)) (first, rest)) =
      Fin.cons (decide (first = 1)) (booleanAssignment rest) := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

noncomputable def statement (table : Table F n) : MvPolynomial (Fin n) F :=
  MvPolynomial.MLE (fun point => table (booleanAssignment point))

theorem statement_degree (table : Table F n) :
    statement table ∈ MvPolynomial.restrictDegree (Fin n) F 1 :=
  MvPolynomial.MLE_mem_restrictDegree _

noncomputable def oracleStatement (table : Table F n) :
    _root_.Sumcheck.Spec.OracleStatement F n 1 () := ⟨statement table, statement_degree table⟩

theorem statement_evaluate (table : Table F n) (point : Fin n → F) :
    MvPolynomial.eval point (statement table) = extension n table point := by
  induction n with
  | zero =>
      simp only [statement, MvPolynomial.MLE_eval, MvPolynomial.eqTilde_eq_prod,
        Finset.univ_eq_empty, Finset.prod_empty, one_mul, Fintype.sum_unique, extension]
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      rw [statement, MvPolynomial.MLE_eval,
        ← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)).sum_comp]
      rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      simp only [Fin.consEquiv_apply, MvPolynomial.eqTilde_eq_prod, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one,
        zero_mul, sub_zero, one_mul, sub_self, zero_add, add_zero]
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [extension]
      congr 1 <;> congr 1
      · rw [← ih]
        simp [statement, MvPolynomial.MLE_eval, MvPolynomial.eqTilde_eq_prod,
          booleanAssignment_cons, Function.comp_def]
      · rw [← ih]
        simp [statement, MvPolynomial.MLE_eval, MvPolynomial.eqTilde_eq_prod,
          booleanAssignment_cons, Function.comp_def]

theorem statement_fixFirst (table : Table F (n + 1)) (first : F) (rest : Fin n → F) :
    MvPolynomial.eval rest (statement (fixFirst table first)) =
      MvPolynomial.eval (Fin.cons first rest) (statement table) := by
  simp only [statement_evaluate, extension_fixFirst]

theorem statement_fixPrefix {remaining : Nat} (count : Nat)
    (table : Table F (remaining + count)) (fixed : Fin count → F) (rest : Fin remaining → F) :
    MvPolynomial.eval rest (statement (fixPrefix count table fixed)) =
      MvPolynomial.eval (Zkc.Polynomial.Quadratic.point count fixed rest) (statement table) := by
  simp only [statement_evaluate, extension_fixPrefix]

variable [Nontrivial F]

/-- The upstream Boolean domain is injective even in characteristic two. -/
theorem domain_sum (f : (Fin n → F) → F) :
    (∑ point ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ n, f point) =
      Zkc.Polynomial.cubeSum n f := by
  classical
  induction n with
  | zero =>
      simp [Zkc.Polynomial.cubeSum]
      congr 1
  | succ n ih =>
      rw [_root_.Sumcheck.Interaction.SingleRound.sum_cube_cons F _ n]
      simp only [Finset.sum_map, Fin.sum_univ_two, boolEmbedding_zero,
        boolEmbedding_one, ih, Zkc.Polynomial.cubeSum]

theorem statement_sum (table : Table F n) :
    (∑ point ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ n,
      MvPolynomial.eval point (statement table)) = booleanSum table := by
  simp_rw [statement_evaluate]
  rw [domain_sum, cubeSum_extension]

theorem statement_sum_ofVector (values : Fin (2 ^ n) → F) :
    (∑ point ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ n,
      MvPolynomial.eval point (statement (ofVector values))) = ∑ i, values i := by
  rw [statement_sum, booleanSum_ofVector]

end ZkcSecurity.ArkLib.Sumcheck.Multilinear
