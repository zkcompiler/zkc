module

public import ZkcSecurity.ArkLib.Sumcheck.Multilinear.Soundness
public import ZkcSecurity.ArkLib.Sumcheck.Multilinear.Completeness

@[expose] public section

/-! Partial reduction through the marginal of the same fixed original table.
Summing out the remaining coordinates gives a degree-one polynomial in exactly
the challenged coordinates. Its terminal truth is residual truth, not a full
evaluation of the original table. No additional protocol interpreter is used. -/

namespace ZkcSecurity.ArkLib.Sumcheck.Multilinear

open Zkc.Polynomial.Multilinear Zkc.Protocols.Sumcheck.Multilinear
open _root_.Interaction.Oracle OracleSpec OracleComp
open _root_.Sumcheck.Interaction
open scoped ENNReal

variable {F : Type} {remaining count : Nat}

variable [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- Exactly `count` causal rounds, followed by residual truth for the original
table. The exported oracle is the proved marginal view of that fixed table;
the observed point has `count` coordinates, without padding. -/
noncomputable def reductionExperiment (table : Table F (remaining + count)) (claim : F)
    (prover : EndpointProver (F := F) unifSpec count) : ProbComp Prop := do
  let result ← Native.Core.execute F count 1 (Message F) evaluate unifSpec ($ᵗ F)
    booleanDomain count 0 (Nat.zero_add count)
    (MultivariateRound.polynomialFamily F count 1).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F count 1)) ⟨claim, Fin.elim0⟩
    ((MultivariateRound.polynomialFamily F count 1).behaviorOfRealizations
      (fun _ => oracleStatement (sumRemaining remaining count table))) prover
  return result.map (fun output => ResidualClaim count table
    output.stmt.challenges output.stmt.target) = some True

omit [Fintype F] in
/-- Equality of accepted-event computations, not equality between a residual
claim and a complete evaluation of the original higher-dimensional table. -/
theorem reductionExperiment_eq (table : Table F (remaining + count)) (claim : F)
    (prover : EndpointProver (F := F) unifSpec count) :
    reductionExperiment table claim prover =
      experiment (sumRemaining remaining count table) claim prover := by
  unfold reductionExperiment experiment
  apply bind_congr_of_forall_mem_support
  intro result supported
  cases result with
  | none => rfl
  | some result =>
      have retained := execute_preserves_original unifSpec count ($ᵗ F) booleanDomain
        count 0 (Nat.zero_add count) (MultivariateRound.polynomialFamily F count 1).spec.toPFunctor
        (VirtualOracle.id (MultivariateRound.polynomialFamily F count 1)) ⟨claim, Fin.elim0⟩
        ((MultivariateRound.polynomialFamily F count 1).behaviorOfRealizations
          (fun _ => oracleStatement (sumRemaining remaining count table))) prover result supported
      apply congrArg pure
      apply propext
      simp only [Option.map_some, Option.some.injEq, eq_iff_iff, iff_true]
      change _ ↔ (result.oracles ⟨(), result.stmt.challenges⟩ = result.stmt.target)
      rw [retained]
      change ResidualClaim count table result.stmt.challenges result.stmt.target ↔
        (MvPolynomial.eval result.stmt.challenges
          (statement (sumRemaining remaining count table)) = result.stmt.target)
      simp only [statement_evaluate, Fin.val_last, extension_sumRemaining]
      rfl

theorem residual_soundness (table : Table F (remaining + count)) (claim : F)
    (prover : EndpointProver (F := F) unifSpec count) (falseClaim : claim ≠ booleanSum table) :
    Pr{let related ← reductionExperiment table claim prover}[related] ≤
      (count : ENNReal) / Fintype.card F := by
  rw [reductionExperiment_eq]
  exact soundness (sumRemaining remaining count table) claim prover
    (by rwa [booleanSum_sumRemaining])

omit [Fintype F] in
/-- The marginal honest strategy establishes original-table residual truth
with certainty, including an empty challenged prefix. -/
theorem residual_perfectCompleteness (table : Table F (remaining + count)) :
    Pr{let related ← (reductionExperiment table (booleanSum table)
      (honestProver unifSpec (sumRemaining remaining count table)))}[related] = 1 := by
  rw [reductionExperiment_eq, ← booleanSum_sumRemaining table]
  let marginal := sumRemaining remaining count table
  have complete := perfectCompleteness marginal ($ᵗ F)
    (MultivariateRound.polynomialFamily F count 1).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F count 1))
    ((MultivariateRound.polynomialFamily F count 1).behaviorOfRealizations
      (fun _ => oracleStatement marginal))
    (fun point => statement_evaluate marginal point)
  simpa only [experiment, bind_assoc, pure_bind] using complete

end ZkcSecurity.ArkLib.Sumcheck.Multilinear
