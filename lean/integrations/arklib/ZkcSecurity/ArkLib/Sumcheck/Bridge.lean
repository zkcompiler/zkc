module

public import ZkcSecurity.ArkLib.Sumcheck.Execution
public import ZkcSecurity.ArkLib.Sumcheck.Strategy

@[expose] public section

namespace ZkcSecurity.ArkLib.Sumcheck
open _root_.Interaction.Oracle OracleSpec OracleComp
open _root_.Sumcheck.Interaction
open Zkc.Protocols.Sumcheck.Common

variable {F : Type} [Field F] [DecidableEq F] [SampleableType F]

noncomputable def nativeAcceptance (domain : List F) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F 2 2))
    (impl : QueryImpl (ofPFunctor A) Id) (claim : F) (prover : Strategy F) : ProbComp Prop := do
  let result ← Native.execute F 2 2 unifSpec ($ᵗ F) domain 2 0 rfl A original
    ⟨claim, Fin.elim0⟩ impl (nativeProver (strategy prover))
  return result.map (Native.outputRelation F 2 2) = some True

set_option backward.isDefEq.respectTransparency false in
theorem native_game (domain : List F) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F 2 2))
    (impl : QueryImpl (ofPFunctor A) Id) (coefficients : Coefficients F)
    (claim : F) (prover : Strategy F)
    (domainSum : ∀ q : Zkc.Protocols.AlgebraicRounds.Message F,
      (domain.map (wireEvaluate q)).sum = wireBoundary q)
    (oracleAnswers : ∀ first second,
      original.eval impl ⟨(), ![first, second]⟩ = evaluate coefficients first second) :
    nativeAcceptance domain A original impl claim prover = game coefficients claim prover := by
  unfold nativeAcceptance
  rw [Native.execute_succ]
  simp only [Native.execute_succ, Native.execute_zero, strategy, nativeProver_send, nativeProver_done, pure_bind,
    domainSum, message_evaluate]
  by_cases firstCheck : wireBoundary prover.first = claim
  · simp only [firstCheck, ite_true, game, bind_assoc]
    apply bind_congr
    intro first
    by_cases secondCheck : wireBoundary (prover.second first) = wireEvaluate prover.first first
    · simp only [secondCheck, ite_true, bind_assoc, pure_bind]
      apply bind_congr
      intro second
      simp only [Native.outputRelation, Native.Core.outputRelation,
        Option.map_some, Option.some.injEq]
      rw [VirtualOracle.eval_sumWeaken_extendImpl
        (Access.extend A (SingleRound.polynomialInterface F 2))
        (original.sumWeaken (SingleRound.polynomialInterface F 2).spec)
        (SingleRound.polynomialInterface F 2)
        (Access.extendImpl A (SingleRound.polynomialInterface F 2) impl (message prover.first))
        (message (prover.second first))]
      rw [VirtualOracle.eval_sumWeaken_extendImpl A original
        (SingleRound.polynomialInterface F 2) impl (message prover.first)]
      congr 1
      apply propext
      rw [eq_iff_iff, iff_true]
      rw [show (Fin.snoc (Fin.snoc Fin.elim0 first) second) = ![first, second] by
        ext i; fin_cases i <;> rfl]
      simp only [Function.comp_def, Fin.cast_eq_self]
      constructor
      · intro accepted
        exact accepted.symm.trans (oracleAnswers first second)
      · intro accepted
        exact (oracleAnswers first second).trans accepted.symm
    · simp [secondCheck]
  · simp [firstCheck, game]

end ZkcSecurity.ArkLib.Sumcheck
