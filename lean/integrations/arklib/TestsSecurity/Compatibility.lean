import ArkLib.ProofSystem.Sumcheck.Interaction.ComputableSoundness

open OracleComp
open scoped ENNReal

theorem uniform_guess_probability (guess : Fin 7) :
    Pr{let challenge ← $ᵗ (Fin 7)}[challenge = guess] = (7 : ENNReal)⁻¹ := by
  simpa using SampleableType.prEvent_uniformSample_eq_singleton guess

open Interaction.Oracle Sumcheck.Interaction.MultivariateRound

theorem computable_sumcheck_bound
    (n degree : Nat) (F : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [BEq F] [LawfulBEq F]
    {m : Nat} (domain : Fin m ↪ F)
    (count start : Nat) (finish : start + count = n) (queries : PFunctor)
    (original : VirtualOracle (OracleSpec.ofPFunctor queries) (polynomialFamily F n degree))
    (statement : Sumcheck.Spec.StatementRound F n ⟨start, by omega⟩)
    (handler : QueryImpl (OracleSpec.ofPFunctor queries) Id)
    (prover : Prover.Strategy unifSpec
      (Sumcheck.Interaction.Computable.protocol F degree count).tree
      (Sumcheck.Interaction.Computable.protocol F degree count).roles (fun _ => Unit))
    (polynomial : Sumcheck.Spec.OracleStatement F n degree ())
    (realizes : original.eval handler =
      (polynomialFamily F n degree).behaviorOfRealizations (fun _ => polynomial))
    (falseClaim : ¬ closedRelation F n degree domain ⟨start, by omega⟩
      ⟨statement, original.eval handler⟩) :
    Pr{let result ← (Sumcheck.Interaction.Computable.execute F n degree unifSpec
      ($ᵗ F) (Finset.univ.map domain).toList count start finish queries original
      statement handler prover)}[
        result.map (Sumcheck.Interaction.Native.outputRelation F n degree) = some True] ≤
      (count : ENNReal) * degree / Fintype.card F := by
  exact Sumcheck.Interaction.Computable.execute_soundness n degree F domain count start
    finish queries original statement handler prover polynomial realizes falseClaim

#print axioms uniform_guess_probability
#print axioms computable_sumcheck_bound
