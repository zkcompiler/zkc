import ZkcArkLib.Sumcheck.Multilinear
import Tests.MultilinearSumcheck

/-! Regression and nonvacuity controls. Numeric examples use kernel reduction;
the probability bounds quantify over arbitrary ordinary effectful strategies. -/

namespace TestsSecurity.MultilinearSumcheck


open Zkc.Polynomial.Multilinear Zkc.Protocols.Sumcheck.Multilinear
open ZkcSecurity.ArkLib.Sumcheck.Multilinear
open _root_.Interaction.Oracle OracleSpec OracleComp
open _root_.Sumcheck.Interaction
open scoped ENNReal

def orderedTable : Table ℚ 2 := ofVector ![0, 1, 2, 3]

example : (message ((1, 5) : ℚ × ℚ)).val.eval 2 = 9 := by
  rw [message_evaluate]
  decide +kernel

example : (message ((1, 5) : ℚ × ℚ)).val.eval 2 ≠ 1 + 5 * 2 := by
  rw [message_evaluate]
  decide +kernel

example : (message ((0, 1) : ZMod 2 × ZMod 2)).val.eval 1 = 1 := message_one _

example (q : SingleRound.Message (ZMod 2) 1) : message (endpoints q) = q := message_endpoints q

example : MvPolynomial.eval ![2, 3] (statement orderedTable) = 7 := by
  rw [statement_evaluate]
  decide +kernel

example : MvPolynomial.eval ![3, 2] (statement orderedTable) = 8 := by
  rw [statement_evaluate]
  decide +kernel

example : MvPolynomial.eval ![2] (statement (fixFirst orderedTable 3)) = 8 := by
  rw [statement_fixFirst, statement_evaluate]
  decide +kernel

example : extension 1 (sumRemaining 1 1 orderedTable) ![2] = 9 := by
  rw [extension_sumRemaining]
  decide +kernel

example : extension 2 orderedTable ![2, 0] = 4 := by decide +kernel

example : ResidualClaim 1 orderedTable ![2] 9 := by unfold ResidualClaim; decide +kernel

example : check [0, 1, 2, 3] ![(2 : ℚ)] 9 = false := by decide +kernel

example : booleanSum (sumRemaining 2 0 orderedTable) = 6 := by
  rw [booleanSum_sumRemaining]
  decide +kernel

local instance : Fact (Nat.Prime 97) := ⟨by decide⟩

-- Every class premise of the quantitative theorem is inhabited together.
example : letI := SampleableType.ofFintype (ZMod 97)
    ∀ prover : EndpointProver (F := ZMod 97) unifSpec 1,
      Pr{let accepted ← experiment (fun _ => 0) 1 prover}[accepted] ≤
        1 / (97 : ENNReal) := by
  let := SampleableType.ofFintype (ZMod 97)
  intro prover
  simpa only [Nat.cast_one, ZMod.card, Nat.cast_ofNat] using
    soundness (fun _ : Fin 1 → Bool => (0 : ZMod 97)) 1 prover (by decide +kernel)

/-- Reuse the foundation's F97 challenge-before-message attack through the
actual polynomial adapter; its pair is chosen after seeing this same `r`. -/
example (r : ZMod 97) (different : r ≠ 49) :
    boundary (r / (2 * r - 1), (r - 1) / (2 * r - 1)) = 1 ∧
      (message (r / (2 * r - 1), (r - 1) / (2 * r - 1))).val.eval r = 0 := by
  rw [message_evaluate]
  exact MultilinearSumcheckTests.earlyChallenge_F97 r different

example (pair : Message (ZMod 97)) (valid : boundary pair = 1) :
    (message pair).val.eval 49 = 49 := by
  rw [message_evaluate]
  exact MultilinearSumcheckTests.earlyChallenge_exception pair valid

def oneRound {F : Type} [CommRing F] {ι : Type} (ambient : OracleSpec ι)
    (pair : Message F) (onAbort : OracleComp ambient Unit) : EndpointProver (F := F) ambient 1 :=
  pure ⟨pair, fun
    | none => onAbort
    | some _ => pure ()⟩

/-- Even an effectful abort response is retained, and the supplied challenge
computation is absent from the failed-boundary branch. -/
theorem rejection_keeps_abort {F : Type} [CommRing F] [Nontrivial F] [DecidableEq F]
    {ι : Type} (ambient : OracleSpec ι) (challenge : OracleComp ambient F)
    (pair : Message F) (claim : F) (failed : boundary pair ≠ claim)
    (onAbort : OracleComp ambient Unit) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F 1 1))
    (impl : QueryImpl (ofPFunctor A) Id) :
    Native.Core.execute F 1 1 (Message F) evaluate ambient challenge booleanDomain 1 0 rfl
      A original ⟨claim, Fin.elim0⟩ impl (oneRound ambient pair onAbort) =
      (do let _ ← onAbort; return none) := by
  rw [execute_round]
  simp only [oneRound, pure_bind, failed, ite_false]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A constant zero challenge lets a fixed causal pair prove the false sum 1
of the zero table. Thus guard order alone cannot replace fresh uniform draws. -/
theorem nonuniform_false_accepts {F : Type} [CommRing F] [Nontrivial F] [DecidableEq F] :
    (do let result ← Native.Core.execute F 1 1 (Message F) evaluate unifSpec (pure 0)
          booleanDomain 1 0 rfl (MultivariateRound.polynomialFamily F 1 1).spec.toPFunctor
          (VirtualOracle.id (MultivariateRound.polynomialFamily F 1 1)) ⟨1, Fin.elim0⟩
          ((MultivariateRound.polynomialFamily F 1 1).behaviorOfRealizations
            (fun _ => oracleStatement (fun _ => 0)))
          (oneRound unifSpec (0, 1) (pure ()))
        return result.map (Native.outputRelation F 1 1) = some True) =
      (pure True : ProbComp Prop) := by
  rw [execute_round]
  simp only [oneRound, pure_bind, boundary, zero_add, ite_true, evaluate,
    sub_zero, one_mul, zero_mul, add_zero, Native.Core.execute_zero]
  apply congrArg pure
  simp only [Option.map_some, Option.some.injEq, eq_iff_iff, iff_true]
  change _ = (0 : F)
  dsimp only
  rw [VirtualOracle.eval_sumWeaken_extendImpl
    (MultivariateRound.polynomialFamily F 1 1).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F 1 1))
    (Native.Core.messageInterface F (Message F) evaluate)
    ((MultivariateRound.polynomialFamily F 1 1).behaviorOfRealizations
      (fun _ => oracleStatement (fun _ => 0))) (0, 1)]
  change MvPolynomial.eval _ (statement (fun _ : Fin 1 → Bool => (0 : F))) = 0
  rw [statement_evaluate]
  simp [extension]

example {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (table : Table F 0) (claim : F) (wrong : claim ≠ booleanSum table) :
    Pr{let accepted ← experiment table claim ()}[accepted] ≤ 0 := by
  simpa only [Nat.cast_zero, ENNReal.zero_div] using soundness table claim () wrong

set_option backward.isDefEq.respectTransparency false in
/-- False-initial is essential: a true singleton claim accepts with certainty,
whereas the putative zero-round soundness bound is zero. -/
example {F : Type} [Field F] [DecidableEq F] [SampleableType F] (value : F) :
    experiment (fun _ : Fin 0 → Bool => value) value () = (pure True : ProbComp Prop) := by
  unfold experiment
  rw [Native.Core.execute_zero]
  simp only [pure_bind, Option.map_some, Option.some.injEq, eq_iff_iff, iff_true]
  apply congrArg pure
  apply propext
  change MvPolynomial.eval _ (statement (fun _ : Fin 0 → Bool => value)) = value ↔ True
  rw [statement_evaluate]
  exact iff_true_intro rfl

/-- A strategy may sample privately before choosing its pair and in its abort
continuation. It remains inside the quantified soundness theorem. -/
example {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (table : Table F 1) (claim : F) (wrong : claim ≠ booleanSum table) :
    Pr{let accepted ← (experiment table claim
      (do let r ← $ᵗ F
          return ⟨(r, claim - r), fun
            | none => do let _ ← $ᵗ F; return ()
            | some _ => do let _ ← $ᵗ F; return ()⟩))}[accepted] ≤
      1 / (Fintype.card F : ENNReal) := by
  simpa only [Nat.cast_one] using soundness table claim _ wrong

end TestsSecurity.MultilinearSumcheck
