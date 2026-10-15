import ZkcSecurity.Examples.Variants
import ZkcSecurity.ArkLib.Sumcheck.Multilinear

/-! Independent reuse across imported source forms and external consumers. -/
noncomputable def importedSumcheckSoundness := @ZkcSecurity.Examples.Variants.sumcheck
noncomputable def importedSchnorrSimulation := @ZkcSecurity.Examples.Variants.schnorr

open Zkc.Polynomial.Multilinear ZkcSecurity.ArkLib.Sumcheck.Multilinear
open OracleComp
open scoped ENNReal BigOperators

/-- A standalone consumer fixes any MSB-ordered table and an arbitrary causal
effectful endpoint prover; no source-import or oracle-realization axiom is needed. -/
theorem importedMultilinearBound {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {n : Nat} (values : Fin (2 ^ n) → F) (claim : F)
    (prover : EndpointProver (F := F) unifSpec n) (wrong : claim ≠ ∑ i, values i) :
    Pr{let accepted ← experiment (ofVector values) claim prover}[accepted] ≤
      (n : ENNReal) / Fintype.card F :=
  soundness (ofVector values) claim prover (by rwa [booleanSum_ofVector])

/-- Partial reduction discharges a residual sum, with exactly the sent prefix. -/
theorem importedResidualBound {F : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {remaining rounds : Nat} (table : Table F (remaining + rounds))
    (claim : F) (prover : EndpointProver (F := F) unifSpec rounds)
    (wrong : claim ≠ booleanSum table) :
    Pr{let related ← reductionExperiment table claim prover}[related] ≤
      (rounds : ENNReal) / Fintype.card F := residual_soundness table claim prover wrong
