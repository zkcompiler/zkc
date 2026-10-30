import ZkcArkLibExamples.Variants
import ZkcArkLib.Sumcheck.Multilinear

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

open ZkcSecurity.VCVio.Execution
open ZkcSecurity.ArkLib.Sumcheck.Multilinear.Causal

/-- The causal phase API is independent of source example bodies. -/
theorem stoppedPhaseBound {F S E : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {n : Nat} (table : Table F n) (claim : F)
    (phases : Causal.Strategy F S E n) (s : S) (wrong : claim ≠ booleanSum table) :
    mass (phaseGame n claim [] phases s (tableTerminal table)) ≤
      (n : ENNReal) / Fintype.card F := phase_soundness table claim phases s wrong

theorem stoppedResidualBound {F S E : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] {remaining rounds : Nat} (table : Table F (remaining + rounds))
    (claim : F) (phases : Causal.Strategy F S E rounds) (s : S)
    (wrong : claim ≠ booleanSum table) :
    mass (phaseGame rounds claim [] phases s (residualTerminal remaining rounds table)) ≤
      (rounds : ENNReal) / Fintype.card F := residual_phase_soundness table claim phases s wrong

/-- Local full-state suffix laws compose with equivalent prefixes, requiring
nothing at states outside the supported invariant. -/
theorem reachableSuffixConsumer {S E A B : Type}
    {p q : ProbComp (PIR.Execution S E A)} (same : SameDist p q)
    (invariant : A → S → Prop) (left right : A → Phase S E B)
    (reachable : Reaches p invariant)
    (law : ∀ a s, invariant a s → SameDist (left a s) (right a s)) :
    SameDist (p >>= fun e => e.followM left) (q >>= fun e => e.followM right) :=
  same.follow_congr invariant left right reachable law
