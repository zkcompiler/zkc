module

public import ZkcArkLib.Sumcheck.Multilinear.Protocol
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolSoundness

@[expose] public section

/-! Interactive soundness for a fixed public table and arbitrary causal,
effectful endpoint strategies. Fresh uniform verifier draws occur only after
the boundary guard. The terminal relation uses the exact original table. -/

namespace ZkcSecurity.ArkLib.Sumcheck.Multilinear

open Zkc.Polynomial.Multilinear Zkc.Protocols.Sumcheck.Multilinear
open _root_.Interaction.Oracle OracleSpec OracleComp
open _root_.Sumcheck.Interaction
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F] {n : Nat}

/-- Any original interface/handler that realizes this table at every point.
The adversary is an unrestricted ordinary native strategy, not a finite list
of transcripts or a preselected deterministic message function. -/
theorem soundness_of_oracle (table : Table F n) (claim : F) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n 1))
    (impl : QueryImpl (ofPFunctor A) Id) (prover : EndpointProver (F := F) unifSpec n)
    (answers : ∀ point, original.eval impl ⟨(), point⟩ = extension n table point)
    (falseClaim : claim ≠ booleanSum table) :
    Pr{let result ← (Native.Core.execute F n 1 (Message F) evaluate unifSpec ($ᵗ F)
      booleanDomain n 0 (Nat.zero_add n) A original ⟨claim, Fin.elim0⟩ impl prover)}[
        result.map (Native.outputRelation F n 1) = some True] ≤
      (n : ENNReal) / Fintype.card F := by
  have realized := oracle_realized table A original impl answers
  have falseRelation : ¬ MultivariateRound.closedRelation F n 1 (boolEmbedding F) 0
      ⟨⟨claim, Fin.elim0⟩, original.eval impl⟩ := by
    rw [realized, closed_statement]
    exact Ne.symm falseClaim
  rw [execute_transport unifSpec n ($ᵗ F) booleanDomain n 0 (Nat.zero_add n)
    A A original original ⟨claim, Fin.elim0⟩ impl impl prover rfl]
  simpa only [booleanDomain, Nat.cast_one, mul_one] using
    Native.execute_soundness n 1 F (boolEmbedding F) n 0 (Nat.zero_add n) A original
      ⟨claim, Fin.elim0⟩ impl (polynomialProver unifSpec n prover) (oracleStatement table)
      realized falseRelation

/-- Concrete public-table experiment. The verifier's statement and original
oracle are fixed arguments; prover effects and fresh challenge queries use
VCVio's normalized uniform oracle specification. -/
noncomputable def experiment (table : Table F n) (claim : F)
    (prover : EndpointProver (F := F) unifSpec n) : ProbComp Prop := do
  let result ← Native.Core.execute F n 1 (Message F) evaluate unifSpec ($ᵗ F)
    booleanDomain n 0 (Nat.zero_add n) (MultivariateRound.polynomialFamily F n 1).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F n 1)) ⟨claim, Fin.elim0⟩
    ((MultivariateRound.polynomialFamily F n 1).behaviorOfRealizations
      (fun _ => oracleStatement table)) prover
  return result.map (Native.outputRelation F n 1) = some True

theorem soundness (table : Table F n) (claim : F)
    (prover : EndpointProver (F := F) unifSpec n) (falseClaim : claim ≠ booleanSum table) :
    Pr{let accepted ← experiment table claim prover}[accepted] ≤
      (n : ENNReal) / Fintype.card F := by
  have bound := soundness_of_oracle table claim
    (MultivariateRound.polynomialFamily F n 1).spec.toPFunctor
    (VirtualOracle.id (MultivariateRound.polynomialFamily F n 1))
    ((MultivariateRound.polynomialFamily F n 1).behaviorOfRealizations
      (fun _ => oracleStatement table)) prover
    (fun point => statement_evaluate table point) falseClaim
  simpa only [experiment, bind_assoc, pure_bind] using bound

/-- The same bound for the actual checked raw-vector observation. Shape and
all-point oracle agreement are explicit; malformed vectors cannot pass check. -/
theorem publicTable_soundness_of_oracle (table : Table F n) (values : List F)
    (decoded : ofList? n values = some table) (claim : F) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n 1))
    (impl : QueryImpl (ofPFunctor A) Id) (prover : EndpointProver (F := F) unifSpec n)
    (answers : ∀ point, original.eval impl ⟨(), point⟩ = extension n table point)
    (falseClaim : claim ≠ values.sum) :
    Pr{let result ← (Native.Core.execute F n 1 (Message F) evaluate unifSpec ($ᵗ F)
      booleanDomain n 0 (Nat.zero_add n) A original ⟨claim, Fin.elim0⟩ impl prover)}[
        result.map (fun (output : ClosedClaim (Native.FinalStatement F n)
          (MultivariateRound.polynomialFamily F n 1)) =>
            check values output.stmt.challenges output.stmt.target) = some true] ≤
      (n : ENNReal) / Fintype.card F := by
  have bound := soundness_of_oracle table claim A original impl prover answers
    (by rwa [booleanSum_ofList? values table decoded])
  change 𝒟[do let result ← Native.Core.execute F n 1 (Message F) evaluate unifSpec ($ᵗ F)
                booleanDomain n 0 (Nat.zero_add n) A original ⟨claim, Fin.elim0⟩ impl prover
              return result.map (fun (output : ClosedClaim (Native.FinalStatement F n)
                (MultivariateRound.polynomialFamily F n 1)) =>
                check values output.stmt.challenges output.stmt.target) = some true] {True} ≤ _
  rw [← publicTable_observation unifSpec table values decoded ($ᵗ F)
    n 0 (Nat.zero_add n) A original ⟨claim, Fin.elim0⟩ impl prover answers]
  exact bound

/-- Public-table checking with the canonical table oracle. The caller supplies
only exact shape, a false original sum and an arbitrary causal strategy. -/
theorem publicTable_soundness (table : Table F n) (values : List F)
    (decoded : ofList? n values = some table) (claim : F)
    (prover : EndpointProver (F := F) unifSpec n) (falseClaim : claim ≠ values.sum) :
    Pr{let result ← (Native.Core.execute F n 1 (Message F) evaluate unifSpec ($ᵗ F)
      booleanDomain n 0 (Nat.zero_add n) (MultivariateRound.polynomialFamily F n 1).spec.toPFunctor
      (VirtualOracle.id (MultivariateRound.polynomialFamily F n 1)) ⟨claim, Fin.elim0⟩
      ((MultivariateRound.polynomialFamily F n 1).behaviorOfRealizations
        (fun _ => oracleStatement table)) prover)}[
      result.map (fun (output : ClosedClaim (Native.FinalStatement F n)
        (MultivariateRound.polynomialFamily F n 1)) =>
        check values output.stmt.challenges output.stmt.target) = some true] ≤
      (n : ENNReal) / Fintype.card F :=
  publicTable_soundness_of_oracle table values decoded claim _ _ _ prover
    (fun point => statement_evaluate table point) falseClaim

end ZkcSecurity.ArkLib.Sumcheck.Multilinear
