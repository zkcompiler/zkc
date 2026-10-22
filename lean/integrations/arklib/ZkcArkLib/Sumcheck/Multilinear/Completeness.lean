module

public import ZkcArkLib.Sumcheck.Multilinear.Protocol
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolCompleteness

@[expose] public section

namespace ZkcSecurity.ArkLib.Sumcheck.Multilinear

open Zkc.Polynomial.Multilinear Zkc.Protocols.Sumcheck.Multilinear
open _root_.Interaction.Oracle OracleSpec OracleComp
open _root_.Sumcheck.Interaction
open scoped BigOperators

variable {F : Type} [CommRing F] [Nontrivial F] {n : Nat}

/-- The first projected polynomial is exactly the ordered residual sum after
fixing the first coordinate, for every challenge. -/
theorem projected_first_evaluate (table : Table F (n + 1)) (r : F) :
    (_root_.Sumcheck.Spec.SingleRound.projectedRoundPolynomial F (n + 1) 1
      (boolEmbedding F) 0 Fin.elim0 (oracleStatement table)).val.eval r =
      booleanSum (fixFirst table r) := by
  rw [SingleRound.projectedRoundPolynomial_eval F n 1 (boolEmbedding F) 0 Fin.elim0
    (oracleStatement table) r]
  change (∑ rest ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ n,
    MvPolynomial.eval (Fin.append (Fin.snoc Fin.elim0 r) rest ∘ Fin.cast (by omega))
      (statement table)) = _
  have joined (rest : Fin n → F) :
      Fin.append (Fin.snoc Fin.elim0 r) rest ∘ Fin.cast (by omega) = Fin.cons r rest := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.append, Fin.snoc, Fin.addCases]
    congr 1
  simp_rw [joined, statement_evaluate, ← extension_fixFirst]
  rw [domain_sum, cubeSum_extension]

theorem projected_first_endpoints (table : Table F (n + 1)) :
    endpoints (_root_.Sumcheck.Spec.SingleRound.projectedRoundPolynomial F (n + 1) 1
      (boolEmbedding F) 0 Fin.elim0 (oracleStatement table)) = honestMessage table := by
  simp only [endpoints, projected_first_evaluate, fixFirst_zero, fixFirst_one, honestMessage]

/-- Honest endpoints are extracted from upstream's actual projected-polynomial
prover at its actual public prefix. No intermediate truth premises are inputs. -/
noncomputable def honestProver {ι : Type} (ambient : OracleSpec ι) (table : Table F n) :
    EndpointProver (F := F) ambient n :=
  Native.Core.transportProver F (SingleRound.Message F 1) (fun q x => q.val.eval x) ambient
    (Message F) evaluate endpoints n
    (Native.honestProver F n 1 (boolEmbedding F) ambient n 0 (Nat.zero_add n)
      ⟨booleanSum table, Fin.elim0⟩ (oracleStatement table))

variable {ι : Type} (ambient : OracleSpec ι) [DecidableEq F]

/-- Arbitrary table, arbitrary challenge computation: every supported honest
result is a true original-table evaluation. Zero rounds are included. -/
theorem support_completeness (table : Table F n) (challenge : OracleComp ambient F)
    (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n 1))
    (impl : QueryImpl (ofPFunctor A) Id)
    (answers : ∀ point, original.eval impl ⟨(), point⟩ = extension n table point) :
    ∀ result ∈ support (Native.Core.execute F n 1 (Message F) evaluate ambient challenge
      booleanDomain n 0 (Nat.zero_add n) A original ⟨booleanSum table, Fin.elim0⟩ impl
      (honestProver ambient table)), result.map (Native.outputRelation F n 1) = some True := by
  unfold honestProver
  rw [← Native.Core.execute_transport F n 1 (SingleRound.Message F 1)
    (fun q x => q.val.eval x) ambient (Message F) evaluate endpoints challenge booleanDomain
    n 0 (Nat.zero_add n) A A original original ⟨booleanSum table, Fin.elim0⟩ impl impl
    (Native.honestProver F n 1 (boolEmbedding F) ambient n 0 (Nat.zero_add n)
      ⟨booleanSum table, Fin.elim0⟩ (oracleStatement table)) endpoints_evaluate rfl]
  apply Native.execute_support_completeness F n 1 (boolEmbedding F) ambient challenge
    n 0 (Nat.zero_add n) A original ⟨booleanSum table, Fin.elim0⟩ impl (oracleStatement table)
    (oracle_realized table A original impl answers)
  rw [oracle_realized table A original impl answers]
  exact (closed_statement table (booleanSum table)).mpr rfl

omit ambient in
theorem perfectCompleteness (table : Table F n) (challenge : ProbComp F) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n 1))
    (impl : QueryImpl (ofPFunctor A) Id)
    (answers : ∀ point, original.eval impl ⟨(), point⟩ = extension n table point) :
    Pr{let result ← (Native.Core.execute F n 1 (Message F) evaluate unifSpec challenge
      booleanDomain n 0 (Nat.zero_add n) A original ⟨booleanSum table, Fin.elim0⟩ impl
      (honestProver unifSpec table))}[result.map (Native.outputRelation F n 1) = some True] = 1 :=
  prEvent_eq_one_of_forall_mem_support _ _
    (support_completeness unifSpec table challenge A original impl answers)

end ZkcSecurity.ArkLib.Sumcheck.Multilinear
