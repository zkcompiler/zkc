module

public import ZkcArkLib.Sumcheck.Multilinear.Message
public import ZkcArkLib.Sumcheck.Multilinear.Table
public import Zkc.Protocols.Sumcheck.Multilinear.Reduction

@[expose] public section

/-! Causal endpoint messages in ArkLib's existing interaction interface.
This is not a zkc native process. The source-facing boundary still has two
ordered scalar receives; message transport compares closed observations. -/

namespace ZkcSecurity.ArkLib.Sumcheck.Multilinear

open Zkc.Polynomial.Multilinear Zkc.Protocols.Sumcheck.Multilinear
open _root_.Interaction.Oracle OracleSpec OracleComp
open _root_.Sumcheck.Interaction
open scoped BigOperators

variable {F : Type} [CommRing F]

abbrev protocol (F : Type) [CommRing F] (count : Nat) :=
  Native.Core.protocol F (Message F) evaluate count

/-- Ordinary strategies may perform ambient effects before selecting a pair,
after receiving a challenge, and in response to public abort. -/
abbrev EndpointProver {ι : Type} (ambient : OracleSpec ι) (count : Nat) :=
  Prover.Strategy ambient (protocol F count).tree (protocol F count).roles (fun _ => Unit)

noncomputable def polynomialProver {ι : Type} (ambient : OracleSpec ι) (count : Nat)
    (prover : EndpointProver (F := F) ambient count) :
    Prover.Strategy ambient (Native.protocol F 1 count).tree
      (Native.protocol F 1 count).roles (fun _ => Unit) :=
  Native.Core.transportProver F (Message F) evaluate ambient (SingleRound.Message F 1)
    (fun q x => q.val.eval x) message count prover

variable {ι : Type} (ambient : OracleSpec ι) [DecidableEq F]

/-- Transport the whole execution, including private continuation and abort
effects. The original view may have a different handler with equal behavior. -/
theorem execute_transport (n : Nat) (challenge : OracleComp ambient F) (domain : List F)
    (count start : Nat) (finish : start + count = n) (A B : PFunctor)
    (viewA : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n 1))
    (viewB : VirtualOracle (ofPFunctor B) (MultivariateRound.polynomialFamily F n 1))
    (stmt : _root_.Sumcheck.Spec.StatementRound F n ⟨start, by omega⟩)
    (implA : QueryImpl (ofPFunctor A) Id) (implB : QueryImpl (ofPFunctor B) Id)
    (prover : EndpointProver (F := F) ambient count)
    (sameOriginal : viewA.eval implA = viewB.eval implB) :
    Native.Core.execute F n 1 (Message F) evaluate ambient challenge domain
      count start finish A viewA stmt implA prover =
    Native.execute F n 1 ambient challenge domain count start finish B viewB stmt implB
      (polynomialProver ambient count prover) :=
  Native.Core.execute_transport F n 1 (Message F) evaluate ambient
    (SingleRound.Message F 1) (fun q x => q.val.eval x) message challenge domain
    count start finish A B viewA viewB stmt implA implB prover message_evaluate sameOriginal

/-- Every returned claim retains the original oracle's complete behavior. -/
theorem execute_preserves_original (n : Nat) (challenge : OracleComp ambient F) (domain : List F)
    (count start : Nat) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n 1))
    (stmt : _root_.Sumcheck.Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    (prover : EndpointProver (F := F) ambient count) :
    ∀ result, some result ∈ support (Native.Core.execute F n 1 (Message F) evaluate ambient
      challenge domain count start finish A original stmt impl prover) →
      result.oracles = original.eval impl := by
  induction count generalizing start A with
  | zero =>
      rw [Native.Core.execute_zero]
      intro result supported
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at supported
      cases supported
      rfl
  | succ count ih =>
      rw [Native.Core.execute_succ]
      intro result supported
      obtain ⟨⟨pair, respond⟩, _, supported⟩ := support_bind_exists supported
      by_cases passed : (domain.map (fun x => evaluate pair x)).sum = stmt.target
      · simp only [passed, ite_true] at supported
        obtain ⟨r, _, supported⟩ := support_bind_exists supported
        obtain ⟨next, _, supported⟩ := support_bind_exists supported
        have retained := ih (start + 1) (by omega) _ _ _ _ next result supported
        rw [VirtualOracle.eval_sumWeaken_extendImpl A original
          (Native.Core.messageInterface F (Message F) evaluate) impl pair] at retained
        exact retained
      · simp only [passed, ite_false] at supported
        obtain ⟨_, _, supported⟩ := support_bind_exists supported
        simp only [support_pure, Set.mem_singleton_iff, Option.some_ne_none] at supported

omit [DecidableEq F] in
theorem oracle_realized {n : Nat} (table : Table F n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n 1))
    (impl : QueryImpl (ofPFunctor A) Id)
    (answers : ∀ point, original.eval impl ⟨(), point⟩ = extension n table point) :
    original.eval impl = (MultivariateRound.polynomialFamily F n 1).behaviorOfRealizations
      (fun _ => oracleStatement table) := by
  funext query
  rcases query with ⟨⟨⟩, point⟩
  exact (answers point).trans (statement_evaluate table point).symm

variable [Nontrivial F]

noncomputable def booleanDomain : List F := (Finset.univ.map (boolEmbedding F)).toList

omit [DecidableEq F] in
theorem domain_sum_message (pair : Message F) :
    ((booleanDomain (F := F)).map (evaluate pair)).sum = boundary pair := by
  classical
  have bridge := Multiset.sum_map_toList (Finset.univ.map (boolEmbedding F)).1 (evaluate pair)
  change _ = ∑ x ∈ Finset.univ.map (boolEmbedding F), evaluate pair x at bridge
  apply bridge.trans
  simp only [Finset.sum_map, Fin.sum_univ_two, boolEmbedding_zero, boolEmbedding_one,
    evaluate_zero, evaluate_one, boundary]

/-- Exposes the actual guard-before-challenge order. On failure the prover's
abort continuation runs; the verifier does not query its challenge program. -/
theorem execute_round (n : Nat) (challenge : OracleComp ambient F)
    (count start : Nat) (finish : start + (count + 1) = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n 1))
    (stmt : _root_.Sumcheck.Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    (prover : EndpointProver (F := F) ambient (count + 1)) :
    Native.Core.execute F n 1 (Message F) evaluate ambient challenge booleanDomain
      (count + 1) start finish A original stmt impl prover =
      (do
        let chosen ← prover
        if boundary chosen.1 = stmt.target then
          let r ← challenge
          let next ← chosen.2 (some r)
          Native.Core.execute F n 1 (Message F) evaluate ambient challenge booleanDomain
            count (start + 1) (by omega)
            (Access.extend A (Native.Core.messageInterface F (Message F) evaluate))
            (original.sumWeaken (Native.Core.messageInterface F (Message F) evaluate).spec)
            ⟨evaluate chosen.1 r, Fin.snoc stmt.challenges r⟩
            (Access.extendImpl A (Native.Core.messageInterface F (Message F) evaluate) impl chosen.1)
            next
        else
          let _ ← chosen.2 none
          return none) := by
  rw [Native.Core.execute_succ]
  apply bind_congr
  rintro ⟨pair, respond⟩
  rw [show (booleanDomain.map (fun x => evaluate pair x)).sum = boundary pair from
    domain_sum_message pair]

omit [DecidableEq F] in
theorem closed_statement {n : Nat} (table : Table F n) (claim : F) :
    MultivariateRound.closedRelation F n 1 (boolEmbedding F) 0
      ⟨⟨claim, Fin.elim0⟩, (MultivariateRound.polynomialFamily F n 1).behaviorOfRealizations
        (fun _ => oracleStatement table)⟩ ↔ booleanSum table = claim := by
  change (∑ point ∈ (Finset.univ.map (boolEmbedding F)) ^ᶠ n,
    MvPolynomial.eval (Fin.append Fin.elim0 point ∘ Fin.cast (by omega))
      (statement table)) = claim ↔ _
  simp only [Fin.append_left_nil _ _ rfl, Function.comp_def, Fin.cast_cast, Fin.cast_eq_self]
  rw [statement_sum]

/-- The accepted-event observation is the independent public-table checker.
This compares final observations, not endpoint/polynomial query traces. -/
theorem publicTable_observation {n : Nat} (table : Table F n) (values : List F)
    (decoded : ofList? n values = some table) (challenge : OracleComp ambient F)
    (count start : Nat) (finish : start + count = n) (A : PFunctor)
    (original : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n 1))
    (stmt : _root_.Sumcheck.Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id) (prover : EndpointProver (F := F) ambient count)
    (answers : ∀ point, original.eval impl ⟨(), point⟩ = extension n table point) :
    (do let result ← Native.Core.execute F n 1 (Message F) evaluate ambient challenge
          booleanDomain count start finish A original stmt impl prover
        return result.map (Native.outputRelation F n 1) = some True) =
    (do let result ← Native.Core.execute F n 1 (Message F) evaluate ambient challenge
          booleanDomain count start finish A original stmt impl prover
        return result.map (fun output => check values output.stmt.challenges output.stmt.target) =
          some true) := by
  apply bind_congr_of_forall_mem_support
  intro result supported
  cases result with
  | none => simp only [Option.map_none, reduceCtorEq]
  | some result =>
      have retained := execute_preserves_original ambient n challenge booleanDomain
        count start finish A original stmt impl prover result supported
      apply congrArg pure
      apply propext
      simp only [Option.map_some, Option.some.injEq, eq_iff_iff, iff_true]
      change result.oracles ⟨(), result.stmt.challenges⟩ = result.stmt.target ↔ _
      rw [retained, answers result.stmt.challenges]
      simp only [check, Fin.val_last, decoded, decide_eq_true_eq]
      rfl

end ZkcSecurity.ArkLib.Sumcheck.Multilinear
