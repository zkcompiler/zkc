module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Typed

@[expose] public section

/-! Separate prover allocation and verifier logical queries. The verifier handler always asks
the macro oracle, even when a prover exposed that root earlier. Both use the same lazy cache.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.QueryTreeSource
open Zkc.Source Zkc.Construction QueryTree OracleComp OracleSpec MeasureTheory
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.decEq α
variable {carriers : Structured.Carriers} {bound height : Nat}

/-- Unlike the allocation simulator, every verifier primitive occurrence issues a macro call. -/
def verifierAsk (segment : Segment) (key : ScalarKey carriers bound) :
    OracleComp ((Root carriers bound) →ₒ (Coordinate bound height → Fin bound)) (Fin bound) := do
  let tree ← ((Root carriers bound) →ₒ (Coordinate bound height → Fin bound)).query
    (locate (height := height) segment key).1
  pure (tree (locate (height := height) segment key).2)

theorem verifier_source_ask (segment : Segment)
    (request : segment.query.request = some (.sampleIndex bound))
    (root : Domain.History carriers) (node : Node (Fin bound) height) :
    verifierAsk (height := height) segment
      ⟨encode segment (root, node), (segment.queryAt_request _).trans request⟩ =
      (do let tree ← verifierQuery root; pure (tree (.inl node))) := by
  exact congrArg (fun pair : Root carriers bound × Coordinate bound height ↦
    (do
      let tree ← ((Root carriers bound) →ₒ (Coordinate bound height → Fin bound)).query pair.1
      pure (tree pair.2) : OracleComp
        ((Root carriers bound) →ₒ (Coordinate bound height → Fin bound)) (Fin bound)))
    (locate_encode segment request (root, node))

variable [NeZero bound]

omit [NeZero bound] in
/-- Every verifier primitive occurrence costs one macro query, including repeated queries. -/
theorem verifier_budget (segment : Segment) {α : Type}
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) (budget : Nat)
    (bounded : IsTotalQueryBound program budget) :
    IsTotalQueryBound (simulateQ (verifierAsk (height := height) segment) program) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => exact bounded
  | query_bind key next ih =>
    obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bounded
    simp only [simulateQ_bind, simulateQ_spec_query, verifierAsk, bind_assoc, pure_bind]
    apply isTotalQueryBound_query_bind_iff.mpr
    exact ⟨positive, fun tree ↦ ih _ _ (rest
      (tree (locate (height := height) segment key).2))⟩

/-- The same complete verifier program follows the prover. No synthetic acceptance event or
successful-source restriction is introduced; failures and logs can be returned in β. -/
def withVerifier (segment : Segment) {α β : Type}
    (prover : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α)
    (verifier : α → OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) β) :
    OracleComp ((Root carriers bound) →ₒ (Coordinate bound height → Fin bound)) β := do
  let output ← translate segment prover
  simulateQ (verifierAsk segment) (verifier output)

/-- Prover family budgets and the verifier's complete primitive budget are both charged.
No reduction by path length, distinct-key counting or cache occupancy is used. -/
theorem withVerifier_budget (segment : Segment) {Family α β : Type}
    [Fintype Family] [DecidableEq Family]
    (family : Root carriers bound × Coordinate bound height → Family)
    (prover : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α)
    (verifier : α → OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) β)
    (proverBudget : Provider.Budget Family) (verifierBudget : Nat)
    (proverBound : Provider.FamilyQueryBound (family ∘ locate segment) prover proverBudget)
    (verifierBound : ∀ output, IsTotalQueryBound (verifier output) verifierBudget) :
    IsTotalQueryBound (withVerifier (height := height) segment prover verifier)
      ((∑ kind, proverBudget kind) + verifierBudget) :=
  isTotalQueryBound_bind (source_budget segment family prover proverBudget proverBound)
    (fun output ↦ verifier_budget segment (verifier output) verifierBudget (verifierBound output))

omit [NeZero bound] in
private theorem verifier_table {α : Type} (segment : Segment)
    (table : Root carriers bound → Coordinate bound height → Fin bound)
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) :
    evalWithAnswerFn (QueryImpl.ofFn table)
      (simulateQ (verifierAsk (height := height) segment) program) =
        evalWithAnswerFn (QueryImpl.ofFn
          (fun key ↦ table (locate (height := height) segment key).1
            (locate (height := height) segment key).2)) program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind key next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, evalWithAnswerFn_bind]
    change evalWithAnswerFn (QueryImpl.ofFn table)
      (simulateQ (verifierAsk (height := height) segment)
        (next (table (locate (height := height) segment key).1
          (locate (height := height) segment key).2))) = _
    exact ih _

private theorem macro_extensional {α : Type} [MeasurableSpace α]
    (first second : OracleComp ((Root carriers bound) →ₒ
      (Coordinate bound height → Fin bound)) α)
    (same : ∀ table, evalWithAnswerFn (QueryImpl.ofFn table) first =
      evalWithAnswerFn (QueryImpl.ofFn table) second) :
    𝒟[(simulateQ randomOracle first).run' ∅] =
      𝒟[(simulateQ randomOracle second).run' ∅] := by
  classical
  let keys := possibleQueryKeys first ∪ possibleQueryKeys second
  have left : AllQueriesSatisfy first (· ∈ keys) :=
    (allQueriesSatisfy_possibleQueryKeys first).mono fun _ member ↦ Finset.mem_union_left _ member
  have right : AllQueriesSatisfy second (· ∈ keys) :=
    (allQueriesSatisfy_possibleQueryKeys second).mono fun _ member ↦ Finset.mem_union_right _ member
  let answers := fun table : keys → Coordinate bound height → Fin bound ↦
    extendTable (R := fun _ ↦ Coordinate bound height → Fin bound) keys table
  have agrees := fun table key ↦ extendTable_subtype
    (R := fun _ ↦ Coordinate bound height → Fin bound) keys table key
  rw [randomOracle_finite_cover first keys left id Function.injective_id answers agrees,
    randomOracle_finite_cover second keys right id Function.injective_id answers agrees]
  simp_rw [same]

/-- Exact shared-cache simulation of prover followed by an independently querying verifier. -/
theorem withVerifier_exact (segment : Segment) {α β : Type} [MeasurableSpace β]
    (prover : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α)
    (verifier : α → OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) β) :
    𝒟[(simulateQ randomOracle (prover >>= verifier)).run' ∅] =
      𝒟[(simulateQ randomOracle (withVerifier (height := height) segment prover verifier)).run' ∅] := by
  refine (adaptive_source_exact (height := height) segment (prover >>= verifier)).trans ?_
  apply macro_extensional
  intro table
  simp only [translate, translate_table, RandomOracleRouting.evalWithAnswerFn_route,
    withVerifier, evalWithAnswerFn_bind, verifier_table]
  rfl

/-- The same result holds at the actual dependent transcript keys used by the source reading. -/
theorem typed_withVerifier_exact
    [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)]
    (segment : Segment) {α β : Type}
    (prover : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α)
    (verifier : α → OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) β) :
    (simulateQ randomOracle (typedRenaming.translate (prover >>= verifier))).run' ∅ =ᵈ
      (simulateQ randomOracle (withVerifier (height := height) segment prover verifier)).run' ∅ := by
  let : MeasurableSpace β := ⊤
  exact (typedRenaming.evalDistEq_translate _).trans
    (EvalDistEq.of_evalDist_eq (withVerifier_exact segment prover verifier))

end
end ZkcSecurity.FiatShamir.QueryTreeSource
