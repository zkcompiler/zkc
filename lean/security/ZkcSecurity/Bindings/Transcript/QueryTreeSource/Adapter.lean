module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Simulation

@[expose] public section

/-! The source scalar-key consumer of cached tree simulation. Distributional equalities
preserve complete returned outcomes. Logging is inserted before routing, so histories still
contain the original typed source keys. Compound probability charges belong to macro trees.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.QueryTreeSource
open Zkc.Source Zkc.Construction QueryTree OracleComp OracleSpec Provider MeasureTheory
noncomputable section
local instance (α : Type) : DecidableEq α := Classical.decEq α
variable {carriers : Structured.Carriers} {bound height : Nat} [NeZero bound]

/-- The actual source-key program, routed and then consumed by the existing simulator. -/
def translate (segment : Segment) {α : Type}
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) :
    OracleComp ((Root carriers bound) →ₒ (Coordinate bound height → Fin bound)) α :=
  simulator.translate (RandomOracleRouting.route (@locate carriers bound height segment) program) ()

theorem adaptive_source_exact (segment : Segment) {α : Type}
    [MeasurableSpace α] (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) :
    𝒟[(simulateQ randomOracle program).run' ∅] =
      𝒟[(simulateQ randomOracle (translate (height := height) segment program)).run' ∅] := by
  exact (routed_exact segment program).symm.trans (adaptive_exact _)

/-- All original primitive keys and replies survive, in order, including repeated cached calls. -/
theorem adaptive_source_logged (segment : Segment) {α : Type}
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α) :
    let observed := (simulateQ loggingOracle program).run
    (simulateQ randomOracle observed).run' ∅ =ᵈ
      (simulateQ randomOracle (translate (height := height) segment observed)).run' ∅ := by
  let : MeasurableSpace (α × QueryLog ((ScalarKey carriers bound) →ₒ Fin bound)) := ⊤
  exact EvalDistEq.of_evalDist_eq (adaptive_source_exact segment _)

/-- A private distribution of adaptive source programs is preserved without fixing their keys. -/
theorem adaptive_source_mixture (segment : Segment) {α : Type}
    (programs : ProbComp (OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α)) :
    (do let program ← programs; (simulateQ randomOracle program).run' ∅) =ᵈ
      (do let program ← programs
          (simulateQ randomOracle (translate (height := height) segment program)).run' ∅) := by
  let : MeasurableSpace α := ⊤
  exact EvalDistEq.bind_right programs fun program ↦
    EvalDistEq.of_evalDist_eq (adaptive_source_exact segment program)

/-- Interleaved private draws are converted by the pinned privatePrograms theorem; the
sampled adaptive program still contains every primitive source query. -/
theorem adaptive_source_interleaved (segment : Segment) {α : Type}
    (program : OracleComp (unifSpec + ((ScalarKey carriers bound) →ₒ Fin bound)) α) :
    (simulateQ (unifSpec.passthrough + randomOracle) program).run' ∅ =ᵈ
      (do let fixed ← privatePrograms program
          (simulateQ randomOracle (translate (height := height) segment fixed)).run' ∅) := by
  let : MeasurableSpace (α × ((ScalarKey carriers bound) →ₒ Fin bound).QueryCache) := ⊤
  have joint := EvalDistEq.of_evalDist_eq (privatePrograms_stateful randomOracle program ∅)
  have output := joint.map Prod.fst
  simp only [map_bind, ← StateT.run'_eq] at output
  exact output.trans (adaptive_source_mixture segment (privatePrograms program))

/-- Uniform-product calibration is attached to the complete macro tree after simulation.
It is unconditional: previously exposed trees cannot be resampled at this law. -/
theorem macro_path_product {α : Type} [MeasurableSpace α]
    (next : List (Fin bound) → ProbComp α) :
    𝒟[do
      let tree ← $ᵗ (Coordinate bound height → Fin bound)
      next (path id height (fun node ↦ tree (.inl node)))] =
      𝒟[samples id height >>= next] := by
  classical
  have projection := EvalDistEq.of_evalDist_eq (evalDist_map_table_comp_injective
    ($ᵗ (Node (Fin bound) height → Fin bound)) ($ᵗ (Coordinate bound height → Fin bound))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample
    (Sum.inl_injective : Function.Injective
      (Sum.inl : Node (Fin bound) height → Coordinate bound height)))
  have equality := (projection.bind_left (fun tree ↦ next (path id height tree))).evalDist_eq
  rw [bind_map_left] at equality
  exact equality.trans (path_product_bind id height next)

omit [NeZero bound] in
/-- Routing spends one primitive budget unit at each query occurrence, even on cache hits. -/
theorem route_budget (segment : Segment) {Family α : Type} [DecidableEq Family]
    (family : Root carriers bound × Coordinate bound height → Family)
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α)
    (budget : Budget Family) (bounded : FamilyQueryBound (family ∘ locate segment) program budget) :
    FamilyQueryBound family (RandomOracleRouting.route (locate segment) program) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure value => exact bounded
  | query_bind key next ih =>
    obtain ⟨positive, rest⟩ := (familyQueryBound_query_bind_iff _).mp bounded
    change FamilyQueryBound family (.queryBind (locate segment key)
      (fun reply ↦ RandomOracleRouting.route (locate segment) (next reply))) budget
    apply (familyQueryBound_query_bind_iff
      (spec := (Root carriers bound × Coordinate bound height) →ₒ Fin bound)
      (query := locate segment key)
      (next := fun reply ↦ RandomOracleRouting.route (locate segment) (next reply)) family).mpr
    exact ⟨positive, fun reply ↦ ih reply _ (rest reply)⟩

/-- No division by the number of scalar draws occurs. Fallback keys are charged as well. -/
theorem source_budget (segment : Segment) {Family α : Type} [Fintype Family]
    [DecidableEq Family] (family : Root carriers bound × Coordinate bound height → Family)
    (program : OracleComp ((ScalarKey carriers bound) →ₒ Fin bound) α)
    (budget : Budget Family) (bounded : FamilyQueryBound (family ∘ locate segment) program budget) :
    IsTotalQueryBound (translate (height := height) segment program) (∑ kind, budget kind) :=
  translate_budget family _ budget (route_budget segment family program budget bounded)

/-- A source suffix key exposes its entry root at its first access, regardless of node depth.
The trace is the actual existing simulator trace; the root is not inferred from a path query. -/
theorem source_checkpoint (segment : Segment)
    (request : segment.query.request = some (.sampleIndex bound))
    (root : Domain.History carriers) (node : Node (Fin bound) height)
    {trace : List (Answered ((Root carriers bound × Coordinate bound height) →ₒ Fin bound)
      (Root carriers bound))}
    {state : (simulator (Root := Root carriers bound) (Coordinate := Coordinate bound height)
      (Raw := Fin bound)).State}
    (runs : simulator.Runs () trace state)
    (first : ∀ entry ∈ trace, entry.query.1 ≠ Sum.inl root) :
    (simulator.handle (locate segment
      ⟨encode segment (root, node), (segment.queryAt_request _).trans request⟩)).run state =
      (fun tree ↦ (tree (.inl node), simulator.record state (.inl root) tree)) <$>
        liftM (((Root carriers bound) →ₒ (Coordinate bound height → Fin bound)).query
          (.inl root)) := by
  rw [locate_encode segment request]
  exact first_node_checkpoint runs _ _ first

/-- Verifier code calls this macro operation itself, including after prover allocation. -/
def verifierQuery (root : Domain.History carriers) :
    OracleComp ((Root carriers bound) →ₒ (Coordinate bound height → Fin bound))
      (Coordinate bound height → Fin bound) :=
  liftM (((Root carriers bound) →ₒ (Coordinate bound height → Fin bound)).query (.inl root))

/-- Logical verifier access is recorded even when the prover has already cached this tree. -/
theorem verifier_cached
    (cache : ((Root carriers bound) →ₒ (Coordinate bound height → Fin bound)).QueryCache)
    (root : Domain.History carriers) (tree : Coordinate bound height → Fin bound)
    (cached : cache (.inl root) = some tree) :
    ((randomOracle.withLogging (.inl root)).run).run cache =
      (pure ((tree, [⟨.inl root, tree⟩]), cache) :
        ProbComp (((Coordinate bound height → Fin bound) ×
          QueryLog ((Root carriers bound) →ₒ (Coordinate bound height → Fin bound))) ×
          ((Root carriers bound) →ₒ (Coordinate bound height → Fin bound)).QueryCache)) :=
  verifier_cache_hit_logged cache (.inl root) tree cached

end
end ZkcSecurity.FiatShamir.QueryTreeSource
