module

public import ZkcSecurity.Bindings.Transcript.QueryTreeSource.Composition.Private

@[expose] public section

/-! First exposure and cached verifier calls in the heterogeneous macro oracle.
Uniform-product calibration applies to a fresh complete tree after exact simulation.
It never asserts conditional independence of previously exposed primitive nodes.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.FiatShamir.QueryTreeSource.Composition
open Zkc.Source Zkc.Construction QueryTree OracleComp OracleSpec MeasureTheory
noncomputable section
local instance (priority := 2000) (α : Type) : DecidableEq α := Classical.decEq α
attribute [local instance] rawSampler otherSampler primitiveSampler macroSampler
/-- A known cached answer is not a fresh uniform draw on a nontrivial range. Therefore
fresh-query source laws cannot be instantiated at arbitrary adversarially exposed histories. -/
theorem cached_not_fresh {D : Type} {R : D → Type} [∀ key, SampleableType (R key)]
    (cache : (ofFn R).QueryCache) (key : D) (value : R key)
    (cached : cache key = some value) (nontrivial : 1 < Nat.card (R key)) :
    ¬ (randomOracle key).run' cache =ᵈ ($ᵗ (R key)) := by
  intro law
  have probability := law.prEvent_eq (· = value)
  rw [StateT.run'_eq, randomOracle.run_eq, cached] at probability
  simp [prEvent_pure_prop] at probability
  rw [SampleableType.prEvent_uniformSample_eq_singleton_natCard] at probability
  have cardOne : (Nat.card (R key) : ENNReal) = 1 := ENNReal.inv_eq_one.mp probability.symm
  have cardinality : Nat.card (R key) = 1 := by exact_mod_cast cardOne
  exact (ne_of_gt nontrivial) cardinality

variable {carriers : Structured.Carriers} {bound height : Nat} [NeZero bound]
variable [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)]

/-- Every logical access to a source root returns its one shared complete tree. -/
def rootQuery (root : Domain.History carriers) :
    OracleComp (ofFn (fullRange carriers bound height)) (Coordinate bound height → Fin bound) :=
  liftM ((ofFn (fullRange carriers bound height)).query (.inl (.inl root)))

/-- The actual lazy macro oracle samples exactly once at the first exposure, even when the
first primitive access was an offpath suffix. The complement cache is retained in full. -/
theorem first_exposure
    (cache : (ofFn (fullRange carriers bound height)).QueryCache)
    (root : Domain.History carriers) (fresh : cache (.inl (.inl root)) = none) :
    (randomOracle (spec := ofFn (fullRange carriers bound height)) (.inl (.inl root))).run cache =ᵈ
      (do let tree ← $ᵗ (Coordinate bound height → Fin bound)
          pure (tree, cache.cacheQuery (.inl (.inl root)) tree)) := by
  dsimp only [fullRange, macroRange, ofFn, OracleSpec.Range] at *
  let : MeasurableSpace (Coordinate bound height → Fin bound) := ⊤
  have uniform :
      (@uniformSample (Coordinate bound height → Fin bound)
        (@macroSampler (Root carriers bound) (Coordinate bound height) (Fin bound)
          (OtherKey carriers bound) otherRange inferInstance inferInstance
          (fun key ↦ otherSampler key) (.inl (.inl root)))) =ᵈ
        ($ᵗ (Coordinate bound height → Fin bound)) :=
    EvalDistEq.of_evalDist_eq (by
      simp only [SampleableType.evalDist_uniformSample])
  simpa only [randomOracle.run_eq, fresh] using
    uniform.bind_left (fun tree ↦ pure (tree, cache.cacheQuery (.inl (.inl root)) tree))

omit [NeZero bound] [∀ event, SampleableType (Domain.Raw (carriers := carriers) event)] in
/-- Allocating a scalar root preserves every other dependent cell, including fields,
blocks and other scalar bounds. No answer is coerced through the scalar reply carrier. -/
theorem scalar_cache_preserves_other
    (cache : (ofFn (fullRange carriers bound height)).QueryCache)
    (root : Root carriers bound) (tree : Coordinate bound height → Fin bound)
    (other : OtherKey carriers bound) :
    (cache.cacheQuery (.inl root) tree) (.inr other) = cache (.inr other) :=
  QueryCache.cacheQuery_of_ne cache (t' := .inr other) (t := .inl root) tree
    (by intro impossible; cases impossible)

/-- After the heterogeneous simulation, the newly exposed root's complete path has the
unconditional product law. A cached root cannot satisfy the freshness premise. -/
theorem first_exposure_product {α : Type} [MeasurableSpace α]
    (cache : (ofFn (fullRange carriers bound height)).QueryCache)
    (root : Domain.History carriers) (fresh : cache (.inl (.inl root)) = none)
    (next : List (Fin bound) → ProbComp α) :
    𝒟[do
      let result ← (randomOracle (spec := ofFn (fullRange carriers bound height))
        (.inl (.inl root))).run cache
      next (path id height (fun node ↦ result.1 (.inl node)))] =
      𝒟[samples id height >>= next] := by
  have exposed := ((first_exposure cache root fresh).bind_left
    (fun result ↦ next (path id height (fun node ↦ result.1 (.inl node))))).evalDist_eq
  simp only [bind_assoc, pure_bind] at exposed
  exact exposed.trans (macro_path_product next)

/-- A separately querying verifier makes its own logical call when the prover already
exposed the tree. Both the full dependent cache and the logical query log are retained. -/
theorem verifier_cached_logged
    (cache : (ofFn (fullRange carriers bound height)).QueryCache)
    (root : Domain.History carriers) (tree : Coordinate bound height → Fin bound)
    (cached : cache (.inl (.inl root)) = some tree) :
    ((randomOracle.withLogging (.inl (.inl root))).run).run cache =
      (pure ((tree, [⟨.inl (.inl root), tree⟩]), cache) :
        ProbComp (((Coordinate bound height → Fin bound) ×
          QueryLog (ofFn (fullRange carriers bound height))) ×
          (ofFn (fullRange carriers bound height)).QueryCache)) := by
  rw [QueryImpl.run_withLogging_apply, StateT.run_bind,
    QueryImpl.withCaching_run_some _ cached]
  rfl

/-- Any event on the complete returned record transfers through the exact heterogeneous
simulation. This is the point at which a separately proved macro-tree charge is applicable. -/
theorem full_event_eq (segment : Segment) {α : Type}
    (program : OracleComp (ofFn (Typed.ByLast (@Domain.Raw carriers))) α)
    (event : α → Prop) :
    Pr{let value ← (simulateQ randomOracle program).run' ∅}[event value] =
      Pr{let value ← (simulateQ randomOracle (fullTranslate (height := height)
        (bound := bound) segment program)).run' ∅}[event value] :=
  (full_exact segment program).prEvent_eq event

end
end ZkcSecurity.FiatShamir.QueryTreeSource.Composition
