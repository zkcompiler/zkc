module

public import VCVio.OracleComp.QueryTracking.CachingOracle

@[expose] public section

/-! Injective key encodings preserve adaptive cached-oracle execution.

The encoding is fixed independently of the sampled oracle table. Both the
result and the projected residual cache are preserved, for arbitrary initial
caches. The client queries typed keys through the encoder. This theorem does
not translate an adversary with arbitrary access to the encoded-key domain;
such an experiment needs an additional adapter for queries outside the image.

The proof uses VCVio's state-projection theorem, at the version pinned in this
package's manifest. No property of a concrete hash or sampler is assumed here.
-/

namespace ZkcSecurity.Oracle.Encoding
open OracleComp OracleSpec

universe u v

variable {Key Bytes Answer : Type u}

/-- A successful round trip suffices to rule out encoded-key collisions. -/
theorem injective_of_roundTrip (encode : Key → Bytes) (decode : Bytes → Option Key)
    (roundTrip : ∀ key, decode (encode key) = some key) :
    Function.Injective encode := by
  intro left right same
  have decoded := congrArg decode same
  rw [roundTrip, roundTrip] at decoded
  exact Option.some.inj decoded

/-- Restrict a byte-domain cache to the keys used by the typed client. -/
def view (encode : Key → Bytes) (cache : (Bytes →ₒ Answer).QueryCache) :
    (Key →ₒ Answer).QueryCache :=
  QueryCache.ofFn (fun key => cache (encode key))

@[simp] theorem view_apply (encode : Key → Bytes)
    (cache : (Bytes →ₒ Answer).QueryCache) (key : Key) :
    view encode cache key = cache (encode key) := rfl

@[simp] theorem view_empty (encode : Key → Bytes) :
    view encode (∅ : (Bytes →ₒ Answer).QueryCache) = ∅ := by
  ext key
  rfl

variable [DecidableEq Key] [DecidableEq Bytes]

/-- Distinct typed keys remain distinct cache entries under an injective encoding. -/
theorem view_cacheQuery (encode : Key → Bytes) (injective : Function.Injective encode)
    (cache : (Bytes →ₒ Answer).QueryCache) (key : Key) (answer : Answer) :
    view encode (cache.cacheQuery (encode key) answer) =
      (view encode cache).cacheQuery key answer := by
  ext other
  by_cases same : other = key
  · subst other
    simp
  · have encoded : encode other ≠ encode key := fun h => same (injective h)
    simp only [view_apply, QueryCache.cacheQuery_of_ne _ _ encoded,
      QueryCache.cacheQuery_of_ne _ _ same]

omit [DecidableEq Key] in
/-- An entry outside the encoding's image does not change this projected cache. -/
theorem view_outside (encode : Key → Bytes) (cache : (Bytes →ₒ Answer).QueryCache)
    (bytes : Bytes) (answer : Answer) (outside : ∀ key, encode key ≠ bytes) :
    view encode (cache.cacheQuery bytes answer) = view encode cache := by
  apply QueryCache.ext
  intro key
  exact QueryCache.cacheQuery_of_ne cache answer (outside key)

variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

/-- Encode before consulting the shared cache; cache hits do not invoke `draw`. -/
def handler (encode : Key → Bytes) (draw : QueryImpl (Bytes →ₒ Answer) m) :
    QueryImpl (Key →ₒ Answer) (StateT (Bytes →ₒ Answer).QueryCache m) :=
  fun key => draw.withCaching (encode key)

/-- One encoded query preserves its response and the restricted successor cache. -/
theorem local_projection (encode : Key → Bytes) (injective : Function.Injective encode)
    (draw : QueryImpl (Bytes →ₒ Answer) m) (key : Key)
    (cache : (Bytes →ₒ Answer).QueryCache) :
    Prod.map id (view encode) <$> (handler encode draw key).run cache =
      (QueryImpl.withCaching (spec := Key →ₒ Answer)
        (fun key => draw (encode key)) key).run (view encode cache) := by
  cases cached : cache (encode key) with
  | none =>
      rw [handler, QueryImpl.withCaching_run_none draw cached,
        QueryImpl.withCaching_run_none _ (show view encode cache key = none from cached)]
      simp only [Functor.map_map, Prod.map_apply, id_eq, view_cacheQuery encode injective]
  | some answer =>
      rw [handler, QueryImpl.withCaching_run_some draw cached,
        QueryImpl.withCaching_run_some _ (show view encode cache key = some answer from cached)]
      simp

/-- Every adaptive typed client preserves its output and projected residual cache.
This includes a client followed by any further typed oracle computation. -/
theorem adaptive_projection (encode : Key → Bytes) (injective : Function.Injective encode)
    (draw : QueryImpl (Bytes →ₒ Answer) m) {Result : Type u}
    (program : OracleComp (Key →ₒ Answer) Result)
    (cache : (Bytes →ₒ Answer).QueryCache) :
    Prod.map id (view encode) <$> (simulateQ (handler encode draw) program).run cache =
      (simulateQ (QueryImpl.withCaching (spec := Key →ₒ Answer)
        (fun key => draw (encode key))) program).run (view encode cache) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ (view encode)
    (local_projection encode injective draw) program cache

/-- An initially empty encoded cache gives precisely an empty typed cache. -/
theorem adaptive_projection_empty (encode : Key → Bytes)
    (injective : Function.Injective encode) (draw : QueryImpl (Bytes →ₒ Answer) m)
    {Result : Type u} (program : OracleComp (Key →ₒ Answer) Result) :
    Prod.map id (view encode) <$>
        (simulateQ (handler encode draw) program).run ∅ =
      (simulateQ (QueryImpl.withCaching (spec := Key →ₒ Answer)
        (fun key => draw (encode key))) program).run ∅ := by
  simpa only [view_empty] using adaptive_projection encode injective draw program ∅

end ZkcSecurity.Oracle.Encoding
