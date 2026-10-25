module

public import VCVio.OracleComp.QueryTracking.CachingOracle

@[expose] public section

/-! Cache projection through an injective key encoding.

A client that queries typed keys through a fixed injective encoding into a
shared cached oracle sees exactly the cache restricted to its keys. Distinct
typed keys stay distinct cache entries, so their answers stay independent. No
property of a concrete hash or sampler is assumed.
-/

namespace ZkcSecurity.Oracle.Encoding
open OracleComp OracleSpec

variable {Key Bytes Answer : Type}

/-- Restrict a cache on encoded keys to the keys a typed client uses. -/
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

/-- Caching an encoded key caches exactly that typed key in the view. -/
theorem view_cacheQuery [DecidableEq Key] [DecidableEq Bytes] (encode : Key → Bytes)
    (injective : Function.Injective encode)
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

end ZkcSecurity.Oracle.Encoding
