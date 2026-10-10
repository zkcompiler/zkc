import Std

/-! Cache correctness relative to one fixed immutable interpretation.

Keys must contain the bindings needed to identify that interpretation. Validity
is relative to the actual provider, so a cached value cannot justify rebinding
or caching a stateful service. Storage policy may depend on the current cache.
-/

set_option autoImplicit false

namespace Zkc.Modules.ImmutableCache

variable {K V : Type}

abbrev Cache (K V : Type) := K → Option V

def Valid (provider : K → V) (cache : Cache K V) : Prop :=
  ∀ key value, cache key = some value → value = provider key

def empty : Cache K V := fun _ => none

theorem empty_valid (provider : K → V) : Valid provider empty := by
  intro key value present
  cases present

def insert [DecidableEq K] (cache : Cache K V) (key : K) (value : V) : Cache K V :=
  fun other => if other = key then some value else cache other

theorem insert_valid [DecidableEq K] (provider : K → V) (cache : Cache K V)
    (valid : Valid provider cache) (key : K) :
    Valid provider (insert cache key (provider key)) := by
  intro other value present
  by_cases same : other = key
  · subst other
    simpa [insert] using present.symm
  · exact valid other value (by simpa [insert, same] using present)

def lookup [DecidableEq K] (provider : K → V) (store : Cache K V → K → Bool)
    (cache : Cache K V) (key : K) : V × Cache K V :=
  match cache key with
  | some value => (value, cache)
  | none => (provider key, if store cache key then insert cache key (provider key) else cache)

theorem lookup_value [DecidableEq K] (provider : K → V) (store : Cache K V → K → Bool)
    (cache : Cache K V) (key : K) (valid : Valid provider cache) :
    (lookup provider store cache key).1 = provider key := by
  unfold lookup
  cases present : cache key with
  | none => rfl
  | some value => exact valid key value present

theorem lookup_valid [DecidableEq K] (provider : K → V) (store : Cache K V → K → Bool)
    (cache : Cache K V) (key : K) (valid : Valid provider cache) :
    Valid provider (lookup provider store cache key).2 := by
  unfold lookup
  cases present : cache key with
  | some value => exact valid
  | none =>
    simp only
    split
    · exact insert_valid provider cache valid key
    · exact valid

/-- Rebinding requires agreement at the actual cached keys. Uncached entries
may change without invalidating the cache. The premise does not come from a name. -/
theorem rebind (before after : K → V) (cache : Cache K V) (valid : Valid before cache)
    (agrees : ∀ key value, cache key = some value → before key = after key) :
    Valid after cache := by
  intro key value present
  exact (valid key value present).trans (agrees key value present)

end Zkc.Modules.ImmutableCache
