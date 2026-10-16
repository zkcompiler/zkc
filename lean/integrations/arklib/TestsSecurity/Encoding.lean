module

public import ZkcSecurity.Oracle.Encoding

@[expose] public section

/-! Executable controls for cache representation, collisions and adaptive reuse. -/
namespace TestsSecurity.Encoding
open OracleComp OracleSpec ZkcSecurity.Oracle.Encoding

def draw : QueryImpl (Option Bool →ₒ Bool) (StateM Nat) :=
  fun key count => (key.getD false, count + 1)

def adaptive : OracleComp (Bool →ₒ Bool) (Bool × Bool × Bool) := do
  let first ← (query (spec := Bool →ₒ Bool) false : OracleComp (Bool →ₒ Bool) Bool)
  let second ← (query (spec := Bool →ₒ Bool) first : OracleComp (Bool →ₒ Bool) Bool)
  let third ← (query (spec := Bool →ₒ Bool) true : OracleComp (Bool →ₒ Bool) Bool)
  pure (first, second, third)

def result := ((simulateQ (handler some draw) adaptive).run ∅).run 0

theorem adaptive_answers : result.1.1 = (false, false, true) := by decide

/-- Three adaptive calls make two fresh draws; the repeated key is a cache hit. -/
theorem two_fresh_draws : result.2 = 2 := by decide

theorem retains_both_answers :
    result.1.2 (some false) = some false ∧ result.1.2 (some true) = some true := by
  constructor <;> decide

/-- Unqueried byte-domain inputs are not implicitly allocated cache entries. -/
theorem outside_not_cached : result.1.2 none = none := by decide

theorem option_encoding_injective : Function.Injective (some : Bool → Option Bool) :=
  injective_of_roundTrip some id (fun _ => rfl)

theorem projected_run :
    Prod.map id (view some) <$>
        (simulateQ (handler some draw) adaptive).run ∅ =
      (simulateQ (QueryImpl.withCaching (spec := Bool →ₒ Bool)
        (fun key => draw (some key))) adaptive).run ∅ :=
  adaptive_projection_empty some option_encoding_injective draw adaptive

def colliding : Bool → Unit := fun _ => ()

/-- Omitting part of the key merges cache cells even though the reply type agrees. -/
theorem collision_changes_other_key :
    view colliding ((∅ : (Unit →ₒ Bool).QueryCache).cacheQuery () true) ≠
      (view colliding ∅).cacheQuery true true := by
  intro equal
  have lookup := congrArg (fun cache : (Bool →ₒ Bool).QueryCache => cache false) equal
  change some true = none at lookup
  cases lookup

theorem foreign_cache_entry_preserved :
    view some ((∅ : (Option Bool →ₒ Bool).QueryCache).cacheQuery none true) =
      (∅ : (Bool →ₒ Bool).QueryCache) := by
  rw [view_outside some ∅ none true (fun _ => Option.some_ne_none _), view_empty]

end TestsSecurity.Encoding
