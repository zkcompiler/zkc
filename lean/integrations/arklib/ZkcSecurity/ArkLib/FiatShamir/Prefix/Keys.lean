module

public import ArkLib.Interaction.Oracle.Security.StateRestoration

@[expose] public section

/-! A fixed, injective encoding of two-round full transcript prefixes into
ArkLib's salted restoration keys. The selected protocol repeats one round
alphabet twice. No table or previously sampled response defines this encoding:
the challenge in a second-round key is supplied by the querying client. -/

namespace ZkcSecurity.ArkLib.FiatShamir.Prefix
open OracleComp OracleSpec
open Interaction.Oracle.Security

variable (Input : Type) (round : StateRestoration.Round)

/-- Every well-typed full prefix is queryable, whether consistent or not. -/
abbrev Key := (Input × round.Message) ⊕
  (Input × round.Message × round.Challenge × round.Message)

abbrev Spec := Key Input round →ₒ round.Challenge
abbrev Salt := Option round.Challenge
abbrev TargetKey := StateRestoration.Key Input (Salt round) [round, round]
abbrev TargetSpec := StateRestoration.oracleSpec Input (Salt round) [round, round]

variable {Input round}

/-- The current salt carries the earlier challenge; the earlier salt stays `none`. -/
def encode : Key Input round → TargetKey Input round
  | .inl (z, first) => StateRestoration.Key.here z first none
  | .inr (z, first, challenge, second) =>
      StateRestoration.Key.later first none (StateRestoration.Key.here z second (some challenge))

/-- Partial inverse rejects all restoration keys outside the chosen salt discipline. -/
def decode : TargetKey Input round → Option (Key Input round)
  | .inl (z, first, none) => some (.inl (z, first))
  | .inr (first, none, .inl (z, second, some challenge)) =>
      some (.inr (z, first, challenge, second))
  | _ => none

@[simp] theorem decode_encode (key : Key Input round) : decode (encode key) = some key := by
  cases key <;> rfl

/-- Distinct claimed challenges remain distinct queries, including inconsistent claims. -/
theorem encode_injective : Function.Injective (encode (Input := Input) (round := round)) := by
  intro a b h
  have := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using this

/-- Both round responses have the selected challenge alphabet. -/
def responseEquiv (key : Key Input round) :
    (encode key).Challenge ≃ round.Challenge := by
  cases key <;> exact Equiv.refl _

/-- Restrict a restoration cache to the complete full-prefix query domain. -/
def view (cache : (TargetSpec Input round).QueryCache) : (Spec Input round).QueryCache :=
  QueryCache.ofFn fun key => (cache (encode key)).map (responseEquiv key)

@[simp] theorem view_apply (cache : (TargetSpec Input round).QueryCache)
    (key : Key Input round) :
    view cache key = (cache (encode key)).map (responseEquiv key) := rfl

@[simp] theorem view_empty :
    view (∅ : (TargetSpec Input round).QueryCache) = ∅ := by
  ext key
  simp [view]

variable [DecidableEq Input] [DecidableEq round.Challenge]

instance targetDecidableEq : DecidableEq (TargetKey Input round) :=
  StateRestoration.Key.instDecidableEq [round, round]

/-- Updating one translated query changes precisely that full-prefix cache entry. -/
theorem view_cacheQuery (cache : (TargetSpec Input round).QueryCache)
    (key : Key Input round) (answer : (encode key).Challenge) :
    view (cache.cacheQuery (encode key) answer) =
      (view cache).cacheQuery key (responseEquiv key answer) := by
  apply QueryCache.ext
  intro other
  by_cases h : other = key
  · subst other
    simp
  · have encoded : encode other ≠ encode key := fun e => h (encode_injective e)
    simp only [view_apply, QueryCache.cacheQuery_of_ne _ _ encoded,
      QueryCache.cacheQuery_of_ne _ _ h]

omit [DecidableEq Input] [DecidableEq round.Challenge] in
/-- Non-image entries are retained in the target cache, but cannot alias full-prefix queries. -/
theorem view_outside [DecidableEq (TargetKey Input round)]
    (cache : (TargetSpec Input round).QueryCache) (key : TargetKey Input round)
    (answer : key.Challenge) (outside : ∀ full, encode full ≠ key) :
    view (cache.cacheQuery key answer) = view cache := by
  apply QueryCache.ext
  intro full
  simp only [view_apply, QueryCache.cacheQuery_of_ne _ _ (outside full)]

/-- Translate one full-prefix access into exactly one restoration access. -/
def translate : QueryImpl (Spec Input round) (OracleComp (TargetSpec Input round)) :=
  fun key => responseEquiv key <$> liftM ((TargetSpec Input round).query (encode key))

omit [DecidableEq Input] [DecidableEq round.Challenge] in
@[simp] theorem translate_first (z : Input) (first : round.Message) :
    translate (.inl (z, first)) =
      liftM ((TargetSpec Input round).query (StateRestoration.Key.here z first none)) := by
  change (id <$> (liftM ((TargetSpec Input round).query
    (StateRestoration.Key.here z first none)) : OracleComp _ round.Challenge)) = _
  exact id_map _

omit [DecidableEq Input] [DecidableEq round.Challenge] in
@[simp] theorem translate_second (z : Input) (first : round.Message)
    (challenge : round.Challenge) (second : round.Message) :
    translate (.inr (z, first, challenge, second)) =
      liftM ((TargetSpec Input round).query
        (StateRestoration.Key.later first none (StateRestoration.Key.here z second (some challenge)))) := by
  change (id <$> (liftM ((TargetSpec Input round).query
    (StateRestoration.Key.later first none (StateRestoration.Key.here z second (some challenge)))) :
      OracleComp _ round.Challenge)) = _
  exact id_map _

end ZkcSecurity.ArkLib.FiatShamir.Prefix
