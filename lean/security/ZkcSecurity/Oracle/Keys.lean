module

public import ZkcSecurity.FiatShamir.Interface
public import ZkcSecurity.VCVio.Deferral
public import ZkcSecurity.Commitment.TableLog
public import VCVio.ProgramLogic.Relational.SimulateQ.Coupling
public import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad
public import VCVio.OracleComp.Constructions.SampleableType.Measure

@[expose] public section

/-! # Transport between oracle key forms

A lazily sampled random oracle can be keyed in several ways: by event
histories, as the typed engine asks it, or by pairs of a history and an
occurrence, as the commitment bridge's joint oracle asks it. A renaming of
oracle cells (`Renaming`) sends each source key to a target cell, or answers it
locally when its answer type has a single value, and reads each target answer
back by an equivalence. It need not be onto: the target may have cells no source
key reaches.

**Transport.** An adversary on the source oracle runs against the target oracle
through the renaming (`Renaming.translate`): every source query, malformed and
empty keys included, asks its target cell and reads the answer back, or is
answered locally. The lazily sampled executions from the empty cache have the
same law (`Renaming.evalDistEq_translate`, `Renaming.prEvent_translate`): the
proof couples the two caches query by query, the target cell of a source key
holding the source answer read through the equivalence, and fresh answers
related by the equivalence, under which uniform answers stay uniform. Costs
transport too: the translated adversary makes no more queries
(`Renaming.translate_queryBound`), and its weighted cost under a target weight is
the source adversary's under the weight of each key's target cell, zero for a
key answered locally (`Renaming.translate_costBound`).

**Pair keys and terminated histories.** Pairs `(preceding, occurrence)`
answered in the occurrence's raw type rename into the histories
`preceding ++ [occurrence]` with raw answers by the last event
(`pairToHistory`); histories rename into pairs by splitting off the last event,
the empty history being answered locally because its answer type `Unit` has a
single value (`historyToPair`). The per-key charge `keyCharge charge` of a
history is the pair weight `charge` of its target pair (`historyToPair_weight`).
For a history oracle whose range does not depend on the key, the empty history's
answer is not a single value, so only the direction from pairs is a renaming.
-/

set_option autoImplicit false

namespace ZkcSecurity.Oracle
open OracleComp OracleSpec OracleComp.ProgramLogic.Relational

/-- A renaming of oracle cells from source keys `D` with answers `R` to target
keys `D'` with answers `R'`: each source key's target cell, or `none` for a key
answered locally; how an answer of the target cell reads as a source answer; and,
for a key answered locally, that its answer type has a single value. Distinct
source keys never share a target cell. -/
structure Renaming {D D' : Type} (R : D → Type) (R' : D' → Type) where
  cell : D → Option D'
  injective : ∀ first second target, cell first = some target → cell second = some target →
    first = second
  read : (key : D) → (target : D') → cell key = some target → R' target ≃ R key
  single : (key : D) → cell key = none → R key ≃ Unit

namespace Renaming
variable {D D' α : Type} {R : D → Type} {R' : D' → Type}

/-- One source query through the renaming: its target cell read back, or its
single local answer. -/
def ask (keys : Renaming R R') (key : D) : OracleComp (OracleSpec.ofFn R') (R key) :=
  match hit : keys.cell key with
  | some target => keys.read key target hit <$> liftM ((OracleSpec.ofFn R').query target)
  | none => pure ((keys.single key hit).symm ())

theorem ask_some (keys : Renaming R R') {key : D} {target : D'} (hit : keys.cell key = some target) :
    keys.ask key = keys.read key target hit <$> liftM ((OracleSpec.ofFn R').query target) := by
  unfold ask
  split
  · rename_i other found
    obtain rfl : other = target := Option.some.inj (found.symm.trans hit)
    rfl
  · rename_i found
    exact absurd (found.symm.trans hit) (by simp)

theorem ask_none (keys : Renaming R R') {key : D} (hit : keys.cell key = none) :
    keys.ask key = pure ((keys.single key hit).symm ()) := by
  unfold ask
  split
  · rename_i other found
    exact absurd (found.symm.trans hit) (by simp)
  · rfl

/-- An adversary on the source oracle, run against the target oracle through the
renaming. -/
def translate (keys : Renaming R R') (adversary : OracleComp (OracleSpec.ofFn R) α) :
    OracleComp (OracleSpec.ofFn R') α :=
  simulateQ keys.ask adversary

theorem translate_pure (keys : Renaming R R') (value : α) :
    keys.translate (pure value) = pure value := by
  simp [translate]

theorem translate_query_bind (keys : Renaming R R') (key : D)
    (next : R key → OracleComp (OracleSpec.ofFn R) α) :
    keys.translate (liftM ((OracleSpec.ofFn R).query key) >>= next) =
      keys.ask key >>= fun answer => keys.translate (next answer) := by
  simp [translate]

section Costs

/-- The translated adversary makes no more queries than the source adversary. -/
theorem translate_queryBound (keys : Renaming R R') :
    ∀ (adversary : OracleComp (OracleSpec.ofFn R) α) (queries : ℕ),
      IsTotalQueryBound adversary queries →
        IsTotalQueryBound (keys.translate adversary) queries := by
  intro adversary
  induction adversary using OracleComp.inductionOn with
  | pure value => intro queries _; rw [translate_pure]; trivial
  | query_bind key next ih =>
      intro queries bounded
      obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bounded
      rw [translate_query_bind]
      cases hit : keys.cell key with
      | some target =>
          rw [ask_some keys hit, bind_map_left]
          exact isTotalQueryBound_query_bind_iff.mpr ⟨positive, fun answer => ih _ _ (rest _)⟩
      | none =>
          rw [ask_none keys hit, pure_bind]
          exact (ih _ _ (rest _)).mono (Nat.sub_le _ _)

/-- The weight of a source key: the weight of its target cell, zero when it is
answered locally. -/
def weight (keys : Renaming R R') (targetWeight : D' → ENNReal) (key : D) : ENNReal :=
  (keys.cell key).elim 0 targetWeight

/-- The translated adversary's weighted cost under a target weight is at most the
source adversary's under the weight of each key's target cell. -/
theorem translate_costBound [∀ key, Nonempty (R key)] (keys : Renaming R R')
    (targetWeight : D' → ENNReal) :
    ∀ (adversary : OracleComp (OracleSpec.ofFn R) α) (cost : ENNReal),
      WorstCaseCostBound adversary ⟨keys.weight targetWeight⟩ cost →
        WorstCaseCostBound (keys.translate adversary) ⟨targetWeight⟩ cost := by
  intro adversary
  induction adversary using OracleComp.inductionOn with
  | pure value =>
      intro cost _
      rw [translate_pure]
      exact (worstCaseCostBound_pure _ _ _).mpr zero_le
  | query_bind key next ih =>
      intro cost bounded
      rw [worstCaseCostBound_query_bind_iff] at bounded
      rw [translate_query_bind]
      by_cases top : cost = ⊤
      · subst top
        exact (worstCaseCostBound_iff_support_bound _ _ _).mpr fun _ _ => le_top
      obtain ⟨answer⟩ := (inferInstance : Nonempty (R key))
      obtain ⟨path, member⟩ := support_nonempty (costDist (next answer) ⟨keys.weight targetWeight⟩)
      have charged : keys.weight targetWeight key ≤ cost :=
        le_trans le_self_add (bounded answer path member)
      have finite : keys.weight targetWeight key ≠ ⊤ := ne_top_of_le_ne_top top charged
      have rest : ∀ value, WorstCaseCostBound (keys.translate (next value)) ⟨targetWeight⟩
          (cost - keys.weight targetWeight key) := fun value =>
        ih value _ ((worstCaseCostBound_iff_support_bound _ _ _).mpr fun path member =>
          ENNReal.le_sub_of_add_le_left finite (bounded value path member))
      cases hit : keys.cell key with
      | some target =>
          rw [ask_some keys hit, bind_map_left, worstCaseCostBound_query_bind_iff]
          intro value path member
          have tail := (worstCaseCostBound_iff_support_bound _ _ _).mp (rest _) path member
          have weighed : keys.weight targetWeight key = targetWeight target := by
            simp [weight, hit]
          calc targetWeight target + Multiplicative.toAdd path.2
              ≤ keys.weight targetWeight key + (cost - keys.weight targetWeight key) :=
                add_le_add (le_of_eq weighed.symm) tail
            _ = cost := add_tsub_cancel_of_le charged
      | none =>
          rw [ask_none keys hit, pure_bind]
          have weighed : keys.weight targetWeight key = 0 := by simp [weight, hit]
          simpa [weighed] using rest ((keys.single key hit).symm ())

end Costs

section Tables

/-- A target answer table read back as a source answer table: a source key's answer is its
target cell's answer read back, or its single local answer. -/
def pullback (keys : Renaming R R') (table : (target : D') → R' target) (key : D) : R key :=
  match hit : keys.cell key with
  | some target => keys.read key target hit (table target)
  | none => (keys.single key hit).symm ()

theorem pullback_some (keys : Renaming R R') (table : (target : D') → R' target) {key : D}
    {target : D'} (hit : keys.cell key = some target) :
    keys.pullback table key = keys.read key target hit (table target) := by
  unfold pullback
  split
  · rename_i other found
    obtain rfl : other = target := Option.some.inj (found.symm.trans hit)
    rfl
  · rename_i found
    exact absurd (found.symm.trans hit) (by simp)

theorem pullback_none (keys : Renaming R R') (table : (target : D') → R' target) {key : D}
    (hit : keys.cell key = none) : keys.pullback table key = (keys.single key hit).symm () := by
  unfold pullback
  split
  · rename_i other found
    exact absurd (found.symm.trans hit) (by simp)
  · rfl

/-- One source query through the renaming, against a target table, answers the source key from
the table read back. -/
theorem evalWithAnswerFn_ask (keys : Renaming R R') (table : (target : D') → R' target) (key : D) :
    evalWithAnswerFn (QueryImpl.ofFn table) (keys.ask key) = keys.pullback table key := by
  cases hit : keys.cell key with
  | some target =>
      rw [ask_some keys hit, pullback_some keys table hit]
      rfl
  | none =>
      rw [ask_none keys hit, pullback_none keys table hit]
      rfl

/-- Against a target table, the translated adversary returns what the source adversary returns
against that table read back. -/
theorem evalWithAnswerFn_translate (keys : Renaming R R') (table : (target : D') → R' target) :
    ∀ adversary : OracleComp (OracleSpec.ofFn R) α,
      evalWithAnswerFn (QueryImpl.ofFn table) (keys.translate adversary) =
        evalWithAnswerFn (QueryImpl.ofFn (keys.pullback table)) adversary := by
  intro adversary
  induction adversary using OracleComp.inductionOn with
  | pure value => rw [translate_pure]; rfl
  | query_bind key next ih =>
      rw [translate_query_bind, evalWithAnswerFn_bind, evalWithAnswerFn_ask, ih,
        evalWithAnswerFn_bind]
      rfl

/-- Against a target table, the translated adversary asks the target cells of the source
adversary's keys against that table read back, in order; locally answered keys ask nothing. -/
theorem tableQueryLog_translate (keys : Renaming R R') (table : (target : D') → R' target) :
    ∀ adversary : OracleComp (OracleSpec.ofFn R) α,
      (tableQueryLog (keys.translate adversary) table).map Sigma.fst =
        ((tableQueryLog adversary (keys.pullback table)).map Sigma.fst).filterMap keys.cell := by
  intro adversary
  induction adversary using OracleComp.inductionOn with
  | pure value => simp [translate_pure]
  | query_bind key next ih =>
      rw [translate_query_bind, tableQueryLog_bind, evalWithAnswerFn_ask, tableQueryLog_query_bind,
        List.map_append, ih]
      cases hit : keys.cell key with
      | some target =>
          rw [ask_some keys hit, ZkcSecurity.Commitment.tableQueryLog_map]
          simp [hit, pullback_some keys table hit]
      | none =>
          rw [ask_none keys hit]
          simp [hit, pullback_none keys table hit]

end Tables

section Law
variable [DecidableEq D] [DecidableEq D'] [∀ key, SampleableType (R key)]
  [∀ target, SampleableType (R' target)]

/-- The source cache and the target cache agree through the renaming: a source
key with a target cell holds that cell's answer read back, and target cells no
source key reaches are empty. -/
def Related (keys : Renaming R R') (source : (OracleSpec.ofFn R).QueryCache)
    (target : (OracleSpec.ofFn R').QueryCache) : Prop :=
  (∀ key cell (hit : keys.cell key = some cell), source key = (target cell).map (keys.read key cell hit)) ∧
  ∀ cell, (∀ key, keys.cell key ≠ some cell) → target cell = none

omit [DecidableEq D] [DecidableEq D'] [∀ key, SampleableType (R key)]
  [∀ target, SampleableType (R' target)] in
theorem related_empty (keys : Renaming R R') : keys.Related ∅ ∅ :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

omit [∀ key, SampleableType (R key)] [∀ target, SampleableType (R' target)] in
/-- Caching related answers at a source key and at its target cell keeps the
caches related. -/
theorem related_cacheQuery (keys : Renaming R R') {source : (OracleSpec.ofFn R).QueryCache}
    {target : (OracleSpec.ofFn R').QueryCache} (related : keys.Related source target) {key : D}
    {cell : D'} (hit : keys.cell key = some cell) (value : R' cell) :
    keys.Related (source.cacheQuery key (keys.read key cell hit value))
      (target.cacheQuery cell value) := by
  obtain ⟨agree, untouched⟩ := related
  refine ⟨fun key' cell' hit' => ?_, fun cell' unreached => ?_⟩
  · by_cases here : key' = key
    · subst here
      obtain rfl : cell' = cell := Option.some.inj (hit'.symm.trans hit)
      rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
      rfl
    · have away : cell' ≠ cell := fun same =>
        here (keys.injective key' key cell (same ▸ hit') hit)
      rw [QueryCache.cacheQuery_of_ne _ _ here, QueryCache.cacheQuery_of_ne _ _ away]
      exact agree key' cell' hit'
  · have different : cell' ≠ cell := fun equal => unreached key (by rw [hit, equal])
    rw [QueryCache.cacheQuery_of_ne _ _ different]
    exact untouched cell' unreached

omit [DecidableEq D'] [∀ key, SampleableType (R key)] [∀ target, SampleableType (R' target)] in
/-- Caching any answer at a source key answered locally keeps the caches
related. -/
theorem related_cacheQuery_local (keys : Renaming R R') {source : (OracleSpec.ofFn R).QueryCache}
    {target : (OracleSpec.ofFn R').QueryCache} (related : keys.Related source target) {key : D}
    (hit : keys.cell key = none) (answer : R key) :
    keys.Related (source.cacheQuery key answer) target := by
  obtain ⟨agree, untouched⟩ := related
  refine ⟨fun key' cell' hit' => ?_, untouched⟩
  have here : key' ≠ key := by
    rintro rfl
    exact absurd (hit.symm.trans hit') (by simp)
  rw [QueryCache.cacheQuery_of_ne _ _ here]
  exact agree key' cell' hit'

/-- One query through the renaming is coupled with the source query: equal
answers and caches that stay related. -/
theorem query_step (keys : Renaming R R') (key : D) (source : (OracleSpec.ofFn R).QueryCache)
    (target : (OracleSpec.ofFn R').QueryCache) (related : keys.Related source target) :
    RelTriple ((randomOracle key).run source) ((simulateQ randomOracle (keys.ask key)).run target)
      (fun first second => first.1 = second.1 ∧ keys.Related first.2 second.2) := by
  rw [randomOracle.run_eq]
  cases hit : keys.cell key with
  | some cell =>
      have known : source key = (target cell).map (keys.read key cell hit) := related.1 key cell hit
      rw [ask_some keys hit, simulateQ_map, simulateQ_spec_query, StateT.run_map,
        randomOracle.run_eq]
      cases cached : target cell with
      | some value =>
          rw [cached] at known
          rw [known]
          exact relTriple_pure_pure ⟨rfl, related⟩
      | none =>
          rw [cached] at known
          rw [known]
          simp only [map_bind, map_pure]
          refine relTriple_of_evalDistEq_right
            (ob := ($ᵗ R key : ProbComp (R key)) >>= fun answer =>
              pure (answer, target.cacheQuery cell ((keys.read key cell hit).symm answer))) ?_ ?_
          · calc (($ᵗ R key : ProbComp (R key)) >>= fun answer =>
                  pure (answer, target.cacheQuery cell ((keys.read key cell hit).symm answer)))
                =ᵈ (((keys.read key cell hit).symm <$> ($ᵗ R key : ProbComp (R key))) >>= fun value =>
                    pure (keys.read key cell hit value, target.cacheQuery cell value)) := by
                  rw [bind_map_left]
                  simp only [Equiv.apply_symm_apply]; rfl
              _ =ᵈ _ := (SampleableType.map_uniformSample_evalDistEq_of_bijective (keys.read key cell hit).symm.bijective).bind_left _
          · refine relTriple_bind relTriple_uniformSample_refl fun answer other same => ?_
            cases same
            have stays := related_cacheQuery keys related hit ((keys.read key cell hit).symm answer)
            simp only [Equiv.apply_symm_apply] at stays
            exact relTriple_pure_pure ⟨rfl, stays⟩
  | none =>
      rw [ask_none keys hit, simulateQ_pure, StateT.run_pure]
      have single : ∀ answer : R key, answer = (keys.single key hit).symm () := fun answer =>
        (keys.single key hit).injective (Subsingleton.elim _ _)
      cases cached : source key with
      | some answer =>
          exact relTriple_pure_pure ⟨single answer, related⟩
      | none =>
          rw [show (pure ((keys.single key hit).symm (), target) :
              ProbComp (R key × (OracleSpec.ofFn R').QueryCache)) =
            (pure () : ProbComp Unit) >>= fun _ => pure ((keys.single key hit).symm (), target) from
              (pure_bind _ _).symm]
          refine relTriple_bind (relTriple_true _ _) fun answer _ _ => ?_
          exact relTriple_pure_pure ⟨single answer, related_cacheQuery_local keys related hit answer⟩

/-- The lazily sampled execution of a translated adversary from the empty cache
has the law of the source adversary's. -/
theorem evalDistEq_translate (keys : Renaming R R') (adversary : OracleComp (OracleSpec.ofFn R) α) :
    ((simulateQ randomOracle (keys.translate adversary)).run' ∅) =ᵈ ((simulateQ randomOracle adversary).run' ∅) := by
  have coupled := relTriple_simulateQ_run randomOracle
    (fun key => simulateQ randomOracle (keys.ask key)) keys.Related adversary
    (fun key source target related => keys.query_step key source target related) ∅ ∅
    keys.related_empty
  rw [translate, ← QueryImpl.simulateQ_compose]
  symm
  refine evalDistEq_of_relTriple_eqRel ?_
  simp only [StateT.run'_eq]
  exact relTriple_map (relTriple_post_mono coupled fun first second related => related.1)

/-- Every event of the translated adversary's execution has the probability of
the same event of the source adversary's execution. -/
theorem prEvent_translate (keys : Renaming R R') (adversary : OracleComp (OracleSpec.ofFn R) α)
    (event : α → Prop) :
    Pr{let result ← (simulateQ randomOracle (keys.translate adversary)).run' ∅}[event result] =
      Pr{let result ← (simulateQ randomOracle adversary).run' ∅}[event result] :=
  _root_.EvalDistEq.prEvent_eq (keys.evalDistEq_translate adversary) event

end Law

end Renaming

section Pairs
variable {E : Type} (Raw : E → Type)
open ZkcSecurity.FiatShamir.Typed

/-- Pair keys rename into the terminated histories: `(preceding, occurrence)` is
the history `preceding ++ [occurrence]`, whose answer reads in the occurrence's
raw type. -/
def pairToHistory : Renaming (fun key : List E × E => Raw key.2) (ByLast Raw) where
  cell key := some (key.1 ++ [key.2])
  injective first second target found other := by
    obtain rfl := Option.some.inj found
    obtain ⟨prefixes, lasts⟩ := List.append_inj' (Option.some.inj other) rfl
    exact Prod.ext prefixes.symm (List.singleton_inj.mp lasts).symm
  read key target found := by
    obtain rfl := Option.some.inj found
    exact ByLast.read Raw
  single key found := by cases found

/-- Histories rename into pairs: a nonempty history is its prefix before the
last event and that event; the empty history, whose answer type is `Unit`, is
answered locally. -/
def historyToPair : Renaming (ByLast Raw) (fun key : List E × E => Raw key.2) where
  cell key := key.getLast?.map fun last => (key.dropLast, last)
  injective first second target found other := by
    obtain ⟨last, firstLast, firstPair⟩ := Option.map_eq_some_iff.mp found
    obtain ⟨last', secondLast, secondPair⟩ := Option.map_eq_some_iff.mp other
    rw [← secondPair] at firstPair
    obtain ⟨prefixes, rfl⟩ := Prod.mk.inj firstPair
    rw [← List.dropLast_append_getLast? _ firstLast, ← List.dropLast_append_getLast? _ secondLast, prefixes]
  read key target found := Equiv.cast (by
    obtain ⟨last, found', rfl⟩ := Option.map_eq_some_iff.mp found
    simp [ByLast, OfLast, found'])
  single key found := Equiv.cast (by
    rw [Option.map_eq_none_iff] at found
    simp [ByLast, OfLast, found])

/-- The pair weight of a history's target pair is the per-key charge of the
history. -/
theorem historyToPair_weight (charge : List E → E → ENNReal) (key : List E) :
    (historyToPair Raw).weight (fun pair => charge pair.1 pair.2) key = keyCharge charge key := by
  unfold Renaming.weight keyCharge
  simp only [historyToPair]
  cases key.getLast? <;> rfl

end Pairs

end ZkcSecurity.Oracle
