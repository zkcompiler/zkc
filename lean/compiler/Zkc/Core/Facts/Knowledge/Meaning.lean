module

public import Zkc.Core.Facts.Knowledge.Inference
public import Zkc.Core.Facts.Body.ValueLaws
public import Zkc.Core.Facts.Knowledge.BufferedFactsLaws
public import Zkc.Core.Facts.Knowledge.KnownLaws

@[expose] public section

namespace Zkc.Core.BodyAnalysis
open FactCheck (FormHolds)

/-- The observation laws speak only about successful runs and the two available queries. -/
structure KnowledgeOperations.Lawful {Raw Val : Type} (ops : KnowledgeOperations Raw)
    (R : Reading Val) (Run : Raw → List Val → List Val → Prop) : Prop where
  functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs
  form : ∀ op xs ys f, ops.form op = some f → Run op xs ys →
    ∃ v, ys.head? = some v ∧ FormHolds R f xs v
  preservesNumber : ∀ op xs ys, ops.preservesNumber op = true → Run op xs ys →
    ∃ source result, xs = [source] ∧ ys.head? = some result ∧ R.nat source = R.nat result
  ranges : ∀ op xs ys (known : List (Option Range)), Run op xs ys →
    (∀ (i : Nat) (r : Range), known[i]? = some (some r) → ∃ v n, xs[i]? = some v ∧ R.nat v = some n ∧ r.Has n) →
    ∀ (i : Nat) (r : Range), (ops.ranges op known)[i]? = some (some r) →
      ∃ v n, ys[i]? = some v ∧ R.nat v = some n ∧ r.Has n

end Zkc.Core.BodyAnalysis

namespace Zkc.Core.BodyAnalysis.Knowledge

open FactCheck (Valuation NatAt BoolAt)
variable {Raw Val T : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {Typed : Val → T → Prop} {table : Table Raw} {ρ : Leaves Val}

/-- Every assignment used as evidence for a cached fact has a reading of the same identifier. -/
def Grounded (Run : Raw → List Val → List Val → Prop) (R : Reading Val) (table : Table Raw)
    (ρ : Leaves Val) (assignment : Valuation Val) : Prop :=
  ∀ id v, assignment id.key = some v → Reads Run R.bool table ρ id v

/-- A partial assignment witnesses the existing fact semantics. It occurs only in the proof. -/
def Means (Run : Raw → List Val → List Val → Prop) (R : Reading Val) (k : BufferedFacts)
    (table : Table Raw) (ρ : Leaves Val) : Prop :=
  ∃ a : Valuation Val, Grounded Run R table ρ a ∧ k.toKnown.Holds R a

theorem mono {k : BufferedFacts} {other : Table Raw} {more : Leaves Val} (sub : table.Le other)
    (extend : ρ.Le more) (h : Means Run R k table ρ) : Means Run R k other more := by
  obtain ⟨a, grounded, facts⟩ := h
  exact ⟨a, fun id v found => (grounded id v found).mono sub extend, facts⟩

theorem empty : Means Run R BufferedFacts.empty table ρ :=
  ⟨fun _ => none, (fun _ _ h => nomatch h), rfl, fun _ _ m => (FactCheck.FactBuckets.not_mem_empty _ m).elim,
    fun _ m => (FactCheck.FactBuckets.not_mem_empty _ m).elim, fun _ _ m => (FactCheck.FactBuckets.not_mem_empty _ m).elim⟩

/-- Insert a newly witnessed reading into the finite evidence needed here.
Slot disjointness ensures this extends every earlier fact about the same key. -/
theorem Grounded.extendRead (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs) (slots : table.WF) {id : Ident} {v : Val}
    {old : Valuation Val} (grounded : Grounded Run R table ρ old) (read : Reads Run R.bool table ρ id v) :
    ∃ a : Valuation Val, Grounded Run R table ρ a ∧ old.Le a ∧ a id.key = some v := by
  let a : Valuation Val := fun key => if key = id.key then some v else old key
  have extend : old.Le a := by
    intro key x found
    by_cases same : key = id.key
    · subst key
      have eq := Reads.functionalOn functional slots read (grounded id x found)
      simp [a, eq]
    · simpa [a, same] using found
  refine ⟨a, ?_, extend, by simp [a]⟩
  intro other x found
  by_cases same : other.key = id.key
  · obtain rfl := Ident.key_injective same
    obtain rfl : v = x := by simpa [a] using found
    exact read
  · exact grounded other x (by simpa [a, same] using found)

theorem withRead (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs) (slots : table.WF) {k : BufferedFacts} {id : Ident} {v : Val}
    (h : Means Run R k table ρ) (read : Reads Run R.bool table ρ id v) :
    ∃ a : Valuation Val, Grounded Run R table ρ a ∧ k.toKnown.Holds R a ∧ a id.key = some v := by
  obtain ⟨old, grounded, facts⟩ := h
  obtain ⟨a, evidence, extendsOld, found⟩ := grounded.extendRead functional slots read
  exact ⟨a, evidence, facts.le extendsOld, found⟩

private theorem truth_boolAt {a : Valuation Val} {k : BufferedFacts} (facts : k.toKnown.Holds R a) (id : Ident)
    {b : Bool} (answered : truth k id = some b) : BoolAt R a id.key b := by
  unfold truth at answered
  dsimp only at answered
  split at answered
  · cases answered
    exact facts.hasTruth (by assumption)
  · split at answered
    · cases answered
      exact facts.hasTruth (by assumption)
    · cases answered

theorem answers_sound {k : BufferedFacts} (h : Means Run R k table ρ) : (answers k).Sound Run R table ρ := by
  obtain ⟨a, grounded, facts⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro id b reported
    obtain ⟨v, found, val⟩ := truth_boolAt facts id reported
    exact ⟨v, grounded _ _ found, val⟩
  · intro id p reported
    change k.pointOf id.key = some p at reported
    cases r : k.rangeOf id.key with
    | none => simp [BufferedFacts.pointOf, r] at reported
    | some range =>
      obtain ⟨n, hn, _⟩ := facts.rangeOf (by simpa only [BufferedFacts.view_rangeOf] using r)
      obtain rfl := facts.pointOf_at hn (by simpa only [BufferedFacts.view_pointOf] using reported)
      obtain ⟨v, found, val⟩ := hn
      exact ⟨v, grounded _ _ found, val⟩
  · intro id hi reported
    change (k.rangeOf id.key).bind Range.hi = some hi at reported
    obtain ⟨r, range, bound⟩ := Option.bind_eq_some_iff.mp reported
    obtain ⟨n, ⟨v, found, val⟩, fits⟩ := facts.rangeOf (by simpa only [BufferedFacts.view_rangeOf] using range)
    exact ⟨v, n, grounded _ _ found, val, fits.2 _ bound⟩

theorem leaves_sound {types : KnowledgeTypes T} (law : types.Lawful R Typed)
    (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs) (slots : table.WF) :
    ∀ (ids : List (Ident × T)) {k : BufferedFacts}, Means Run R k table ρ →
      (∀ p, p ∈ ids → ∃ v, Reads Run R.bool table ρ p.1 v ∧ Typed v p.2) →
      Means Run R (leaves types k ids) table ρ
  | [], _, h, _ => h
  | (id, t) :: rest, _, h, named => by
    obtain ⟨v, read, typed⟩ := named (id, t) List.mem_cons_self
    obtain ⟨a, grounded, facts, found⟩ := withRead functional slots h read
    simp only [leaves, law.inhabited typed, Bool.false_eq_true, ↓reduceIte]
    apply leaves_sound law functional slots rest
    · refine ⟨a, grounded, ?_⟩
      rw [BufferedFacts.view_addRange?]
      apply facts.addRange?
      intro r known
      obtain ⟨n, val, fits⟩ := law.range typed known
      exact ⟨n, ⟨v, found, val⟩, fits⟩
    · exact fun p m => named p (List.mem_cons_of_mem _ m)

theorem assume_sound {asks : Asks} {k : BufferedFacts} {id : Ident} {b : Bool} {v : Val}
    (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs) (slots : table.WF) (external : asks.Sound Run R table ρ)
    (h : Means Run R k table ρ) (read : Reads Run R.bool table ρ id v) (val : R.bool v = some b) :
    Means Run R (assume asks k id b) table ρ := by
  obtain ⟨a, grounded, facts, found⟩ := withRead functional slots h read
  have actual : BoolAt R a id.key b := ⟨v, found, val⟩
  have cached : k.hasTruth id.key (!b) = false := by
    cases prior : k.hasTruth id.key (!b) with
    | false => rfl
    | true =>
      obtain ⟨x, hx, opposite⟩ := facts.hasTruth prior
      rw [found] at hx
      cases hx
      rw [val] at opposite
      cases b <;> contradiction
  have peer : asks.truth id ≠ some (!b) := by
    intro prior
    obtain ⟨x, other, opposite⟩ := external.truth _ _ prior
    obtain rfl := Reads.functionalOn functional slots read other
    rw [val] at opposite
    cases b <;> contradiction
  simp only [assume, cached, Bool.false_or, beq_iff_eq, peer, ↓reduceIte]
  exact ⟨a, grounded, facts.addTruth actual⟩

#print axioms withRead
#print axioms leaves_sound
#print axioms assume_sound
end Zkc.Core.BodyAnalysis.Knowledge
