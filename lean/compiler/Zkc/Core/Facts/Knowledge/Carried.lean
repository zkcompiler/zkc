module

public import Zkc.Core.Facts.Knowledge.Forms
public import Zkc.Core.Facts.Knowledge.Loop

@[expose] public section

namespace Zkc.Core.BodyAnalysis.Knowledge

variable {T Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {Typed : Val → T → Prop} {table : Table Raw} {ρ : Leaves Val}

abbrev LoopHistory (Run : Raw → List Val → List Val → Prop) (R : Reading Val) (Typed : Val → T → Prop)
    (L : Loop T) (out : BufferedFacts) (exit : Asks) (table : Table Raw) (ρ : Leaves Val)
    (returned : List Ident) (carried : Nat → List Val) (N : Nat) : Prop :=
  ∀ k, k < N → ∃ more, ρ.Le more ∧ L.At Run R Typed table more k (carried k) ∧
    Means Run R out table more ∧ exit.Sound Run R table more ∧ ReadsAll Run R.bool table more returned (carried (k+1))

private theorem sum_step {ops : KnowledgeOperations Raw} (laws : ops.Lawful R Run) (slots : table.WF)
    {out : BufferedFacts} {exit : Asks} {cid ret term : Ident} {growth : Range} {v next : Val} {n : Nat}
    (form : addedTerm ops table cid ret = some term) (bound : rangeFor exit out term = some growth)
    (peer : exit.Sound Run R table ρ) (h : Means Run R out table ρ) (old : Reads Run R.bool table ρ cid v)
    (result : Reads Run R.bool table ρ ret next) (num : R.nat v = some n) :
    ∃ t, growth.Has t ∧ R.nat next = some (n+t) := by
  obtain ⟨op, sum, shape | shape⟩ := addedTerm_spec form
  · obtain ⟨a,b,x,y,first,second,na,nb,nv⟩ := reads_sum laws slots sum shape result
    obtain rfl := Reads.functionalOn laws.functional slots old first
    rw [num] at na
    cases na
    obtain ⟨m, same, fits⟩ := rangeFor_sound laws.functional slots peer h second bound
    rw [nb] at same
    cases same
    exact ⟨_, fits, nv⟩
  · obtain ⟨a,b,x,y,first,second,na,nb,nv⟩ := reads_sum laws slots sum shape result
    obtain rfl := Reads.functionalOn laws.functional slots old second
    rw [num] at nb
    cases nb
    obtain ⟨m, same, fits⟩ := rangeFor_sound laws.functional slots peer h first bound
    rw [na] at same
    cases same
    exact ⟨_, fits, by simpa [Nat.add_comm] using nv⟩

private theorem iterationBound_sound {asks : Asks} {k : BufferedFacts} {count : Nat ⊕ Ident} {N : Nat}
    (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs) (slots : table.WF)
    (peer : asks.Sound Run R table ρ) (h : Means Run R k table ρ)
    (counts : match count with
      | .inl n => N = n
      | .inr id => ∃ v, Reads Run R.bool table ρ id v ∧ R.nat v = some N) :
    ∀ hi, iterationBound asks k count = some hi → N ≤ hi := by
  cases count with
  | inl n => intro hi found; cases found; exact Nat.le_of_eq counts
  | inr id =>
    intro hi found
    obtain ⟨v, read, val⟩ := counts
    obtain ⟨r, bound, top⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨n, num, fit⟩ := rangeFor_sound functional slots peer h read bound
    rw [val] at num
    cases num
    exact fit.2 _ top

private theorem accumulate {ops : KnowledgeOperations Raw} (laws : ops.Lawful R Run) (slots : table.WF)
    {L : Loop T} {out : BufferedFacts} {exit : Asks} {N j : Nat} {returned : List Ident} {carried : Nat → List Val}
    {cid ret term : Ident} {start growth : Range}
    (history : LoopHistory Run R Typed L out exit table ρ returned carried N)
    (cidAt : L.carried[j]? = some cid) (retAt : returned[j]? = some ret)
    (termAt : addedTerm ops table cid ret = some term) (termBound : rangeFor exit out term = some growth)
    (base : ∃ v n, (carried 0)[j]? = some v ∧ R.nat v = some n ∧ start.Has n) :
    ∀ i, i ≤ N → ∃ v n, (carried i)[j]? = some v ∧ R.nat v = some n ∧
      (Range.afterSums start growth (some i)).Has n
  | 0, _ => by
    obtain ⟨v,n,at_,num,fits⟩ := base
    exact ⟨v,n,at_,num,Range.afterSums_zero fits⟩
  | i+1, le => by
    obtain ⟨v,n,at_,num,fits⟩ := accumulate laws slots history cidAt retAt termAt termBound base i
      (Nat.le_of_succ_le le)
    obtain ⟨_, _, iteration, held, peer, result⟩ := history i le
    obtain ⟨x, same, read⟩ := iteration.2.1.get cidAt
    rw [at_] at same
    cases same
    obtain ⟨next, nextAt, nextRead⟩ := result.get retAt
    obtain ⟨t, growthHas, numNext⟩ := sum_step laws slots termAt termBound peer held read nextRead num
    exact ⟨next, n+t, nextAt, numNext, Range.afterSums_step fits growthHas⟩

theorem afterLoop_sound {ops : KnowledgeOperations Raw} (laws : ops.Lawful R Run) (slots : table.WF)
    {before exit : Asks} {k out : BufferedFacts} {L : Loop T} {returned made : List Ident} {more : Leaves Val}
    {N : Nat} {carried : Nat → List Val}
    (peer : before.Sound Run R table ρ) (h : Means Run R k table ρ) (counts : L.Counts Run R table ρ N)
    (initial : ReadsAll Run R.bool table ρ L.initial (carried 0))
    (history : LoopHistory Run R Typed L out exit table ρ returned carried N) (ext : ρ.Le more)
    (results : ReadsAll Run R.bool table more made (carried N)) :
    Means Run R (afterLoop ops before exit table k L out returned made) table more := by
  let high := iterationBound before k L.count
  have highOK : ∀ hi, high = some hi → N ≤ hi := iterationBound_sound laws.functional slots peer h counts
  apply learnRanges_sound laws.functional slots results 0 _ (mono (Table.Le.refl _) ext h)
  intro j v bound endAt found
  simp only [Nat.zero_add, Option.bind_eq_bind, Option.bind_eq_some_iff] at found
  obtain ⟨input, inputAt, cid, cidAt, ret, retAt, range⟩ := found
  change carriedRange ops table before exit k out high input cid ret = some bound at range
  simp only [carriedRange, Option.bind_eq_bind, Option.bind_eq_some_iff] at range
  obtain ⟨start, startAt, range⟩ := range
  obtain ⟨v₀, baseAt, baseRead⟩ := initial.get inputAt
  obtain ⟨n₀, baseNum, baseFits⟩ := rangeFor_sound laws.functional slots peer h baseRead startAt
  split at range
  · next zero =>
    have same : N = 0 := by
      rcases Bool.or_eq_true_iff.mp zero with dead | bounded
      · cases N with
        | zero => rfl
        | succ N =>
          obtain ⟨_,_,_,⟨_,_,facts⟩,_,_⟩ := history 0 (Nat.zero_lt_succ _)
          change out.toKnown.dead = true at dead
          rw [facts.alive] at dead
          cases dead
      · exact Nat.eq_zero_of_le_zero (highOK 0 (beq_iff_eq.mp bounded))
    subst N
    rw [baseAt] at endAt
    cases endAt
    cases range
    exact ⟨n₀, baseNum, baseFits⟩
  · simp only [Option.bind_eq_some_iff, Option.pure_def] at range
    obtain ⟨term, form, growth, grows, same⟩ := range
    cases same
    obtain ⟨v',n,at_,num,fits⟩ := accumulate laws slots history cidAt retAt form grows
      ⟨v₀,n₀,baseAt,baseNum,baseFits⟩ N (Nat.le_refl _)
    rw [endAt] at at_
    cases at_
    exact ⟨n,num,Range.afterSums_widen fits highOK⟩

end Zkc.Core.BodyAnalysis.Knowledge
