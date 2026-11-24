module

public import Zkc.Core.Facts.Knowledge.Transfer
public import Zkc.Core.Facts.Body.LoopSound

@[expose] public section

namespace Zkc.Core.BodyAnalysis.Knowledge

variable {T Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {Typed : Val → T → Prop} {table : Table Raw} {ρ : Leaves Val}
    (functional : ∀ op xs ys zs, Run op xs ys → Run op xs zs → ys = zs) (slots : table.WF)

include functional slots in
private theorem numberIndex_sound {asks : Asks} {k : BufferedFacts} {L : Loop T} {N i : Nat} {v : Val}
    (external : asks.Sound Run R table ρ) (h : Means Run R k table ρ) (counts : L.Counts Run R table ρ N)
    (below : i < N) (read : Reads Run R.bool table ρ L.index v)
    (numbered : L.numbered = true → R.nat v = some i) : Means Run R (numberIndex asks k L) table ρ := by
  cases on : L.numbered with
  | false => simpa [numberIndex, on] using h
  | true =>
    obtain ⟨a, grounded, facts, found⟩ := withRead functional slots h read
    have iv := numbered on
    cases count : L.count with
    | inl n =>
      have eq : N = n := by simpa [Loop.Counts, count] using counts
      subst n
      simp only [numberIndex, on, count, ↓reduceIte]
      refine ⟨a, grounded, ?_⟩
      rw [BufferedFacts.view_addRange]
      exact facts.addRange ⟨v, found, iv⟩ ((Range.has_point.mpr rfl).below below)
    | inr id =>
      obtain ⟨x, countRead, value⟩ : ∃ x, Reads Run R.bool table ρ id x ∧ R.nat x = some N := by
        simpa [Loop.Counts, count] using counts
      have fits : (((rangeFor asks k id).map Range.below).getD ⟨0, none⟩).Has i := by
        cases bound : rangeFor asks k id with
        | none => exact ⟨Nat.zero_le _, fun _ eq => nomatch eq⟩
        | some r =>
          obtain ⟨n, num, fit⟩ := rangeFor_sound functional slots external h countRead bound
          rw [value] at num
          cases num
          exact fit.below below
      simp only [numberIndex, on, count, ↓reduceIte]
      refine rememberComparison_sound functional slots external ?_ read countRead iv value ?_
      · exact ⟨a, grounded, by simpa using facts.addRange ⟨v, found, iv⟩ fits⟩
      · intro state index bound assignment current atIndex atCount
        simpa using current.addOrder (strict := true) (byLoop := true) atIndex atCount below

include functional slots in
theorem enter_sound {types : KnowledgeTypes T} (law : types.Lawful R Typed)
    {asks : Asks} {k : BufferedFacts} {L : Loop T} {N i : Nat} {carried : List Val} {more : Leaves Val}
    (h : Means Run R k table ρ) (counts : L.Counts Run R table ρ N) (ext : ρ.Le more)
    (below : i < N) (atIteration : L.At Run R Typed table more i carried) (peer : asks.Sound Run R table more) :
    Means Run R (enter types asks k L) table more := by
  have live : L.count ≠ .inl 0 := by
    intro bad
    have eq : N = 0 := by simpa [Loop.Counts, bad] using counts
    omega
  obtain ⟨⟨v, read, typed, val⟩, carriedRead, _, typedAt⟩ := atIteration
  simp only [enter, live, ↓reduceIte]
  apply leaves_sound law functional slots _ (numberIndex_sound functional slots peer
    (mono (Table.Le.refl _) ext h) (counts.mono (Table.Le.refl _) ext)
    below read val)
  intro pair member
  rcases List.mem_cons.mp member with rfl | tail
  · exact ⟨v, read, typed⟩
  · obtain ⟨j, at_⟩ := List.mem_iff_getElem?.mp tail
    obtain ⟨idAt, typeAt⟩ := List.getElem?_zip_eq_some.mp at_
    obtain ⟨x, found, reads⟩ := carriedRead.get idAt
    exact ⟨x, reads, typedAt j x _ found typeAt⟩

end Zkc.Core.BodyAnalysis.Knowledge
