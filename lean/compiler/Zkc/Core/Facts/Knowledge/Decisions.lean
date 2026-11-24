module

public import Zkc.Core.Facts.Knowledge.Offsets
public import Zkc.Core.Facts.Domains.Product

@[expose] public section

namespace Zkc.Core.BodyAnalysis.Knowledge

variable {Raw Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {table : Table Raw} {ρ : Leaves Val} {ops : KnowledgeOperations Raw}
    (laws : ops.Lawful R Run) (slots : table.WF) {asks : Asks}
    (external : asks.Sound Run R table ρ) {k : BufferedFacts} (h : Means Run R k table ρ)

include laws slots external h in
private theorem separates_sound {term : Ident} {v : Val} {t : Nat} {strict : Bool}
    (read : Reads Run R.bool table ρ term v) (num : R.nat v = some t)
    (yes : separates asks k strict (some term) = true) : strict = true → 0 < t := by
  intro enabled
  subst strict
  cases found : rangeFor asks k term with
  | none => simp [separates, found] at yes
  | some r =>
    have positive : 0 < r.lo := by simpa [separates, found] using yes
    obtain ⟨n, val, fit⟩ := rangeFor_sound laws.functional slots external h read found
    rw [num] at val
    cases val
    exact Nat.lt_of_lt_of_le positive fit.1

include laws slots in
private theorem sumParts {a b term : Ident} {va vb : Val} {x y : Nat}
    (ra : Reads Run R.bool table ρ a va) (rb : Reads Run R.bool table ρ b vb)
    (na : R.nat va = some x) (nb : R.nat vb = some y) (found : addedTerm ops table a b = some term) :
    ∃ v n, Reads Run R.bool table ρ term v ∧ R.nat v = some n ∧ y = x+n := by
  obtain ⟨op,sum,shape | shape⟩ := addedTerm_spec found
  · obtain ⟨_,_,_,_,first,second,ix,iy,res⟩ := reads_sum laws slots sum shape rb
    obtain rfl := Reads.functionalOn laws.functional slots ra first
    rw [na] at ix
    rw [nb] at res
    exact ⟨_,_,second,iy,by simp_all⟩
  · obtain ⟨_,_,_,_,first,second,ix,iy,res⟩ := reads_sum laws slots sum shape rb
    obtain rfl := Reads.functionalOn laws.functional slots ra second
    rw [na] at iy
    rw [nb] at res
    exact ⟨_,_,first,ix,by simp_all [Nat.add_comm]⟩

include laws slots external h in
private theorem sumOrder {a b : Ident} {va vb : Val} {x y : Nat} {strict : Bool}
    (ra : Reads Run R.bool table ρ a va) (rb : Reads Run R.bool table ρ b vb)
    (na : R.nat va = some x) (nb : R.nat vb = some y)
    (found : separates asks k strict (addedTerm ops table a b) = true) :
    if strict then x < y else x ≤ y := by
  cases atTerm : addedTerm ops table a b with
  | none => simp [atTerm,separates] at found
  | some t =>
    rw [atTerm] at found
    obtain ⟨_,_,read,numeric,rfl⟩ := sumParts laws slots ra rb na nb atTerm
    have positive := separates_sound laws slots external h read numeric found
    cases strict <;> simp_all <;> omega

include laws slots external h in
private theorem zeroAddend_sound {a b : Ident} {va vb : Val} {x y : Nat}
    (ra : Reads Run R.bool table ρ a va) (rb : Reads Run R.bool table ρ b vb)
    (na : R.nat va = some x) (nb : R.nat vb = some y) (found : zeroAddend ops table asks k a b = true) : y = x := by
  cases atTerm : addedTerm ops table a b with
  | none => simp [zeroAddend, atTerm] at found
  | some t =>
    have zero : (asks.orElse (answers k)).exact t = some 0 := by simpa [zeroAddend, atTerm] using found
    obtain ⟨_,n,read,numeric,rfl⟩ := sumParts laws slots ra rb na nb atTerm
    obtain ⟨_,other,value⟩ := (external.orElse (answers_sound h)).exact _ _ zero
    obtain rfl := Reads.functionalOn laws.functional slots read other
    rw [numeric] at value
    simp [Option.some.inj value]

include laws slots external h in
private theorem differenceOrder {a b : Ident} {va vb : Val} {x y : Nat} {strict : Bool}
    (ra : Reads Run R.bool table ρ a va) (rb : Reads Run R.bool table ρ b vb)
    (na : R.nat va = some x) (nb : R.nat vb = some y)
    (found : separates asks k strict (subtractedTerm ops table a b) = true) :
    if strict then x < y else x ≤ y := by
  unfold subtractedTerm at found
  split at found
  · next minuend term form =>
    split at found
    · next same =>
      subst minuend
      obtain ⟨_, reads, u, v, m, n, rfl, nu, nv, fits, res⟩ := resultForm_reads laws slots form ra
      cases reads with | cons first tail => cases tail with | cons second _ =>
        obtain rfl := Reads.functionalOn laws.functional slots rb first
        rw [nb] at nu
        rw [na] at res
        have := separates_sound laws slots external h second nv found
        cases strict <;> simp_all <;> omega
    · contradiction
  · contradiction

include laws slots external h in
private theorem sameNumber_sound {a b : Ident} {va vb : Val} {x y : Nat}
    (ra : Reads Run R.bool table ρ a va) (rb : Reads Run R.bool table ρ b vb)
    (na : R.nat va = some x) (nb : R.nat vb = some y) (found : sameNumber asks k a b = true) : x = y := by
  obtain same | points := Bool.or_eq_true_iff.mp found
  · obtain ⟨_, readA, numA⟩ := external.numberAt_reads laws.functional slots ra
    obtain ⟨_, readB, numB⟩ := external.numberAt_reads laws.functional slots rb
    rw [beq_iff_eq.mp same] at readA
    cases Reads.functionalOn laws.functional slots readA readB
    exact Option.some.inj (na.symm.trans (numA.symm.trans (numB.trans nb)))
  · let q := asks.orElse (answers k)
    have sound : q.Sound Run R table ρ := external.orElse (answers_sound h)
    change (q.exact a).any _ = true at points
    cases atA : q.exact a with
    | none => simp [atA] at points
    | some n =>
      have atB : q.exact b = some n := by simpa [atA] using points
      obtain ⟨_,readA,numA⟩ := sound.exact _ _ atA
      obtain ⟨_,readB,numB⟩ := sound.exact _ _ atB
      obtain rfl := Reads.functionalOn laws.functional slots ra readA
      obtain rfl := Reads.functionalOn laws.functional slots rb readB
      exact Option.some.inj ((na.symm.trans numA).trans (numB.symm.trans nb))

include laws slots external h in
private theorem orderedAt_sound {a b : Ident} {va vb : Val} {x y : Nat} {strict : Bool}
    (ra : Reads Run R.bool table ρ a va) (rb : Reads Run R.bool table ρ b vb)
    (na : R.nat va = some x) (nb : R.nat vb = some y) (found : orderedAt ops table asks k a b strict = true) :
    if strict then x < y else x ≤ y := by
  simp only [orderedAt, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at found
  rcases found with ((((((⟨rfl,rfl⟩ | known) | ranges) | added) | subtracted) | offset) | ⟨rfl,zero⟩)
  · obtain rfl := Reads.functionalOn laws.functional slots ra rb
    rw [na] at nb
    cases nb
    exact Nat.le_refl _
  · obtain ⟨assignment, grounded, facts⟩ := h
    obtain ⟨_,_,⟨v,ha,xa⟩,⟨w,hb,yb⟩, le⟩ := facts.hasOrder known
    obtain rfl := Reads.functionalOn laws.functional slots ra (grounded _ _ ha)
    obtain rfl := Reads.functionalOn laws.functional slots rb (grounded _ _ hb)
    rw [na] at xa
    rw [nb] at yb
    cases xa
    cases yb
    exact le
  · apply FactCheck.rangesOrder_sound _ _ ranges
    · intro r found
      obtain ⟨_, eq, fits⟩ := rangeFor_sound laws.functional slots external h ra found
      exact Option.some.inj (eq.symm.trans na) ▸ fits
    · intro r found
      obtain ⟨_, eq, fits⟩ := rangeFor_sound laws.functional slots external h rb found
      exact Option.some.inj (eq.symm.trans nb) ▸ fits
  · exact sumOrder laws slots external h ra rb na nb added
  · exact differenceOrder laws slots external h ra rb na nb subtracted
  · obtain ⟨limit, picked⟩ := Option.isSome_iff_exists.mp offset
    obtain ⟨same, n, cap, m, num, rc, nc, lt⟩ := offsetLimit_sound laws slots h ra picked
    obtain rfl := sameNumber_sound laws slots external h rc rb nc nb same
    obtain rfl := Option.some.inj (na.symm.trans num)
    cases strict
    · exact Nat.le_of_lt lt
    · exact lt
  · exact Nat.le_of_eq (zeroAddend_sound laws slots external h rb ra nb na zero)

include laws slots external h in
private theorem ordered_sound {a b : Ident} {va vb : Val} {x y : Nat} {strict : Bool}
    (ra : Reads Run R.bool table ρ a va) (rb : Reads Run R.bool table ρ b vb)
    (na : R.nat va = some x) (nb : R.nat vb = some y) (found : ordered ops table asks k a b strict = true) :
    if strict then x < y else x ≤ y := by
  rcases Bool.or_eq_true_iff.mp found with direct | represented
  · exact orderedAt_sound laws slots external h ra rb na nb direct
  · obtain ⟨_,r₁,n₁⟩ := external.numberAt_reads laws.functional slots ra
    obtain ⟨_,r₂,n₂⟩ := external.numberAt_reads laws.functional slots rb
    exact orderedAt_sound laws slots external h r₁ r₂ (n₁.trans na) (n₂.trans nb)
      (Bool.and_eq_true_iff.mp represented).2

include laws slots external h in
private theorem matchingSums_sound {a b : Ident} {va vb : Val} {x y : Nat}
    (ra : Reads Run R.bool table ρ a va) (rb : Reads Run R.bool table ρ b vb)
    (na : R.nat va = some x) (nb : R.nat vb = some y) (found : matchingSums ops table asks k a b = true) :
    x = y := by
  unfold matchingSums at found
  split at found
  · next a1 a2 b1 b2 formA formB =>
    obtain ⟨_, readsA, _, _, _, _, rfl, n₁, n₂, resA⟩ := resultForm_reads laws slots formA ra
    obtain ⟨_, readsB, _, _, _, _, rfl, n₃, n₄, resB⟩ := resultForm_reads laws slots formB rb
    rw [na] at resA
    rw [nb] at resB
    cases readsA with | cons a₁ tail => cases tail with | cons a₂ _ =>
      cases readsB with | cons b₁ tail => cases tail with | cons b₂ _ =>
        simp only [Bool.or_eq_true, Bool.and_eq_true] at found
        rcases found with ⟨one,two⟩ | ⟨one,two⟩
        · have := sameNumber_sound laws slots external h a₁ b₁ n₁ n₃ one
          have := sameNumber_sound laws slots external h a₂ b₂ n₂ n₄ two
          simp_all
        · have := sameNumber_sound laws slots external h a₁ b₂ n₁ n₄ one
          have := sameNumber_sound laws slots external h a₂ b₁ n₂ n₃ two
          simp_all [Nat.add_comm]
  · contradiction

include laws slots external h in
private theorem compareNumbers_sound {a b : Ident} {va vb : Val} {x y : Nat} {equal result : Bool}
    (ra : Reads Run R.bool table ρ a va) (rb : Reads Run R.bool table ρ b vb)
    (na : R.nat va = some x) (nb : R.nat vb = some y)
    (found : compareNumbers ops table asks k a b equal = some result) :
    (if equal then decide (x = y) else decide (x < y)) = result := by
  have ab (s : Bool) := ordered_sound (strict := s) laws slots external h ra rb na nb
  have ba (s : Bool) := ordered_sound (strict := s) laws slots external h rb ra nb na
  unfold compareNumbers at found
  cases equal <;> simp only [Bool.false_eq_true, ↓reduceIte] at found ⊢
  · split at found
    · cases found
      exact decide_eq_true (ab true (by assumption))
    · split at found
      · cases found
        exact decide_eq_false (Nat.not_lt_of_ge (ba false (by assumption)))
      · cases found
  · split at found
    · next either =>
      cases found
      rcases Bool.or_eq_true_iff.mp either with lt | gt
      · exact decide_eq_false (Nat.ne_of_lt (ab true lt))
      · exact decide_eq_false (Nat.ne_of_gt (ba true gt))
    · split at found
      · next both =>
        cases found
        rcases Bool.or_eq_true_iff.mp both with orders | sums
        · obtain ⟨le,ge⟩ := Bool.and_eq_true_iff.mp orders
          exact decide_eq_true (Nat.le_antisymm (ab false le) (ba false ge))
        · exact decide_eq_true (matchingSums_sound laws slots external h ra rb na nb sums)
      · cases found

private theorem combineTruth_sound {x y : Bool} {a b : Option Bool} {conjunction result : Bool}
    (first : ∀ z, a = some z → x = z) (second : ∀ z, b = some z → y = z)
    (found : combineTruth conjunction a b = some result) :
    (if conjunction then x && y else x || y) = result := by
  cases conjunction <;> cases a <;> cases b <;> cases x <;> cases y <;>
    simp_all [combineTruth] <;> split at found <;> simp_all

private def RightAt (Run : Raw → List Val → List Val → Prop) (R : Reading Val) (table : Table Raw)
    (ρ : Leaves Val) (id : Ident) (answer : Option Bool) : Prop :=
  ∀ {v b}, Reads Run R.bool table ρ id v → answer = some b → R.bool v = some b

private def CacheSound (Run : Raw → List Val → List Val → Prop) (R : Reading Val) (table : Table Raw)
    (ρ : Leaves Val) (cache : TruthCache) : Prop :=
  ∀ item, item ∈ cache → RightAt Run R table ρ item.1 item.2

private theorem cacheHit {cache : TruthCache} {id : Ident} {answer : Option Bool}
    (sound : CacheSound Run R table ρ cache) (found : cache.lookup id = some answer) :
    RightAt Run R table ρ id answer := by
  obtain ⟨⟨actual, val⟩, picked, rfl⟩ := Option.map_eq_some_iff.mp found
  have eq := List.find?_some picked
  obtain rfl : actual = id := beq_iff_eq.mp eq
  intro v b read answer
  exact sound _ (BitTree.mem_of_find _ _ _ _ (List.mem_of_find?_eq_some picked)) read answer

private theorem cacheInsert {cache : TruthCache} {id : Ident} {answer : Option Bool}
    (sound : CacheSound Run R table ρ cache) (value : RightAt Run R table ρ id answer) :
    CacheSound Run R table ρ (cache.remember id answer) := by
  intro item found
  obtain earlier | rfl := BitTree.mem_insert _ _ _ _ _ found
  · exact sound item earlier
  · exact value

private abbrev QuerySound (Run : Raw → List Val → List Val → Prop) (R : Reading Val) (table : Table Raw)
    (ρ : Leaves Val) (query : Ident → TruthCache → Option Bool × TruthCache) :=
  ∀ id cache, CacheSound Run R table ρ cache →
    RightAt Run R table ρ id (query id cache).1 ∧ CacheSound Run R table ρ (query id cache).2

include laws slots external h in
private theorem evalTruth_sound {child : Ident → TruthCache → Option Bool × TruthCache}
    (sound : QuerySound Run R table ρ child) : QuerySound Run R table ρ (evalTruth ops asks table k child) := by
  intro id cache hc
  unfold evalTruth
  dsimp only
  split
  · next c ids eq =>
    refine ⟨?_,hc⟩
    intro v b read found
    cases found
    obtain ⟨_, _, meaning⟩ := resultForm_reads laws slots eq read
    exact meaning
  · next a b eq =>
    refine ⟨?_,hc⟩
    intro v z read found
    obtain ⟨_, reads, _, _, _, _, rfl, na, nb, result⟩ := resultForm_reads laws slots eq read
    cases reads with | cons first tail => cases tail with | cons second _ =>
      exact result.trans (congrArg some (compareNumbers_sound (equal := false) laws slots external h first second na nb found))
  · next a b eq =>
    refine ⟨?_,hc⟩
    intro v z read found
    obtain ⟨_, reads, _, _, _, _, rfl, na, nb, result⟩ := resultForm_reads laws slots eq read
    cases reads with | cons first tail => cases tail with | cons second _ =>
      exact result.trans (congrArg some (compareNumbers_sound (equal := true) laws slots external h first second na nb found))
  · next a eq =>
    obtain ⟨one, saved⟩ := sound a cache hc
    refine ⟨?_,saved⟩
    intro v b read found
    obtain ⟨_, reads, _, _, rfl, va, result⟩ := resultForm_reads laws slots eq read
    obtain ⟨_, answer, rfl⟩ := Option.map_eq_some_iff.mp found
    cases reads with | cons first _ =>
      exact result.trans (congrArg (fun z => some (!z)) (Option.some.inj (va.symm.trans (one first answer))))
  · next a b eq =>
    obtain ⟨one, saved⟩ := sound a cache hc
    split
    · next short =>
      refine ⟨?_,saved⟩
      intro v z read found
      cases found
      obtain ⟨_, reads, _, _, x, y, rfl, va, vb, result⟩ := resultForm_reads laws slots eq read
      cases reads with | cons first _ =>
        have hx := Option.some.inj (va.symm.trans (one first (beq_iff_eq.mp short)))
        simpa [hx] using result
    · obtain ⟨two, saved'⟩ := sound b _ saved
      refine ⟨?_,saved'⟩
      intro v z read found
      obtain ⟨_, reads, _, _, _, _, rfl, va, vb, result⟩ := resultForm_reads laws slots eq read
      cases reads with | cons first rest => cases rest with | cons second _ =>
        exact result.trans (congrArg some (combineTruth_sound
          (fun _ e => Option.some.inj (va.symm.trans (one first e)))
          (fun _ e => Option.some.inj (vb.symm.trans (two second e))) found))
  · next a b eq =>
    obtain ⟨one, saved⟩ := sound a cache hc
    split
    · next short =>
      refine ⟨?_,saved⟩
      intro v z read found
      cases found
      obtain ⟨_, reads, _, _, x, y, rfl, va, vb, result⟩ := resultForm_reads laws slots eq read
      cases reads with | cons first _ =>
        have hx := Option.some.inj (va.symm.trans (one first (beq_iff_eq.mp short)))
        simpa [hx] using result
    · obtain ⟨two, saved'⟩ := sound b _ saved
      refine ⟨?_,saved'⟩
      intro v z read found
      obtain ⟨_, reads, _, _, _, _, rfl, va, vb, result⟩ := resultForm_reads laws slots eq read
      cases reads with | cons first rest => cases rest with | cons second _ =>
        exact result.trans (congrArg some (combineTruth_sound
          (fun _ e => Option.some.inj (va.symm.trans (one first e)))
          (fun _ e => Option.some.inj (vb.symm.trans (two second e))) found))
  · split
    · next c a b shape =>
      obtain ⟨condSound, saved⟩ := sound c cache hc
      split
      · exact ⟨(fun _ wrong => nomatch wrong), saved⟩
      · next which eq =>
        obtain ⟨arm, saved'⟩ := sound (if which then a else b) _ saved
        refine ⟨?_,saved'⟩
        intro v z read found
        obtain ⟨_, w, condRead, condVal, selected⟩ := readSelection slots shape read
        obtain rfl := Option.some.inj (condVal.symm.trans (condSound condRead eq))
        exact arm selected found
    · exact ⟨(fun _ wrong => nomatch wrong), hc⟩

include laws slots external h in
private theorem cachedTruth_sound : ∀ fuel, QuerySound Run R table ρ (cachedTruth ops asks table k fuel)
  | 0 => by
    intro id cache hc
    refine ⟨?_, hc⟩
    intro v b read found
    obtain ⟨_, other, val⟩ := (external.orElse (answers_sound h)).truth _ _ found
    exact Reads.functionalOn laws.functional slots read other ▸ val
  | fuel+1 => by
    intro id cache hc
    unfold cachedTruth
    split
    · next hit at_ => exact ⟨cacheHit hc at_, hc⟩
    · split
      · next z found =>
        refine ⟨?_,hc⟩
        intro v b read same
        cases same
        obtain ⟨_, other, val⟩ := (external.orElse (answers_sound h)).truth _ _ found
        exact Reads.functionalOn laws.functional slots read other ▸ val
      · obtain ⟨answer, seen⟩ := evalTruth_sound laws slots external h (cachedTruth_sound fuel) id cache hc
        exact ⟨answer, cacheInsert seen answer⟩

include laws slots external h in
theorem decideTruth_sound {id v b} (read : Reads Run R.bool table ρ id v)
    (found : decideTruth ops asks table k id = some b) : R.bool v = some b :=
  by
    apply (cachedTruth_sound laws slots external h (depth id) id (.leaf [])
      (fun item mem => (BitTree.not_mem_empty item mem).elim)).1 read
    cases id with
    | leaf => exact found
    | val n =>
      change (match (asks.orElse (answers k)).truth (.val n) with
        | some z => (some z, _)
        | none => _).1 = some b
      cases value : (asks.orElse (answers k)).truth (.val n) <;>
        simpa [decideTruth, value] using found

end Zkc.Core.BodyAnalysis.Knowledge
