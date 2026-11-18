module

public import Zkc.Core.Facts.Knowledge.Known
public import Zkc.Core.Meaning.Requirement

@[expose] public section

namespace Zkc.Core.FactCheck

/-- A partial assignment of values to identifiers. -/
abbrev Valuation (Val : Type) : Type := Nat → Option Val

variable {Val : Type}

/-- `ρ'` keeps every value of `ρ`. -/
def Valuation.Le (ρ ρ' : Valuation Val) : Prop := ∀ i v, ρ i = some v → ρ' i = some v

/-- An identifier has a value that reads as the natural. -/
def NatAt (R : Reading Val) (ρ : Valuation Val) (id n : Nat) : Prop :=
  ∃ v, ρ id = some v ∧ R.nat v = some n

/-- An identifier has a value that reads as the truth value. -/
def BoolAt (R : Reading Val) (ρ : Valuation Val) (id : Nat) (b : Bool) : Prop :=
  ∃ v, ρ id = some v ∧ R.bool v = some b

/-- What is known holds of a valuation: the region runs, and every fact holds. -/
structure Known.Holds (R : Reading Val) (ρ : Valuation Val) (k : Known) : Prop where
  alive : k.dead = false
  ranges : ∀ id r, (id, r) ∈ k.ranges → ∃ n, NatAt R ρ id n ∧ r.Has n
  orders : ∀ o, o ∈ k.orders →
    ∃ x y, NatAt R ρ o.first x ∧ NatAt R ρ o.second y ∧ (if o.strict then x < y else x ≤ y)
  truths : ∀ id b, (id, b) ∈ k.truths → BoolAt R ρ id b

theorem NatAt.le {R : Reading Val} {ρ ρ' : Valuation Val} (h : ρ.Le ρ') {id n : Nat} :
    NatAt R ρ id n → NatAt R ρ' id n
  | ⟨v, hv, hn⟩ => ⟨v, h _ _ hv, hn⟩

theorem BoolAt.le {R : Reading Val} {ρ ρ' : Valuation Val} (h : ρ.Le ρ') {id : Nat} {b : Bool} :
    BoolAt R ρ id b → BoolAt R ρ' id b
  | ⟨v, hv, hb⟩ => ⟨v, h _ _ hv, hb⟩

theorem NatAt.unique {R : Reading Val} {ρ : Valuation Val} {id n m : Nat} :
    NatAt R ρ id n → NatAt R ρ id m → n = m
  | ⟨v, hv, hn⟩, ⟨w, hw, hm⟩ => by
      rw [hv] at hw
      cases hw
      rw [hn] at hm
      cases hm
      rfl

/-- What is known keeps holding as the valuation grows. -/
theorem Known.Holds.le {R : Reading Val} {ρ ρ' : Valuation Val} (h : ρ.Le ρ') {k : Known}
    (hk : k.Holds R ρ) : k.Holds R ρ' where
  alive := hk.alive
  ranges id r m := by
    obtain ⟨n, hn, has⟩ := hk.ranges id r m
    exact ⟨n, hn.le h, has⟩
  orders o m := by
    obtain ⟨x, y, hx, hy, ord⟩ := hk.orders o m
    exact ⟨x, y, hx.le h, hy.le h, ord⟩
  truths id b m := (hk.truths id b m).le h

variable {R : Reading Val} {ρ : Valuation Val}

theorem rangeIn_has {id n : Nat} :
    ∀ {facts : List (Nat × Range)} {r : Range}, (∀ r', (id, r') ∈ facts → r'.Has n) →
      rangeIn id facts = some r → r.Has n
  | [], _, _, h => by simp [rangeIn] at h
  | (id', r') :: rest, r, all, h => by
      simp only [rangeIn] at h
      split at h
      · next same =>
          have same : id' = id := same
          subst same
          exact Range.meet_has h (fun r e => by cases e; exact all r' List.mem_cons_self)
            (fun r e => rangeIn_has (fun r'' m => all r'' (List.mem_cons_of_mem _ m)) e)
      · exact rangeIn_has (fun r'' m => all r'' (List.mem_cons_of_mem _ m)) h

theorem rangeIn_mem {id : Nat} :
    ∀ {facts : List (Nat × Range)} {r : Range}, rangeIn id facts = some r →
      ∃ r', (id, r') ∈ facts
  | [], _, h => by simp [rangeIn] at h
  | (id', r') :: rest, r, h => by
      simp only [rangeIn] at h
      split at h
      · next same =>
          have same : id' = id := same
          subst same
          exact ⟨r', List.mem_cons_self⟩
      · obtain ⟨r'', m⟩ := rangeIn_mem h
        exact ⟨r'', List.mem_cons_of_mem _ m⟩

/-- A range that is known of an identifier holds of its value. -/
theorem Known.Holds.rangeOf {k : Known} (hk : k.Holds R ρ) {id : Nat} {r : Range}
    (h : k.rangeOf id = some r) : ∃ n, NatAt R ρ id n ∧ r.Has n := by
  obtain ⟨r', m⟩ := rangeIn_mem h
  obtain ⟨n, hn, _⟩ := hk.ranges id r' (FactBuckets.mem_of_find _ _ _ m)
  refine ⟨n, hn, rangeIn_has (fun r'' m'' => ?_) h⟩
  obtain ⟨n', hn', has⟩ := hk.ranges id r'' (FactBuckets.mem_of_find _ _ _ m'')
  rw [hn.unique hn']
  exact has

theorem Known.Holds.rangeOf_at {k : Known} (hk : k.Holds R ρ) {id n : Nat} (hn : NatAt R ρ id n)
    {r : Range} (h : k.rangeOf id = some r) : r.Has n := by
  obtain ⟨n', hn', has⟩ := hk.rangeOf h
  rw [hn.unique hn']
  exact has

/-! ## Learning -/

theorem Known.Holds.addRange {k : Known} (hk : k.Holds R ρ) {id n : Nat} (hn : NatAt R ρ id n)
    {r : Range} (has : r.Has n) : (k.addRange id r).Holds R ρ := by
  refine ⟨hk.alive, ?_, hk.orders, hk.truths⟩
  · intro id' r' m
    rcases FactBuckets.mem_insert _ _ _ _ m with m | e
    · exact hk.ranges id' r' m
    · cases e; exact ⟨n, hn, has⟩

theorem Known.Holds.addRange? {k : Known} (hk : k.Holds R ρ) {id : Nat} {o : Option Range}
    (h : ∀ r : Range, o = some r → ∃ n, NatAt R ρ id n ∧ r.Has n) :
    (k.addRange? id o).Holds R ρ := by
  cases o with
  | none => exact hk
  | some r =>
      obtain ⟨n, hn, has⟩ := h r rfl
      exact hk.addRange hn has

theorem Known.Holds.addOrder {k : Known} (hk : k.Holds R ρ) {a b x y : Nat} {strict : Bool}
    {byLoop : Bool} (ha : NatAt R ρ a x) (hb : NatAt R ρ b y)
    (o : if strict then x < y else x ≤ y) : (k.addOrder a b strict byLoop).Holds R ρ := by
  refine ⟨hk.alive, hk.ranges, ?_, hk.truths⟩
  intro fact m
  rcases FactBuckets.mem_insert _ _ _ _ m with m | e
  · exact hk.orders fact m
  · subst e; exact ⟨x, y, ha, hb, o⟩

theorem Known.Holds.addTruth {k : Known} (hk : k.Holds R ρ) {id : Nat} {b : Bool}
    (h : BoolAt R ρ id b) : (k.addTruth id b).Holds R ρ := by
  refine ⟨hk.alive, hk.ranges, hk.orders, ?_⟩
  intro id' b' m
  rcases FactBuckets.mem_insert _ _ _ _ m with m | e
  · exact hk.truths id' b' m
  · cases e; exact h

theorem Known.Holds.hasTruth {k : Known} (hk : k.Holds R ρ) {id : Nat} {b : Bool}
    (h : k.hasTruth id b = true) : BoolAt R ρ id b := by
  simp only [Known.hasTruth, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨id', b'⟩, m, e1, e2⟩ := h
  simp only at e1 e2
  subst e1; subst e2
  exact hk.truths _ _ (FactBuckets.mem_of_find _ _ _ m)

theorem Known.Holds.hasOrder {k : Known} (hk : k.Holds R ρ) {a b : Nat} {strict : Bool}
    (h : k.hasOrder a b strict = true) :
    ∃ x y, NatAt R ρ a x ∧ NatAt R ρ b y ∧ (if strict then x < y else x ≤ y) := by
  simp only [Known.hasOrder, List.any_eq_true] at h
  obtain ⟨⟨a', b', s, l⟩, m, e⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at e
  obtain ⟨⟨rfl, rfl⟩, e3⟩ := e
  obtain ⟨x, y, hx, hy, o⟩ := hk.orders _ (FactBuckets.mem_of_find _ _ _ m)
  refine ⟨x, y, hx, hy, ?_⟩
  cases strict <;> cases s
  · exact o
  · simp only [Bool.false_eq_true, ↓reduceIte] at o ⊢
    omega
  · simp at e3
  · exact o

/-- The one number of an identifier, when its range is one number, is its value. -/
theorem Known.Holds.pointOf_at {k : Known} (hk : k.Holds R ρ) {id n p : Nat}
    (hn : NatAt R ρ id n) (h : k.pointOf id = some p) : n = p := by
  simp only [Known.pointOf] at h
  cases hr : k.rangeOf id with
  | none => rw [hr] at h; cases h
  | some r =>
      rw [hr] at h
      obtain ⟨lo, hi⟩ := r
      cases hi with
      | none => cases h
      | some hi =>
          simp only at h
          split at h
          · next same =>
              have hp : lo = p := Option.some.inj h
              have has := hk.rangeOf_at hn hr
              have h1 : lo ≤ n := has.1
              have h2 : n ≤ hi := has.2 hi rfl
              omega
          · cases h

theorem Known.Holds.pushLess {k : Known} (hk : k.Holds R ρ) {a b x y : Nat}
    (ha : NatAt R ρ a x) (hb : NatAt R ρ b y) (lt : x < y) : (k.pushLess a b).Holds R ρ := by
  simp only [Known.pushLess]
  have h1 := hk.addOrder (strict := true) (byLoop := false) ha hb (by simpa using lt)
  refine (h1.addRange? fun r e => ?_).addRange? fun r e => ?_
  · cases hs : k.pointOf b with
    | none => rw [hs] at e; cases e
    | some p =>
        rw [hs] at e
        cases e
        rw [← hk.pointOf_at hb hs]
        exact ⟨x, ha, (Range.has_point.mpr rfl : (Range.point y).Has y).below lt⟩
  · cases hf : k.pointOf a with
    | none => rw [hf] at e; cases e
    | some p =>
        rw [hf] at e
        cases e
        rw [← hk.pointOf_at ha hf]
        exact ⟨y, hb, ⟨by show x + 1 ≤ y; omega, fun _ e => nomatch e⟩⟩

theorem Known.Holds.pushLe {k : Known} (hk : k.Holds R ρ) {a b x y : Nat}
    (ha : NatAt R ρ a x) (hb : NatAt R ρ b y) (le : x ≤ y) : (k.pushLe a b).Holds R ρ := by
  simp only [Known.pushLe]
  have h1 := hk.addOrder (strict := false) (byLoop := false) ha hb (by simpa using le)
  refine (h1.addRange? fun r e => ?_).addRange? fun r e => ?_
  · cases hs : k.pointOf b with
    | none => rw [hs] at e; cases e
    | some p =>
        rw [hs] at e
        cases e
        rw [← hk.pointOf_at hb hs]
        exact ⟨x, ha, Nat.zero_le _, fun h e => by cases e; exact le⟩
  · cases hf : k.pointOf a with
    | none => rw [hf] at e; cases e
    | some p =>
        rw [hf] at e
        cases e
        rw [← hk.pointOf_at ha hf]
        exact ⟨y, hb, le, fun _ e => nomatch e⟩

theorem Known.Holds.pushEqual {k : Known} (hk : k.Holds R ρ) {a b x : Nat}
    (ha : NatAt R ρ a x) (hb : NatAt R ρ b x) : (k.pushEqual a b).Holds R ρ := by
  simp only [Known.pushEqual]
  have h1 := (hk.addOrder (strict := false) (byLoop := false) ha hb (by simp)).addOrder
    (strict := false) (byLoop := false) hb ha (by simp)
  refine (h1.addRange? fun r e => ?_).addRange? fun r e => ?_
  · cases hs : k.pointOf b with
    | none => rw [hs] at e; cases e
    | some p =>
        rw [hs] at e
        cases e
        exact ⟨x, ha, Range.has_point.mpr (hk.pointOf_at hb hs)⟩
  · cases hf : k.pointOf a with
    | none => rw [hf] at e; cases e
    | some p =>
        rw [hf] at e
        cases e
        exact ⟨x, hb, Range.has_point.mpr (hk.pointOf_at ha hf)⟩

theorem Known.Holds.oneDifferent {k : Known} (hk : k.Holds R ρ) {a b x y : Nat}
    (ha : NatAt R ρ a x) (hb : NatAt R ρ b y) (ne : x ≠ y) :
    (if k.rangeOf b = some (Range.point 0) then k.addRange a ⟨1, none⟩ else k).Holds R ρ := by
  split
  · next e =>
      have := Range.has_point.mp (hk.rangeOf_at hb e)
      exact hk.addRange ha ⟨by show 1 ≤ x; omega, fun _ e => nomatch e⟩
  · exact hk

theorem Known.Holds.pushDifferent {k : Known} (hk : k.Holds R ρ) {a b x y : Nat}
    (ha : NatAt R ρ a x) (hb : NatAt R ρ b y) (ne : x ≠ y) :
    (k.pushDifferent a b).Holds R ρ := by
  simp only [Known.pushDifferent]
  have learned := hk.oneDifferent ha hb ne
  by_cases zero : k.rangeOf a = some (Range.point 0)
  · rw [ite_eq_left zero]
    have := Range.has_point.mp (hk.rangeOf_at ha zero)
    exact learned.addRange hb ⟨by show 1 ≤ y; omega, fun _ e => nomatch e⟩
  · rw [ite_eq_right zero]
    exact learned


theorem rangesOrder_sound {rf rs : Option Range} {strict : Bool} {x y : Nat}
    (hrf : ∀ r, rf = some r → r.Has x) (hrs : ∀ r, rs = some r → r.Has y)
    (h : rangesOrder rf rs strict = true) : if strict then x < y else x ≤ y := by
  simp only [rangesOrder] at h
  split at h
  · next a b =>
      have ha := hrf a rfl
      have hb := (hrs b rfl).1
      split at h
      · next hi e =>
          have := ha.2 hi e
          cases strict
          · simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h ⊢
            omega
          · simp only [↓reduceIte, decide_eq_true_eq] at h ⊢
            omega
      · cases h
  · cases h

end Zkc.Core.FactCheck
