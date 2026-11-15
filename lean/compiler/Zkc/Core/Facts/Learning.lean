module

public import Zkc.Core.Facts.Valuation

@[expose] public section

/-!
The rules of what is known are true: what is learned of a valuation where what was known holds
holds too, and a requirement that the rules decide holds of the values it names.

Over any values, any reading of them and any relation of operations whose `OpFacts` are lawful.
-/

namespace Zkc.Core

/-! ## Ranges -/

namespace Range

theorem Has.inter {a b : Range} {n : Nat} (ha : a.Has n) (hb : b.Has n) : (a.inter b).Has n := by
  obtain ⟨la, ua⟩ := ha
  obtain ⟨lb, ub⟩ := hb
  refine ⟨Nat.max_le.mpr ⟨la, lb⟩, fun h e => ?_⟩
  rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
    simp only [Range.inter, Option.some.injEq, reduceCtorEq] at e
  · subst e; exact ub _ rfl
  · subst e; exact ua _ rfl
  · subst e; exact Nat.le_min.mpr ⟨ua _ rfl, ub _ rfl⟩

theorem Has.hull_left {a b : Range} {n : Nat} (ha : a.Has n) : (a.hull b).Has n := by
  obtain ⟨la, ua⟩ := ha
  refine ⟨Nat.le_trans (Nat.min_le_left _ _) la, fun h e => ?_⟩
  rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
    simp only [Range.hull, Option.some.injEq, reduceCtorEq] at e
  subst e
  exact Nat.le_trans (ua _ rfl) (Nat.le_max_left _ _)

theorem Has.hull_right {a b : Range} {n : Nat} (hb : b.Has n) : (a.hull b).Has n := by
  obtain ⟨lb, ub⟩ := hb
  refine ⟨Nat.le_trans (Nat.min_le_right _ _) lb, fun h e => ?_⟩
  rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
    simp only [Range.hull, Option.some.injEq, reduceCtorEq] at e
  subst e
  exact Nat.le_trans (ub _ rfl) (Nat.le_max_right _ _)

theorem Has.not_empty {r : Range} {n : Nat} (h : r.Has n) : r.isEmpty = false := by
  rcases r with ⟨lo, _ | hi⟩ <;> simp_all [Range.isEmpty, Range.Has] <;> omega

theorem has_point {n m : Nat} : (Range.point n).Has m ↔ m = n :=
  ⟨fun ⟨l, u⟩ => Nat.le_antisymm (u n rfl) l,
    fun e => by subst e; exact ⟨Nat.le_refl _, fun h e => by cases e; exact Nat.le_refl _⟩⟩

theorem not_has_nothing {n : Nat} : ¬ Range.nothing.Has n := fun ⟨h1, h2⟩ => by
  have := h2 0 rfl
  simp only [Range.nothing] at h1
  omega

/-- Below a natural in the range, a natural is in the range below it. -/
theorem Has.below {r : Range} {c i : Nat} (h : r.Has c) (lt : i < c) : r.below.Has i := by
  rcases r with ⟨lo, _ | _ | hi⟩
  · exact ⟨Nat.zero_le _, fun _ e => nomatch e⟩
  · have := h.2 0 rfl
    exfalso
    omega
  · have := h.2 (hi + 1) rfl
    exact ⟨Nat.zero_le _, fun h' e => by cases e; omega⟩

end Range

theorem Range.meet_has {a b : Option Range} {r : Range} {n : Nat} (h : Range.meet a b = some r)
    (ha : ∀ r, a = some r → r.Has n) (hb : ∀ r, b = some r → r.Has n) : r.Has n := by
  cases a with
  | none =>
      simp only [Range.meet] at h
      exact hb r h
  | some a =>
      cases b with
      | none =>
          simp only [Range.meet, Option.some.injEq] at h
          subst h
          exact ha a rfl
      | some b =>
          simp only [Range.meet, Option.some.injEq] at h
          subst h
          exact (ha a rfl).inter (hb b rfl)

namespace FactCheck

section
variable {Val Raw : Type} {R : Reading Val} {ρ : Valuation Val}

/-! ## Ranges of identifiers -/

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
  obtain ⟨n, hn, _⟩ := hk.ranges id r' m
  refine ⟨n, hn, rangeIn_has (fun r'' m'' => ?_) h⟩
  obtain ⟨n', hn', has⟩ := hk.ranges id r'' m''
  rw [hn.unique hn']
  exact has

theorem Known.Holds.rangeOf_at {k : Known} (hk : k.Holds R ρ) {id n : Nat} (hn : NatAt R ρ id n)
    {r : Range} (h : k.rangeOf id = some r) : r.Has n := by
  obtain ⟨n', hn', has⟩ := hk.rangeOf h
  rw [hn.unique hn']
  exact has

/-- The lower end of what is known of an identifier is at most its value. -/
theorem Known.Holds.low {k : Known} (hk : k.Holds R ρ) {id n : Nat} (hn : NatAt R ρ id n) :
    k.low id ≤ n := by
  simp only [Known.low]
  cases h : k.rangeOf id with
  | none => simp
  | some r => simpa using (hk.rangeOf_at hn h).1

theorem Known.Holds.low_valued {k : Known} (hk : k.Holds R ρ) {id : Nat} (h : 1 ≤ k.low id) :
    ∃ n, NatAt R ρ id n ∧ 1 ≤ n := by
  simp only [Known.low] at h
  cases e : k.rangeOf id with
  | none => rw [e] at h; simp at h
  | some r =>
      rw [e] at h
      obtain ⟨n, hn, has⟩ := hk.rangeOf e
      exact ⟨n, hn, by simp at h; exact Nat.le_trans h has.1⟩

/-! ## Learning -/

theorem Known.Holds.addRange {k : Known} (hk : k.Holds R ρ) {id n : Nat} (hn : NatAt R ρ id n)
    {r : Range} (has : r.Has n) : (k.addRange id r).Holds R ρ := by
  have all : ∀ r', (id, r') ∈ (id, r) :: k.ranges → r'.Has n := by
    intro r' m
    rcases List.mem_cons.mp m with e | m
    · cases e; exact has
    · obtain ⟨n', hn', has'⟩ := hk.ranges id r' m
      rw [hn.unique hn']
      exact has'
  refine ⟨?_, ?_, hk.orders, hk.truths, hk.choices⟩
  · simp only [Known.addRange, hk.alive, Bool.false_or]
    split
    · next found e => exact (rangeIn_has all e).not_empty
    · rfl
  · intro id' r' m
    rcases List.mem_cons.mp m with e | m
    · cases e; exact ⟨n, hn, has⟩
    · exact hk.ranges id' r' m

theorem Known.Holds.addRange? {k : Known} (hk : k.Holds R ρ) {id : Nat} {o : Option Range}
    (h : ∀ r : Range, o = some r → ∃ n, NatAt R ρ id n ∧ r.Has n) :
    (k.addRange? id o).Holds R ρ := by
  cases o with
  | none => exact hk
  | some r =>
      obtain ⟨n, hn, has⟩ := h r rfl
      exact hk.addRange hn has

theorem Known.Holds.addRanges :
    ∀ {k : Known} {ids : List Nat} {rs : List (Option Range)}, k.Holds R ρ →
      (∀ (j id : Nat) (r : Range), ids[j]? = some id → rs[j]? = some (some r) →
        ∃ n, NatAt R ρ id n ∧ r.Has n) →
      (k.addRanges ids rs).Holds R ρ
  | k, [], _, hk, _ => by cases ‹List (Option Range)› <;> exact hk
  | k, _ :: _, [], hk, _ => hk
  | k, id :: ids, r :: rs, hk, h => by
      simp only [Known.addRanges]
      refine Known.Holds.addRanges (hk.addRange? fun r' e => h 0 id r' rfl (by simp [e])) ?_
      intro j id' r' e1 e2
      exact h (j + 1) id' r' (by simpa using e1) (by simpa using e2)

theorem Known.Holds.addOrder {k : Known} (hk : k.Holds R ρ) {a b x y : Nat} {strict : Bool}
    (ha : NatAt R ρ a x) (hb : NatAt R ρ b y) (o : if strict then x < y else x ≤ y) :
    (k.addOrder a b strict).Holds R ρ := by
  refine ⟨hk.alive, hk.ranges, ?_, hk.truths, hk.choices⟩
  intro a' b' s m
  rcases List.mem_cons.mp m with e | m
  · cases e; exact ⟨x, y, ha, hb, o⟩
  · exact hk.orders a' b' s m

theorem Known.Holds.addTruth {k : Known} (hk : k.Holds R ρ) {id : Nat} {b : Bool}
    (h : BoolAt R ρ id b) : (k.addTruth id b).Holds R ρ := by
  refine ⟨hk.alive, hk.ranges, hk.orders, ?_, hk.choices⟩
  intro id' b' m
  rcases List.mem_cons.mp m with e | m
  · cases e; exact h
  · exact hk.truths id' b' m

theorem Known.Holds.addChoice {k : Known} (hk : k.Holds R ρ) {c : ChoiceFact}
    (h : ρ c.result ≠ none ∧ ∀ b, BoolAt R ρ c.result b →
      b = c.conjunction → BoolAt R ρ c.condition b ∧ BoolAt R ρ c.other b) :
    (k.addChoice c).Holds R ρ := by
  refine ⟨hk.alive, hk.ranges, hk.orders, hk.truths, ?_⟩
  intro c' m
  rcases List.mem_cons.mp m with e | m
  · cases e; exact h
  · exact hk.choices c' m

theorem Known.Holds.not_kill {k : Known} : ¬ k.kill.Holds R ρ := fun h => by
  have := h.alive
  simp [Known.kill] at this

theorem Known.Holds.hasTruth {k : Known} (hk : k.Holds R ρ) {id : Nat} {b : Bool}
    (h : k.hasTruth id b = true) : BoolAt R ρ id b := by
  simp only [Known.hasTruth, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨id', b'⟩, m, e1, e2⟩ := h
  simp only at e1 e2
  subst e1; subst e2
  exact hk.truths _ _ m

theorem Known.Holds.hasOrder {k : Known} (hk : k.Holds R ρ) {a b : Nat} {strict : Bool}
    (h : k.hasOrder a b strict = true) :
    ∃ x y, NatAt R ρ a x ∧ NatAt R ρ b y ∧ (if strict then x < y else x ≤ y) := by
  simp only [Known.hasOrder, List.any_eq_true] at h
  obtain ⟨⟨a', b', s⟩, m, e⟩ := h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at e
  obtain ⟨⟨rfl, rfl⟩, e3⟩ := e
  obtain ⟨x, y, hx, hy, o⟩ := hk.orders a' b' s m
  refine ⟨x, y, hx, hy, ?_⟩
  cases strict <;> cases s
  · exact o
  · simp only [Bool.false_eq_true, ↓reduceIte] at o ⊢
    omega
  · simp at e3
  · exact o

theorem Known.Holds.pushLess {k : Known} (hk : k.Holds R ρ) {a b x y : Nat}
    (ha : NatAt R ρ a x) (hb : NatAt R ρ b y) (lt : x < y) : (k.pushLess a b).Holds R ρ := by
  simp only [Known.pushLess]
  have h1 := hk.addOrder (strict := true) ha hb (by simpa using lt)
  refine (h1.addRange? fun r e => ?_).addRange? fun r e => ?_
  · cases hs : k.rangeOf b with
    | none => rw [hs] at e; cases e
    | some rb =>
        rw [hs] at e
        cases e
        exact ⟨x, ha, (hk.rangeOf_at hb hs).below lt⟩
  · cases hf : k.rangeOf a with
    | none => rw [hf] at e; cases e
    | some ra =>
        rw [hf] at e
        cases e
        have := (hk.rangeOf_at ha hf).1
        exact ⟨y, hb, by simp only [Range.Has]; exact ⟨by omega, fun _ e => nomatch e⟩⟩

theorem Known.Holds.pushLe {k : Known} (hk : k.Holds R ρ) {a b x y : Nat}
    (ha : NatAt R ρ a x) (hb : NatAt R ρ b y) (le : x ≤ y) : (k.pushLe a b).Holds R ρ := by
  simp only [Known.pushLe]
  have h1 := hk.addOrder (strict := false) ha hb (by simpa using le)
  refine (h1.addRange? fun r e => ?_).addRange? fun r e => ?_
  · cases hs : k.rangeOf b with
    | none => rw [hs] at e; cases e
    | some rb =>
        rw [hs] at e
        cases e
        have := (hk.rangeOf_at hb hs).2
        exact ⟨x, ha, ⟨Nat.zero_le _, fun h e => by have := this h e; omega⟩⟩
  · cases hf : k.rangeOf a with
    | none => rw [hf] at e; cases e
    | some ra =>
        rw [hf] at e
        cases e
        have := (hk.rangeOf_at ha hf).1
        exact ⟨y, hb, ⟨by simp only; omega, fun _ e => nomatch e⟩⟩

theorem Known.Holds.pushEqual {k : Known} (hk : k.Holds R ρ) {a b x : Nat}
    (ha : NatAt R ρ a x) (hb : NatAt R ρ b x) : (k.pushEqual a b).Holds R ρ := by
  simp only [Known.pushEqual]
  have h1 := (hk.addOrder (strict := false) ha hb (by simp)).addOrder (strict := false) hb ha
    (by simp)
  refine (h1.addRange? fun r e => ?_).addRange? fun r e => ?_
  · exact ⟨x, ha, hk.rangeOf_at hb e⟩
  · exact ⟨x, hb, hk.rangeOf_at ha e⟩

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
  exact (hk.oneDifferent ha hb ne).oneDifferent hb ha (Ne.symm ne)

/-! ## Assuming a truth value -/

variable {Run : Raw → List Val → List Val → Prop} {ops : OpFacts Raw}

/-- The values of the operands of the entry of an identifier that has a value, and how the value
reads by the entry's form. -/
theorem formOf_values (lawful : OpFacts.Lawful ops R Run) {tbl : Table Raw}
    (hc : Consistent Run ρ tbl) (hcl : Closed ρ tbl) {id : Nat} {f : ResultForm}
    {args : List Nat} (h : tbl.formOf ops id = some (f, args)) {v : Val} (hv : ρ id = some v) :
    ∃ vs, lookupAll ρ args = some vs ∧ FormHolds R f vs v := by
  obtain ⟨e, m, lo, pos, form, eargs⟩ := Table.formOf_spec h
  subst eargs
  have valued : ρ (e.lo + 0) ≠ none := by rw [Nat.add_zero, lo, hv]; simp
  obtain ⟨vs, hvs⟩ := lookupAll_of_mem (hcl e m 0 pos valued)
  obtain ⟨rs, run, at0⟩ := hc e m vs hvs 0 pos v (by rw [Nat.add_zero, lo, hv])
  obtain ⟨r, head, holds⟩ := lawful.form _ _ _ _ form run
  have : r = v := by
    rw [List.head?_eq_getElem?] at head
    rw [head] at at0
    cases at0
    rfl
  subst this
  exact ⟨vs, hvs, holds⟩

theorem lookupAll_pair {a b : Nat} {vs : List Val} (h : lookupAll ρ [a, b] = some vs) :
    ∃ va vb, vs = [va, vb] ∧ ρ a = some va ∧ ρ b = some vb := by
  have hl := lookupAll_length h
  match vs, hl with
  | [va, vb], _ =>
      exact ⟨va, vb, rfl, by simpa using lookupAll_get h 0 (by simp),
        by simpa using lookupAll_get h 1 (by simp)⟩

theorem lookupAll_single {a : Nat} {vs : List Val} (h : lookupAll ρ [a] = some vs) :
    ∃ va, vs = [va] ∧ ρ a = some va := by
  have hl := lookupAll_length h
  match vs, hl with
  | [va], _ => exact ⟨va, rfl, by simpa using lookupAll_get h 0 (by simp)⟩

theorem foldl_invariant {α β : Type} {P : β → Prop} (f : β → α → β) :
    ∀ (xs : List α) (b : β), P b → (∀ b x, x ∈ xs → P b → P (f b x)) → P (xs.foldl f b)
  | [], _, hb, _ => hb
  | x :: xs, b, hb, step =>
      foldl_invariant f xs (f b x) (step b x List.mem_cons_self hb)
        (fun b' x' m h => step b' x' (List.mem_cons_of_mem _ m) h)

/-- Assuming the truth value that an identifier has: what is learned holds. -/
theorem assume_holds (lawful : OpFacts.Lawful ops R Run) {tbl : Table Raw}
    (hc : Consistent Run ρ tbl) (hcl : Closed ρ tbl) :
    ∀ (fuel : Nat) {k : Known} {id : Nat} {value : Bool}, k.Holds R ρ → BoolAt R ρ id value →
      (assume ops tbl fuel k id value).Holds R ρ
  | 0, k, id, value, hk, hb => by
      simp only [assume]
      exact hk.addTruth hb
  | fuel + 1, k, id, value, hk, hb => by
      simp only [assume, hk.alive, Bool.false_eq_true, ↓reduceIte]
      split
      · exact hk
      split
      · next opposite =>
          have := (hk.hasTruth opposite).unique hb
          cases value <;> simp at this
      have k₁ := hk.addTruth hb
      have hb0 := hb
      obtain ⟨v, hv, hbool⟩ := hb0
      apply foldl_invariant
      · split
        · next first second e =>
            obtain ⟨vs, hvs, a, b, x, y, eq, hx, hy, hr⟩ := formOf_values lawful hc hcl e hv
            obtain ⟨va, vb, rfl, ha, hb'⟩ := lookupAll_pair hvs
            cases eq
            rw [hbool] at hr
            cases value
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact k₁.pushLe ⟨_, hb', hy⟩ ⟨_, ha, hx⟩ (by simp at hr; omega)
            · simp only [↓reduceIte]
              exact k₁.pushLess ⟨_, ha, hx⟩ ⟨_, hb', hy⟩ (by simpa using hr.symm)
        · next first second e =>
            obtain ⟨vs, hvs, a, b, x, y, eq, hx, hy, hr⟩ := formOf_values lawful hc hcl e hv
            obtain ⟨va, vb, rfl, ha, hb'⟩ := lookupAll_pair hvs
            cases eq
            rw [hbool] at hr
            cases value
            · simp only [Bool.false_eq_true, ↓reduceIte]
              exact k₁.pushDifferent ⟨_, ha, hx⟩ ⟨_, hb', hy⟩ (by simpa using hr.symm)
            · simp only [↓reduceIte]
              have : x = y := by simpa using hr.symm
              subst this
              exact k₁.pushEqual ⟨_, ha, hx⟩ ⟨_, hb', hy⟩
        · next operand e =>
            obtain ⟨vs, hvs, a, x, eq, hx, hr⟩ := formOf_values lawful hc hcl e hv
            obtain ⟨va, rfl, ha⟩ := lookupAll_single hvs
            cases eq
            rw [hbool] at hr
            have : x = !value := by cases x <;> cases value <;> simp_all
            subst this
            exact assume_holds lawful hc hcl fuel k₁ ⟨_, ha, hx⟩
        · next first second e =>
            obtain ⟨vs, hvs, a, b, x, y, eq, hx, hy, hr⟩ := formOf_values lawful hc hcl e hv
            obtain ⟨va, vb, rfl, ha, hb'⟩ := lookupAll_pair hvs
            cases eq
            rw [hbool] at hr
            cases value
            · simpa using k₁
            · simp only [↓reduceIte]
              have both : x = true ∧ y = true := by
                cases x <;> cases y <;> simp_all
              obtain ⟨rfl, rfl⟩ := both
              exact assume_holds lawful hc hcl fuel
                (assume_holds lawful hc hcl fuel k₁ ⟨_, ha, hx⟩) ⟨_, hb', hy⟩
        · next first second e =>
            obtain ⟨vs, hvs, a, b, x, y, eq, hx, hy, hr⟩ := formOf_values lawful hc hcl e hv
            obtain ⟨va, vb, rfl, ha, hb'⟩ := lookupAll_pair hvs
            cases eq
            rw [hbool] at hr
            cases value
            · simp only [Bool.false_eq_true, ↓reduceIte]
              have both : x = false ∧ y = false := by
                cases x <;> cases y <;> simp_all
              obtain ⟨rfl, rfl⟩ := both
              exact assume_holds lawful hc hcl fuel
                (assume_holds lawful hc hcl fuel k₁ ⟨_, ha, hx⟩) ⟨_, hb', hy⟩
            · simpa using k₁
        · next written rest e =>
            obtain ⟨vs, hvs, hr⟩ := formOf_values lawful hc hcl e hv
            simp only [FormHolds] at hr
            rw [hbool] at hr
            cases hr
            simpa using k₁
        · exact k₁
      · intro known c m hknown
        split
        · next same =>
            obtain ⟨rfl, rfl⟩ := same
            obtain ⟨_, imp⟩ := hk.choices c m
            obtain ⟨hcond, hother⟩ := imp _ hb rfl
            exact assume_holds lawful hc hcl fuel (assume_holds lawful hc hcl fuel hknown hcond)
              hother
        · exact hknown

/-! ## Deciding a requirement -/

section
variable {tbl : Table Raw} {k : Known}

theorem sumAbove_sound (lawful : OpFacts.Lawful ops R Run) (hc : Consistent Run ρ tbl)
    (hcl : Closed ρ tbl) (hk : k.Holds R ρ) {first second : Nat} {strict : Bool} {vf vs : Val}
    (hf : ρ first = some vf) (hs : ρ second = some vs)
    (h : sumAbove ops tbl k first second strict = true) :
    ∀ x y, R.nat vf = some x → R.nat vs = some y → if strict then x < y else x ≤ y := by
  intro x y hx hy
  simp only [sumAbove] at h
  split at h
  · next a b e =>
      obtain ⟨vals, hvals, va, vb, x', y', eq, hx', hy', hsum⟩ := formOf_values lawful hc hcl e hs
      obtain ⟨wa, wb, rfl, ha, hb⟩ := lookupAll_pair hvals
      cases eq
      rw [hy] at hsum
      cases hsum
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
        decide_eq_true_eq] at h
      rcases h with ⟨rfl, hs'⟩ | ⟨rfl, hs'⟩
      · rw [hf] at ha
        cases ha
        rw [hx] at hx'
        cases hx'
        cases strict
        · simp
        · simp only [↓reduceIte]
          have := hk.low ⟨_, hb, hy'⟩
          simp at hs'
          omega
      · rw [hf] at hb
        cases hb
        rw [hx] at hy'
        cases hy'
        cases strict
        · simp
        · simp only [↓reduceIte]
          have := hk.low ⟨_, ha, hx'⟩
          simp at hs'
          omega
  · cases h

theorem differenceBelow_sound (lawful : OpFacts.Lawful ops R Run) (hc : Consistent Run ρ tbl)
    (hcl : Closed ρ tbl) (hk : k.Holds R ρ) {first second : Nat} {strict : Bool} {vf vs : Val}
    (hf : ρ first = some vf) (hs : ρ second = some vs)
    (h : differenceBelow ops tbl k first second strict = true) :
    ∀ x y, R.nat vf = some x → R.nat vs = some y → if strict then x < y else x ≤ y := by
  intro x y hx hy
  simp only [differenceBelow] at h
  split at h
  · next a u e =>
      obtain ⟨vals, hvals, va, vu, x', y', eq, hx', hy', le, hdiff⟩ :=
        formOf_values lawful hc hcl e hf
      obtain ⟨wa, wu, rfl, ha, hu⟩ := lookupAll_pair hvals
      cases eq
      rw [hx] at hdiff
      cases hdiff
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at h
      obtain ⟨rfl, hs'⟩ := h
      rw [hs] at ha
      cases ha
      rw [hy] at hx'
      cases hx'
      cases strict
      · simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      · simp only [↓reduceIte]
        have := hk.low ⟨_, hu, hy'⟩
        simp at hs'
        omega
  · cases h

theorem offsetBelow_sound (lawful : OpFacts.Lawful ops R Run) (hc : Consistent Run ρ tbl)
    (hcl : Closed ρ tbl) (hk : k.Holds R ρ) {first second : Nat} {vf vs : Val}
    (hf : ρ first = some vf) (hs : ρ second = some vs)
    (h : offsetBelow ops tbl k first second = true) :
    ∀ x y, R.nat vf = some x → R.nat vs = some y → x < y := by
  intro x y hx hy
  simp only [offsetBelow] at h
  split at h
  · next a t e =>
      obtain ⟨vals, hvals, va, vt, a0, t0, eq, ha0, ht0, hsum⟩ := formOf_values lawful hc hcl e hf
      obtain ⟨wa, wt, rfl, ha, ht⟩ := lookupAll_pair hvals
      cases eq
      rw [hx] at hsum
      cases hsum
      simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨t', d, s⟩, m, ⟨rfl, hstrict⟩, hd⟩ := h
      simp only at hstrict
      subst hstrict
      obtain ⟨t1, d0, ht1, hd0, lt⟩ := hk.orders _ _ _ m
      simp only [↓reduceIte] at lt
      have := ht1.unique ⟨_, ht, ht0⟩
      subst this
      split at hd
      · next r x' e' =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hd
          obtain ⟨rfl, rfl⟩ := hd
          obtain ⟨vd, hvd, hdn⟩ := hd0
          obtain ⟨vals', hvals', vr, vx, r0, a1, eq', hr0, ha1, le, hdiff⟩ :=
            formOf_values lawful hc hcl e' hvd
          obtain ⟨wr, wx, rfl, hr, hx'⟩ := lookupAll_pair hvals'
          cases eq'
          rw [hs] at hr
          cases hr
          rw [hy] at hr0
          cases hr0
          rw [ha] at hx'
          cases hx'
          rw [ha0] at ha1
          cases ha1
          rw [hdn] at hdiff
          cases hdiff
          omega
      · cases hd
  · cases h

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

/-- The ranges given for the operands of a requirement hold of the values of the operands. -/
def RangesHold (R : Reading Val) (rf : Option Range) (v : Val) : Prop :=
  ∀ r, rf = some r → ∃ x, R.nat v = some x ∧ r.Has x

theorem RangesHold.has {rf : Option Range} {v : Val} {x : Nat} (h : RangesHold R rf v)
    (hx : R.nat v = some x) : ∀ r, rf = some r → r.Has x := fun r e => by
  obtain ⟨x', hx', has⟩ := h r e
  rw [hx] at hx'
  cases hx'
  exact has

theorem knownLe_sound (lawful : OpFacts.Lawful ops R Run) (hc : Consistent Run ρ tbl)
    (hcl : Closed ρ tbl) (hk : k.Holds R ρ) {first second : Nat} {vf vs : Val}
    {rf rs : Option Range} (hf : ρ first = some vf) (hs : ρ second = some vs)
    (hrf : RangesHold R rf vf) (hrs : RangesHold R rs vs)
    (h : knownLe ops tbl k first second rf rs = true) :
    ∀ x y, R.nat vf = some x → R.nat vs = some y → x ≤ y := by
  intro x y hx hy
  simp only [knownLe, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((h | h) | h) | h) | h
  · simpa using rangesOrder_sound (hrf.has hx) (hrs.has hy) h
  · subst h
    rw [hf] at hs
    cases hs
    rw [hx] at hy
    cases hy
    exact Nat.le_refl _
  · obtain ⟨x', y', hx', hy', o⟩ := hk.hasOrder h
    rw [hx'.unique ⟨_, hf, hx⟩, hy'.unique ⟨_, hs, hy⟩] at o
    simpa using o
  · simpa using sumAbove_sound lawful hc hcl hk hf hs h x y hx hy
  · simpa using differenceBelow_sound lawful hc hcl hk hf hs h x y hx hy

theorem knownLt_sound (lawful : OpFacts.Lawful ops R Run) (hc : Consistent Run ρ tbl)
    (hcl : Closed ρ tbl) (hk : k.Holds R ρ) {first second : Nat} {vf vs : Val}
    {rf rs : Option Range} (hf : ρ first = some vf) (hs : ρ second = some vs)
    (hrf : RangesHold R rf vf) (hrs : RangesHold R rs vs)
    (h : knownLt ops tbl k first second rf rs = true) :
    ∀ x y, R.nat vf = some x → R.nat vs = some y → x < y := by
  intro x y hx hy
  simp only [knownLt, Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · simpa using rangesOrder_sound (hrf.has hx) (hrs.has hy) h
  · obtain ⟨x', y', hx', hy', o⟩ := hk.hasOrder h
    rw [hx'.unique ⟨_, hf, hx⟩, hy'.unique ⟨_, hs, hy⟩] at o
    simpa using o
  · simpa using sumAbove_sound lawful hc hcl hk hf hs h x y hx hy
  · simpa using differenceBelow_sound lawful hc hcl hk hf hs h x y hx hy
  · exact offsetBelow_sound lawful hc hcl hk hf hs h x y hx hy

theorem knownDifference_sound (lawful : OpFacts.Lawful ops R Run) (hc : Consistent Run ρ tbl)
    (hcl : Closed ρ tbl) (hk : k.Holds R ρ) {first second : Nat} {vf vs : Val}
    {rf rs : Option Range} {n : Nat} (hf : ρ first = some vf) (hs : ρ second = some vs)
    (hrf : RangesHold R rf vf) (hrs : RangesHold R rs vs)
    (h : knownDifference ops tbl k second first rs rf n = true) :
    ∀ x y, R.nat vs = some x → R.nat vf = some y → x - y = n := by
  intro x y hx hy
  simp only [knownDifference, Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    · next p p' q q' =>
        simp only [decide_eq_true_eq] at h
        obtain ⟨rfl, rfl, le, eq⟩ := h
        have hp := hrs.has hx _ rfl
        have hq := hrf.has hy _ rfl
        have e1 : x = p := by have h1 := hp.2 p rfl; have h2 : p ≤ x := hp.1; omega
        have e2 : y = q := by have h1 := hq.2 q rfl; have h2 : q ≤ y := hq.1; omega
        subst e1; subst e2
        exact eq
    · cases h
  · split at h
    · next a c e =>
        obtain ⟨vals, hvals, va, vc, x', c0, eq, ha', hc', hsum⟩ := formOf_values lawful hc hcl e hs
        obtain ⟨wa, wc, rfl, ha, hcv⟩ := lookupAll_pair hvals
        cases eq
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨rfl, hr⟩ := h
        rw [hf] at ha
        cases ha
        rw [hy] at ha'
        cases ha'
        rw [hx] at hsum
        cases hsum
        have := Range.has_point.mp (hk.rangeOf_at ⟨_, hcv, hc'⟩ hr)
        omega
    · cases h

/-- A requirement that the rules decide holds of the values it names. -/
theorem decideRequirement_sound (lawful : OpFacts.Lawful ops R Run) (hc : Consistent Run ρ tbl)
    (hcl : Closed ρ tbl) (hk : k.Holds R ρ) {req : Requirement Raw} {ids : List (Option Nat)}
    {ranges : List (Option Range)} {vs : List Val}
    (hvals : ∀ (j id : Nat), ids[j]? = some (some id) → ρ id = vs[j]?)
    (hlen : vs.length = ids.length)
    (hranges : ∀ (j : Nat) (v : Val), vs[j]? = some v → RangesHold R (ranges.getD j none) v)
    (h : decideRequirement ops tbl k req ids ranges = true) : req.Relation R vs := by
  have pair : ∀ {a b : Nat}, ids = [some a, some b] →
      ∃ va vb, vs = [va, vb] ∧ ρ a = some va ∧ ρ b = some vb := fun {a b} e => by
    subst e
    match vs, hlen with
    | [va, vb], _ =>
        exact ⟨va, vb, rfl, by simpa using hvals 0 a rfl, by simpa using hvals 1 b rfl⟩
  have single : ∀ {a : Nat}, ids = [some a] → ∃ va, vs = [va] ∧ ρ a = some va := fun {a} e => by
    subst e
    match vs, hlen with
    | [va], _ => exact ⟨va, rfl, by simpa using hvals 0 a rfl⟩
  unfold decideRequirement at h
  split at h
  · next a b ra rb =>
      obtain ⟨va, vb, rfl, ha, hb⟩ := pair rfl
      exact knownLe_sound lawful hc hcl hk ha hb (by simpa using hranges 0 va rfl)
        (by simpa using hranges 1 vb rfl) h
  · next a b ra rb =>
      obtain ⟨va, vb, rfl, ha, hb⟩ := pair rfl
      exact knownLt_sound lawful hc hcl hk ha hb (by simpa using hranges 0 va rfl)
        (by simpa using hranges 1 vb rfl) h
  · next n a ra =>
      obtain ⟨va, rfl, ha⟩ := single rfl
      have hr : RangesHold R ra va := by simpa using hranges 0 va rfl
      intro x hx
      split at h
      · next r =>
          have := (hr.has hx r rfl).1
          simp only [decide_eq_true_eq] at h
          omega
      · cases h
  · next n a ra =>
      obtain ⟨va, rfl, ha⟩ := single rfl
      have hr : RangesHold R ra va := by simpa using hranges 0 va rfl
      intro x hx
      split at h
      · next lo hi =>
          have := (hr.has hx _ rfl).2 hi rfl
          simp only [decide_eq_true_eq] at h
          omega
      · cases h
  · next n a ra =>
      obtain ⟨va, rfl, ha⟩ := single rfl
      have hr : RangesHold R ra va := by simpa using hranges 0 va rfl
      intro x hx
      split at h
      · next lo hi =>
          have has := hr.has hx _ rfl
          have h1 := has.2 hi rfl
          have h2 : lo ≤ x := has.1
          simp only [decide_eq_true_eq] at h
          omega
      · cases h
  · next n b a rb ra =>
      obtain ⟨vb, va, rfl, hb, ha⟩ := pair rfl
      exact knownDifference_sound lawful hc hcl hk ha hb (by simpa using hranges 1 va rfl)
        (by simpa using hranges 0 vb rfl) h
  · next a rest =>
      obtain ⟨va, rfl, ha⟩ := single rfl
      obtain ⟨v, hv, hb⟩ := hk.hasTruth h
      rw [ha] at hv
      cases hv
      exact hb
  · next a ra =>
      obtain ⟨va, rfl, ha⟩ := single rfl
      have hr : RangesHold R ra va := by simpa using hranges 0 va rfl
      split at h
      · next lo hi =>
          obtain ⟨x, hx, _⟩ := hr _ rfl
          exact ⟨x, hx⟩
      · cases h
  · cases h

end

/-! ## Resolving the values of a requirement -/

theorem atPositions_length {α : Type} {xs : List α} :
    ∀ {ps : List Nat} {ys : List α}, atPositions xs ps = some ys → ys.length = ps.length
  | [], ys, h => by simp only [atPositions, Option.some.injEq] at h; subst h; rfl
  | p :: ps, ys, h => by
      simp only [atPositions] at h
      split at h
      · next x rest e1 e2 =>
          cases h
          simp [atPositions_length e2]
      · cases h

theorem atPositions_mem {α : Type} {xs : List α} :
    ∀ {ps : List Nat} {ys : List α}, atPositions xs ps = some ys → ∀ y, y ∈ ys → y ∈ xs
  | [], ys, h, y, m => by simp only [atPositions, Option.some.injEq] at h; subst h; cases m
  | p :: ps, ys, h, y, m => by
      simp only [atPositions] at h
      split at h
      · next x rest e1 e2 =>
          cases h
          rcases List.mem_cons.mp m with rfl | m
          · exact List.mem_of_getElem? e1
          · exact atPositions_mem e2 y m
      · cases h

theorem atPositions_getElem {α : Type} {xs : List α} :
    ∀ {ps : List Nat} {ys : List α}, atPositions xs ps = some ys →
      ∀ (i p : Nat), ps[i]? = some p → ys[i]? = xs[p]?
  | [], ys, h, i, p, e => by simp at e
  | q :: ps, ys, h, i, p, e => by
      simp only [atPositions] at h
      split at h
      · next x rest e1 e2 =>
          cases h
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at e
              subst e
              simpa using e1.symm
          | succ i =>
              simp only [List.getElem?_cons_succ] at e ⊢
              exact atPositions_getElem e2 i p e
      · cases h

variable {Valid : Val → Prop}

theorem lookupAll_valid {ρ : Valuation Val} :
    ∀ {ids : List Nat} {vs : List Val}, lookupAll ρ ids = some vs →
      (∀ i v, ρ i = some v → Valid v) → ∀ v, v ∈ vs → Valid v
  | [], vs, h, _, v, m => by
      simp only [lookupAll, Option.some.injEq] at h
      subst h
      cases m
  | i :: is, vs, h, valid, v, m => by
      simp only [lookupAll] at h
      split at h
      · next w ws e1 e2 =>
          cases h
          rcases List.mem_cons.mp m with rfl | m
          · exact valid i _ e1
          · exact lookupAll_valid e2 valid v m
      · cases h

theorem Stepped.refl {T : Type} {ρ : Valuation Val} {st : St T Raw}
    (coh : Coherent Run Valid ρ st) : Stepped Run Valid ρ ρ st st :=
  ⟨Valuation.Le.refl ρ, coh, ⟨Nat.le_refl _, [], rfl, fun _ m => nomatch m⟩, rfl, rfl⟩

theorem St.Grows.trans {T : Type} {a b c : St T Raw} (h1 : St.Grows a b) (h2 : St.Grows b c) :
    St.Grows a c := by
  obtain ⟨n1, new1, e1, low1⟩ := h1
  obtain ⟨n2, new2, e2, low2⟩ := h2
  refine ⟨Nat.le_trans n1 n2, new2 ++ new1, by rw [e2, e1, List.append_assoc], ?_⟩
  intro e m
  rcases List.mem_append.mp m with m | m
  · exact Nat.le_trans n1 (low2 e m)
  · exact low1 e m

theorem Stepped.trans {T : Type} {ρ₁ ρ₂ ρ₃ : Valuation Val} {st₁ st₂ st₃ : St T Raw}
    (h1 : Stepped Run Valid ρ₁ ρ₂ st₁ st₂) (h2 : Stepped Run Valid ρ₂ ρ₃ st₂ st₃) :
    Stepped Run Valid ρ₁ ρ₃ st₁ st₃ :=
  ⟨h1.le.trans h2.le, h2.coherent, h1.grows.trans h2.grows, by rw [h2.refusals, h1.refusals],
    by rw [h2.bounds, h1.bounds]⟩

theorem fill_valid {ρ : Valuation Val} {lo : Nat} {rs : List Val}
    (valid : ∀ i v, ρ i = some v → Valid v) (hrs : ∀ r, r ∈ rs → Valid r) :
    ∀ i v, ρ.fill lo rs i = some v → Valid v := fun i v e => by
  simp only [Valuation.fill] at e
  split at e
  · next w hw =>
      cases e
      exact valid i _ hw
  · split at e
    · exact hrs v (List.mem_of_getElem? e)
    · cases e

theorem setFrom_valid {ρ : Valuation Val} {lo : Nat} {rs : List Val}
    (valid : ∀ i v, ρ i = some v → Valid v) (hrs : ∀ r, r ∈ rs → Valid r) :
    ∀ i v, ρ.setFrom lo rs i = some v → Valid v := fun i v e => by
  simp only [Valuation.setFrom] at e
  split at e
  · exact hrs v (List.mem_of_getElem? e)
  · exact valid i v e

/-- An application of a written operation, shared: its results have the values that it gives,
and the state and the valuation still agree. -/
theorem share_sound [DecidableEq Raw] (lawful : OpFacts.Lawful ops R Run) {T : Type}
    {ρ : Valuation Val} {st : St T Raw} (coh : Coherent Run Valid ρ st) {w : Raw}
    {argIds : List Nat} {as rs : List Val} (hargs : lookupAll ρ argIds = some as)
    (hlt : ∀ a, a ∈ argIds → a < st.next) (run : Run w as rs) (hvalid : ∀ r, r ∈ rs → Valid r) :
    ∃ ρ', Stepped Run Valid ρ ρ' st (share w argIds rs.length st).2 ∧
      lookupAll ρ' (share w argIds rs.length st).1 = some rs ∧
      ∀ i, i ∈ (share w argIds rs.length st).1 → i < (share w argIds rs.length st).2.next := by
  have hfun : ∀ rs', Run w as rs' → rs' = rs := fun rs' r' => lawful.functional _ _ _ _ r' run
  simp only [share]
  split
  · next lo found =>
      obtain ⟨e, m, ew, ea, ec, el⟩ := Table.find_spec found
      subst el
      have hvs : lookupAll ρ e.args = some as := by rw [ea]; exact hargs
      have hrun : Run e.written as rs := by rw [ew]; exact run
      obtain ⟨le, sup, cons, clo, look⟩ := fill_entry coh.wf coh.consistent coh.closed
        coh.support m hvs hrun ec.symm (by rw [ew]; exact hfun)
      refine ⟨ρ.fill e.lo rs, ⟨le, ⟨sup, coh.wf, cons, clo, fill_valid coh.valid hvalid⟩,
        ⟨Nat.le_refl _, [], rfl, fun _ m => nomatch m⟩, rfl, rfl⟩, ?_, ?_⟩
      · rw [← ec]; exact look
      · intro i hi
        have := (coh.wf.mem m).2
        rw [ec] at this
        have hi := mem_range'_bounds hi
        show i < st.next
        omega
  · let e : Entry Raw := ⟨w, argIds, st.next, rs.length⟩
    have wf' : Table.WF (st.next + rs.length) (e :: st.table) :=
      ⟨hlt, Nat.le_refl _, coh.wf⟩
    obtain ⟨cons', clo'⟩ := consistent_extend (new := [e]) coh.support coh.consistent coh.closed
      (fun e' m => by simp at m; subst m; exact Nat.le_refl _)
    obtain ⟨le, sup, cons, clo, look⟩ := fill_entry wf' cons' clo'
      (coh.support.mono (Nat.le_add_right _ _)) (e := e) List.mem_cons_self hargs run rfl hfun
    refine ⟨ρ.fill st.next rs, ⟨le, ⟨sup, wf', cons, clo, fill_valid coh.valid hvalid⟩,
      ⟨Nat.le_add_right _ _, [e], rfl, fun e' m => by simp at m; subst m; exact Nat.le_refl _⟩,
      rfl, rfl⟩, look, ?_⟩
    intro i hi
    have hi := mem_range'_bounds hi
    simp only
    omega

/-- Resolving an operand of a requirement: the identifier it resolves to has a value that the
operand names. -/
theorem resolve_sound [DecidableEq Raw] (lawful : OpFacts.Lawful ops R Run)
    (runValid : ∀ w as rs, Run w as rs → (∀ a, a ∈ as → Valid a) → ∀ r, r ∈ rs → Valid r)
    {T : Type} {ρ : Valuation Val} {st : St T Raw} (coh : Coherent Run Valid ρ st)
    {argIds : List Nat} {args : List Val} (hargs : lookupAll ρ argIds = some args)
    (hlt : ∀ a, a ∈ argIds → a < st.next) {operand : Operand Raw}
    (runs : ∀ w ps, operand = .apply w ps →
      ∃ as rs, atPositions args ps = some as ∧ Run w as rs ∧ rs.length = 1) :
    ∃ ρ', Stepped Run Valid ρ ρ' st (resolve argIds st operand).2 ∧
      ∀ id, (resolve argIds st operand).1 = some id →
        ∃ v, ρ' id = some v ∧ operand.Denotes Run args v := by
  cases operand with
  | arg position =>
      refine ⟨ρ, Stepped.refl coh, fun id e => ?_⟩
      simp only [resolve] at e
      have := lookupAll_getElem hargs e
      cases hv : args[position]? with
      | none =>
          rw [hv] at this
          exact absurd this (lookupAll_mem hargs id (List.mem_of_getElem? e))
      | some v =>
          rw [hv] at this
          exact ⟨v, this, hv⟩
  | apply w ps =>
      obtain ⟨as, rs, has, run, one⟩ := runs w ps rfl
      simp only [resolve]
      split
      · next ids' e =>
          obtain ⟨values, hvalues, hl⟩ := atPositions_lookupAll hargs e
          rw [has] at hvalues
          cases hvalues
          have hlt' : ∀ a, a ∈ ids' → a < st.next := fun a m => hlt a (atPositions_mem e a m)
          have hvalid : ∀ r, r ∈ rs → Valid r :=
            runValid w as rs run (lookupAll_valid hl coh.valid)
          obtain ⟨ρ', step, look, _⟩ := share_sound lawful coh hl hlt' run hvalid
          rw [one] at step look
          refine ⟨ρ', step, fun id hid => ?_⟩
          match rs, one with
          | [r], _ =>
              obtain ⟨rest, hrest⟩ : ∃ rest, (share w ids' 1 st).1 = id :: rest := by
                cases h : (share w ids' 1 st).1 with
                | nil => rw [h] at hid; cases hid
                | cons a rest =>
                    rw [h] at hid
                    simp only [List.head?_cons, Option.some.injEq] at hid
                    exact ⟨rest, by rw [hid]⟩
              rw [hrest] at look
              refine ⟨r, ?_, as, [r], has, run, rfl⟩
              simpa using lookupAll_get look 0 (by simp)
      · refine ⟨ρ, Stepped.refl coh, fun id e => ?_⟩
        cases e

/-! ### The refusals and bounds of a step -/

theorem share_state [DecidableEq Raw] {T : Type} (w : Raw) (args : List Nat) (count : Nat)
    (st : St T Raw) : (share w args count st).2.refusals = st.refusals ∧
      (share w args count st).2.bounds = st.bounds := by
  simp only [share]
  split <;> exact ⟨rfl, rfl⟩

theorem resolve_state [DecidableEq Raw] {T : Type} (argIds : List Nat) (st : St T Raw)
    (o : Operand Raw) : (resolve argIds st o).2.refusals = st.refusals ∧
      (resolve argIds st o).2.bounds = st.bounds := by
  cases o with
  | arg => exact ⟨rfl, rfl⟩
  | apply w ps =>
      simp only [resolve]
      split
      · exact share_state _ _ _ _
      · exact ⟨rfl, rfl⟩

theorem resolveAll_state [DecidableEq Raw] {T : Type} (argIds : List Nat) :
    ∀ (os : List (Operand Raw)) (st : St T Raw), (resolveAll argIds os st).2.refusals =
      st.refusals ∧ (resolveAll argIds os st).2.bounds = st.bounds
  | [], _ => ⟨rfl, rfl⟩
  | o :: os, st => by
      simp only [resolveAll]
      obtain ⟨r1, b1⟩ := resolve_state argIds st o
      obtain ⟨r2, b2⟩ := resolveAll_state argIds os (resolve argIds st o).2
      exact ⟨r2.trans r1, b2.trans b1⟩

theorem checkRequirements_state [DecidableEq Raw] {T : Type} (ops : OpFacts Raw) (k : Known)
    (place : Place) (written : Raw) (argIds : List Nat) :
    ∀ (reqs : List (Requirement Raw)) (st : St T Raw),
      (∃ new, (checkRequirements ops k place written argIds reqs st).refusals =
        new ++ st.refusals) ∧
        (checkRequirements ops k place written argIds reqs st).bounds = st.bounds
  | [], st => ⟨⟨[], rfl⟩, rfl⟩
  | req :: rest, st => by
      simp only [checkRequirements]
      obtain ⟨r1, b1⟩ := resolveAll_state argIds req.operands st
      generalize resolveAll argIds req.operands st = resolved at r1 b1 ⊢
      split
      · obtain ⟨⟨new, e⟩, b⟩ := checkRequirements_state ops k place written argIds rest resolved.2
        exact ⟨⟨new, by rw [e, r1]⟩, by rw [b, b1]⟩
      · refine ⟨?_, ?_⟩
        · obtain ⟨⟨new, e⟩, _⟩ := checkRequirements_state ops k place written argIds rest
            { resolved.2 with refusals := _ :: resolved.2.refusals }
          exact ⟨new ++ [⟨.domain, place, .unjustified written req
            (List.zipWith (operandRange ops k argIds) req.operands resolved.1)⟩],
            by rw [e]; simp [r1]⟩
        · rw [(checkRequirements_state ops k place written argIds rest _).2]
          exact b1

/-! ### Resolving and deciding the requirements of an application -/

theorem Resolved.le {ρ ρ' : Valuation Val} (h : ρ.Le ρ') {args : List Val} :
    ∀ {os : List (Operand Raw)} {is : List (Option Nat)}, Resolved Run args ρ os is →
      Resolved Run args ρ' os is
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨first, rest⟩ =>
      ⟨fun id e => by
        obtain ⟨v, hv, hd⟩ := first id e
        exact ⟨v, h _ _ hv, hd⟩, Resolved.le h rest⟩

theorem Resolved.values {ρ : Valuation Val} {args : List Val} :
    ∀ {os : List (Operand Raw)} {is : List (Option Nat)}, Resolved Run args ρ os is →
      (∀ i, i ∈ is → i ≠ none) →
      ∃ vs, vs.length = is.length ∧ (∀ (j id : Nat), is[j]? = some (some id) → ρ id = vs[j]?) ∧
        DenotesAll Run args os vs
  | [], [], _, _ => ⟨[], rfl, fun j id e => by simp at e, trivial⟩
  | o :: os, i :: is, ⟨first, rest⟩, all => by
      obtain ⟨id, rfl⟩ := Option.ne_none_iff_exists'.mp (all i List.mem_cons_self)
      obtain ⟨v, hv, hd⟩ := first id rfl
      obtain ⟨vs, hl, hvs, hds⟩ := Resolved.values rest
        (fun i' m => all i' (List.mem_cons_of_mem _ m))
      refine ⟨v :: vs, by simp [hl], fun j id' e => ?_, hd, hds⟩
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          cases e
          simpa using hv
      | succ j =>
          simp only [List.getElem?_cons_succ] at e ⊢
          exact hvs j id' e

theorem Resolved.length {ρ : Valuation Val} {args : List Val} :
    ∀ {os : List (Operand Raw)} {is : List (Option Nat)}, Resolved Run args ρ os is →
      is.length = os.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, rest⟩ => by simp [Resolved.length rest]

theorem Resolved.get {ρ : Valuation Val} {args : List Val} :
    ∀ {os : List (Operand Raw)} {is : List (Option Nat)}, Resolved Run args ρ os is →
      ∀ (j id : Nat), is[j]? = some (some id) →
        ∃ o v, os[j]? = some o ∧ ρ id = some v ∧ o.Denotes Run args v
  | [], [], _, j, id, e => by simp at e
  | o :: os, i :: is, ⟨first, rest⟩, j, id, e => by
      cases j with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          obtain ⟨v, hv, hd⟩ := first id e
          exact ⟨o, v, rfl, hv, hd⟩
      | succ j =>
          simp only [List.getElem?_cons_succ] at e ⊢
          exact Resolved.get rest j id e

theorem resolveAll_sound [DecidableEq Raw] (lawful : OpFacts.Lawful ops R Run)
    (runValid : ∀ w as rs, Run w as rs → (∀ a, a ∈ as → Valid a) → ∀ r, r ∈ rs → Valid r)
    {T : Type} {argIds : List Nat} {args : List Val} :
    ∀ (os : List (Operand Raw)) {ρ : Valuation Val} {st : St T Raw},
      Coherent Run Valid ρ st → lookupAll ρ argIds = some args →
      (∀ a, a ∈ argIds → a < st.next) →
      (∀ o, o ∈ os → ∀ w ps, o = .apply w ps →
        ∃ as rs, atPositions args ps = some as ∧ Run w as rs ∧ rs.length = 1) →
      ∃ ρ', Stepped Run Valid ρ ρ' st (resolveAll argIds os st).2 ∧
        Resolved Run args ρ' os (resolveAll argIds os st).1
  | [], ρ, st, coh, _, _, _ => ⟨ρ, Stepped.refl coh, trivial⟩
  | o :: os, ρ, st, coh, hargs, hlt, runs => by
      simp only [resolveAll]
      obtain ⟨ρ₁, step₁, first⟩ := resolve_sound lawful runValid coh hargs hlt
        (runs o List.mem_cons_self)
      obtain ⟨ρ₂, step₂, rest⟩ := resolveAll_sound lawful runValid os step₁.coherent
        (lookupAll_le step₁.le hargs) (fun a m => Nat.lt_of_lt_of_le (hlt a m) step₁.grows.next)
        (fun o' m => runs o' (List.mem_cons_of_mem _ m))
      refine ⟨ρ₂, step₁.trans step₂, fun id e => ?_, rest⟩
      obtain ⟨v, hv, hd⟩ := first id e
      exact ⟨v, step₂.le _ _ hv, hd⟩

theorem operandRange_sound (lawful : OpFacts.Lawful ops R Run) {k : Known} (hk : k.Holds R ρ)
    {argIds : List Nat} {args : List Val} (hargs : lookupAll ρ argIds = some args)
    {operand : Operand Raw} {id : Nat} {v : Val} (hv : ρ id = some v)
    (hd : operand.Denotes Run args v) :
    RangesHold R (operandRange ops k argIds operand (some id)) v := by
  cases operand with
  | arg position =>
      intro r e
      obtain ⟨n, ⟨w, hw, hn⟩, has⟩ := hk.rangeOf e
      rw [hv] at hw
      cases hw
      exact ⟨n, hn, has⟩
  | apply w ps =>
      obtain ⟨as, rs, has, run, head⟩ := hd
      have known : ∀ (i : Nat) (r : Range),
          (ps.map fun p => (argIds[p]?).bind k.rangeOf)[i]? = some (some r) →
          ∃ v n, as[i]? = some v ∧ R.nat v = some n ∧ r.Has n := by
        intro i r e
        simp only [List.getElem?_map] at e
        cases hp : ps[i]? with
        | none => rw [hp] at e; cases e
        | some p =>
            rw [hp] at e
            simp only [Option.map_some, Option.some.injEq] at e
            cases hid : argIds[p]? with
            | none => rw [hid] at e; cases e
            | some idp =>
                rw [hid] at e
                simp only [Option.bind_some] at e
                obtain ⟨n, ⟨w', hw', hn⟩, hasr⟩ := hk.rangeOf e
                have := lookupAll_getElem hargs hid
                rw [hw'] at this
                exact ⟨w', n, by rw [atPositions_getElem has i p hp, ← this], hn, hasr⟩
      have fromOps : ∀ r, (ops.ranges w (ps.map fun p => (argIds[p]?).bind k.rangeOf)).head?.join
          = some r → ∃ n, R.nat v = some n ∧ r.Has n := by
        intro r e
        have e0 : (ops.ranges w (ps.map fun p => (argIds[p]?).bind k.rangeOf))[0]? =
            some (some r) := by
          rw [← List.head?_eq_getElem?]
          cases hh : (ops.ranges w (ps.map fun p => (argIds[p]?).bind k.rangeOf)).head? with
          | none => rw [hh] at e; cases e
          | some o => rw [hh] at e; simp at e; rw [e]
        obtain ⟨v', n, hv', hn, hasr⟩ := lawful.ranges _ _ _ _ run known 0 r e0
        rw [← List.head?_eq_getElem?, head] at hv'
        cases hv'
        exact ⟨n, hn, hasr⟩
      intro r e
      simp only [operandRange] at e
      have nat : ∃ n, R.nat v = some n := by
        cases h1 : k.rangeOf id with
        | some r1 =>
            obtain ⟨n, ⟨w', hw', hn⟩, _⟩ := hk.rangeOf h1
            rw [hv] at hw'
            cases hw'
            exact ⟨n, hn⟩
        | none =>
            rw [h1] at e
            simp only [Range.meet] at e
            obtain ⟨n, hn, _⟩ := fromOps r e
            exact ⟨n, hn⟩
      obtain ⟨n, hn⟩ := nat
      refine ⟨n, hn, Range.meet_has e (fun r1 e1 => ?_) (fun r2 e2 => ?_)⟩
      · obtain ⟨n', ⟨w', hw', hn'⟩, has'⟩ := hk.rangeOf e1
        rw [hv] at hw'
        cases hw'
        rw [hn] at hn'
        cases hn'
        exact has'
      · obtain ⟨n', hn', has'⟩ := fromOps r2 e2
        rw [hn] at hn'
        cases hn'
        exact has'

theorem decideRequirement_some {tbl : Table Raw} {k : Known} {req : Requirement Raw}
    {ids : List (Option Nat)} {ranges : List (Option Range)}
    (h : decideRequirement ops tbl k req ids ranges = true) : ∀ i, i ∈ ids → i ≠ none := by
  unfold decideRequirement at h
  split at h <;> first
    | (intro i m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
       rcases m with rfl | rfl <;> simp)
    | (intro i m; simp only [List.mem_cons, List.not_mem_nil, or_false] at m
       subst m; simp)
    | cases h

/-- The requirements of an application that the walk decides hold of its operands' values. -/
theorem checkRequirements_sound [DecidableEq Raw] (lawful : OpFacts.Lawful ops R Run)
    (runValid : ∀ w as rs, Run w as rs → (∀ a, a ∈ as → Valid a) → ∀ r, r ∈ rs → Valid r)
    {T : Type} {k : Known} {place : Place} {written : Raw} {argIds : List Nat}
    {args : List Val} :
    ∀ (reqs : List (Requirement Raw)) {ρ : Valuation Val} {st : St T Raw},
      Coherent Run Valid ρ st → k.Holds R ρ → lookupAll ρ argIds = some args →
      (∀ a, a ∈ argIds → a < st.next) →
      (∀ req, req ∈ reqs → ∀ o, o ∈ req.operands → ∀ w ps, o = .apply w ps →
        ∃ as rs, atPositions args ps = some as ∧ Run w as rs ∧ rs.length = 1) →
      (checkRequirements ops k place written argIds reqs st).refusals = [] →
      ∃ ρ', Stepped Run Valid ρ ρ' st (checkRequirements ops k place written argIds reqs st) ∧
        ∀ req, req ∈ reqs → req.Holds Run R args
  | [], ρ, st, coh, _, _, _, _, _ => ⟨ρ, Stepped.refl coh, fun _ m => nomatch m⟩
  | req :: rest, ρ, st, coh, hk, hargs, hlt, runs, hnone => by
      obtain ⟨ρ₁, step₁, res⟩ := resolveAll_sound lawful runValid req.operands coh hargs hlt
        (runs req List.mem_cons_self)
      simp only [checkRequirements] at hnone ⊢
      generalize resolveAll argIds req.operands st = resolved at step₁ res hnone ⊢
      have hk₁ := hk.le step₁.le
      by_cases cond : (k.dead || decideRequirement ops resolved.2.table k req resolved.1
          (List.zipWith (operandRange ops k argIds) req.operands resolved.1)) = true
      · simp only [cond, ↓reduceIte] at hnone ⊢
        have dec : decideRequirement ops resolved.2.table k req resolved.1
            (List.zipWith (operandRange ops k argIds) req.operands resolved.1) = true := by
          simpa [hk.alive] using cond
        have holds : req.Holds Run R args := by
          have all := decideRequirement_some dec
          obtain ⟨vs, hl, hvs, hds⟩ := res.values all
          refine ⟨vs, hds, decideRequirement_sound lawful step₁.coherent.consistent
            step₁.coherent.closed hk₁ hvs hl ?_ dec⟩
          intro j v hv
          have lt : j < resolved.1.length := by
            have := (List.getElem?_eq_some_iff.mp hv).1
            omega
          obtain ⟨id, hid⟩ : ∃ id, resolved.1[j]? = some (some id) := by
            have m := List.getElem_mem lt
            obtain ⟨id, e⟩ := Option.ne_none_iff_exists'.mp (all _ m)
            exact ⟨id, by rw [List.getElem?_eq_getElem lt, e]⟩
          obtain ⟨o, v', ho, hv', hd⟩ := res.get j id hid
          have := hvs j id hid
          rw [hv', hv] at this
          cases this
          rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith, ho, hid]
          exact operandRange_sound lawful hk₁ (lookupAll_le step₁.le hargs) hv' hd
        obtain ⟨ρ₂, step₂, others⟩ := checkRequirements_sound lawful runValid rest
          step₁.coherent hk₁ (lookupAll_le step₁.le hargs)
          (fun a m => Nat.lt_of_lt_of_le (hlt a m) step₁.grows.next)
          (fun req' m => runs req' (List.mem_cons_of_mem _ m)) hnone
        refine ⟨ρ₂, step₁.trans step₂, fun req' m => ?_⟩
        rcases List.mem_cons.mp m with rfl | m
        · exact holds
        · exact others req' m
      · exfalso
        simp only [Bool.not_eq_true] at cond
        simp only [cond, Bool.false_eq_true, ↓reduceIte] at hnone
        obtain ⟨⟨new, e⟩, _⟩ := checkRequirements_state ops k place written argIds rest
          { resolved.2 with refusals := ⟨.domain, place, .unjustified written req
            (List.zipWith (operandRange ops k argIds) req.operands resolved.1)⟩ ::
              resolved.2.refusals }
        rw [e] at hnone
        simp at hnone

end

end FactCheck

end Zkc.Core
