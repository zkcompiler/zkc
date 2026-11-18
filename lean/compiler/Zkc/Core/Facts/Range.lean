module

public import Zkc.Core.Program.Requirement

@[expose] public section

/-!
The arithmetic of ranges of naturals: what the analysis computes of a natural from what it knows
of others, each operation with the lemma that it holds of the numbers that it is about. The type
of a range and what it is for a natural to be in one are in `Program/Requirement.lean`.

Two ranges meet and join (`Range.inter`, `Range.meet`, `Range.hull`); a range of one number, of
none, and below a number of a range (`Range.point`, `Range.nothing`, `Range.below`); the ranges of
a sum, a difference, a product, a quotient, a remainder and a power from those of their operands
(`Range.add` to `Range.pow`; a power's ends are computed only when they are small enough, TY8),
and an operation of two naturals or of one on the list of the ranges of its operands
(`Range.onTwo`, `Range.onOne`); and the range of a natural after iterations that each add a term
of a range (`Range.afterSums`), which starts where the initial range starts.
-/

namespace Zkc.Core

/-! ## Meeting and joining -/

namespace Range

/-- The numbers in both ranges. -/
def inter (a b : Range) : Range :=
  ⟨max a.lo b.lo, match a.hi, b.hi with
    | some x, some y => some (min x y)
    | some x, none => some x
    | none, y => y⟩

/-- The numbers between the two ranges, both included. -/
def hull (a b : Range) : Range :=
  ⟨min a.lo b.lo, match a.hi, b.hi with
    | some x, some y => some (max x y)
    | _, _ => none⟩

/-- The range of one number. -/
def point (n : Nat) : Range := ⟨n, some n⟩

/-- The range of no number. -/
def nothing : Range := ⟨1, some 0⟩

/-- The numbers below a number of the range: from zero to its upper end less one; no number
when the upper end is zero, every natural when it has none. -/
def below (r : Range) : Range :=
  match r.hi with
  | some 0 => Range.nothing
  | some (h + 1) => ⟨0, some h⟩
  | none => ⟨0, none⟩

end Range

/-- What two pieces of knowledge of one natural say together; nothing known is the absence. -/
def Range.meet : Option Range → Option Range → Option Range
  | some a, some b => some (a.inter b)
  | some a, none => some a
  | none, b => b

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

theorem has_point {n m : Nat} : (Range.point n).Has m ↔ m = n :=
  ⟨fun ⟨l, u⟩ => Nat.le_antisymm (u n rfl) l,
    fun e => by subst e; exact ⟨Nat.le_refl _, fun h e => by cases e; exact Nat.le_refl _⟩⟩

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

/-! ## Arithmetic -/

namespace Range

/-- The ranges of a sum. -/
def add : Option Range → Option Range → Option Range
  | some a, some b => some ⟨a.lo + b.lo, match a.hi, b.hi with
      | some x, some y => some (x + y)
      | _, _ => none⟩
  | _, _ => none

/-- The ranges of a difference, not below zero. -/
def sub : Option Range → Option Range → Option Range
  | some a, some b => some ⟨match b.hi with | some y => a.lo - y | none => 0, a.hi.map (· - b.lo)⟩
  | _, _ => none

/-- The ranges of a product. -/
def mul : Option Range → Option Range → Option Range
  | some a, some b => some ⟨a.lo * b.lo, match a.hi, b.hi with
      | some x, some y => some (x * y)
      | _, _ => none⟩
  | _, _ => none

/-- The ranges of a quotient rounded down, where the divisor is at least one. -/
def div : Option Range → Option Range → Option Range
  | some a, some b => some ⟨match b.hi with | some y => a.lo / y | none => 0,
      a.hi.map (· / max b.lo 1)⟩
  | _, _ => none

/-- The ranges of a remainder, where the divisor is at least one. -/
def rem : Option Range → Option Range → Option Range
  | some a, some b => some ⟨0, match a.hi, b.hi with
      | some x, some y => some (min x (y - 1))
      | some x, none => some x
      | none, some y => some (y - 1)
      | none, none => none⟩
  | _, _ => none

/-- The number of binary digits of a natural, within a number of steps: none for zero. -/
def digitsWithin : Nat → Nat → Nat
  | 0, _ => 0
  | steps + 1, n => if n = 0 then 0 else digitsWithin steps (n / 2) + 1

/-- The number of binary digits of a natural, zero being written with one. -/
def binaryDigits (n : Nat) : Nat := n.log2 + 1

/-- Whether an end of the range of a power is computed: when its exponent times the number of
binary digits of its base is at most 65536 (TY8). -/
def powComputed (base exponent : Nat) : Bool := decide (exponent * binaryDigits base ≤ 65536)

/-- The ranges of a power: a number to the power zero is one. An end whose power would be too
large to compute is not computed: the lower end is then one when the base is at least one, and
the upper end is absent. -/
def pow : Option Range → Option Range → Option Range
  | some a, some b =>
      some ⟨if 1 ≤ a.lo then (if powComputed a.lo b.lo then a.lo ^ b.lo else 1)
          else if b.hi = some 0 then 1 else 0,
        match a.hi, b.hi with
        | some x, some y =>
            if powComputed x y then some (max (x ^ y) (if b.lo = 0 then 1 else 0)) else none
        | _, _ => none⟩
  | _, _ => none

end Range

namespace Range

theorem add_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.add a b = some r → r.Has (x + y) := by
  intro r e
  cases a with
  | none => simp [Range.add] at e
  | some a =>
      cases b with
      | none => simp [Range.add] at e
      | some b =>
          simp only [Range.add, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨by simp only; omega, fun h e => ?_⟩
          rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;> simp at e
          have := ua ahi rfl
          have := ub bhi rfl
          omega

theorem sub_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.sub a b = some r → r.Has (x - y) := by
  intro r e
  cases a with
  | none => simp [Range.sub] at e
  | some a =>
      cases b with
      | none => simp [Range.sub] at e
      | some b =>
          simp only [Range.sub, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          rcases a with ⟨alo, ahi⟩
          rcases b with ⟨blo, _ | bhi⟩
          · have la : alo ≤ x := la
            have lb : blo ≤ y := lb
            refine ⟨Nat.zero_le _, fun h e => ?_⟩
            cases ahi with
            | none => cases e
            | some ahi =>
                simp only [Option.map_some, Option.some.injEq] at e
                subst e
                have := ua ahi rfl
                omega
          · have la : alo ≤ x := la
            have lb : blo ≤ y := lb
            have hy := ub bhi rfl
            refine ⟨by show alo - bhi ≤ x - y; omega, fun h e => ?_⟩
            cases ahi with
            | none => cases e
            | some ahi =>
                simp only [Option.map_some, Option.some.injEq] at e
                subst e
                have := ua ahi rfl
                omega

theorem mul_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.mul a b = some r → r.Has (x * y) := by
  intro r e
  cases a with
  | none => simp [Range.mul] at e
  | some a =>
      cases b with
      | none => simp [Range.mul] at e
      | some b =>
          simp only [Range.mul, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨Nat.mul_le_mul la lb, fun h e => ?_⟩
          rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;> simp at e
          subst e
          exact Nat.mul_le_mul (ua ahi rfl) (ub bhi rfl)

theorem div_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) (pos : 1 ≤ y) :
    ∀ r, Range.div a b = some r → r.Has (x / y) := by
  intro r e
  cases a with
  | none => simp [Range.div] at e
  | some a =>
      cases b with
      | none => simp [Range.div] at e
      | some b =>
          simp only [Range.div, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨?_, fun h e => ?_⟩
          · cases hbh : b.hi with
            | none => simp
            | some yh =>
                simp only
                have := ub yh hbh
                exact Nat.le_trans (Nat.div_le_div_right la) (Nat.div_le_div_left this pos)
          · cases hah : a.hi with
            | none => rw [hah] at e; cases e
            | some xh =>
                rw [hah] at e
                simp only [Option.map_some, Option.some.injEq] at e
                subst e
                exact Nat.le_trans (Nat.div_le_div_right (ua xh hah))
                  (Nat.div_le_div_left (Nat.max_le.mpr ⟨lb, pos⟩) (by omega))

theorem rem_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) (pos : 1 ≤ y) :
    ∀ r, Range.rem a b = some r → r.Has (x % y) := by
  intro r e
  cases a with
  | none => simp [Range.rem] at e
  | some a =>
      cases b with
      | none => simp [Range.rem] at e
      | some b =>
          simp only [Range.rem, Option.some.injEq] at e
          subst e
          obtain ⟨_, ua⟩ := ha a rfl
          obtain ⟨_, ub⟩ := hb b rfl
          have lt := Nat.mod_lt x (by omega : y > 0)
          have le := Nat.mod_le x y
          refine ⟨Nat.zero_le _, fun h e => ?_⟩
          rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
            simp only [Option.some.injEq, reduceCtorEq] at e
          · subst e
            have := ub bhi rfl
            omega
          · subst e
            have := ua ahi rfl
            omega
          · subst e
            have := ua ahi rfl
            have := ub bhi rfl
            exact Nat.le_min.mpr ⟨by omega, by omega⟩

theorem pow_has {a b : Option Range} {x y : Nat} (ha : ∀ r, a = some r → r.Has x)
    (hb : ∀ r, b = some r → r.Has y) : ∀ r, Range.pow a b = some r → r.Has (x ^ y) := by
  intro r e
  cases a with
  | none => simp [Range.pow] at e
  | some a =>
      cases b with
      | none => simp [Range.pow] at e
      | some b =>
          simp only [Range.pow, Option.some.injEq] at e
          subst e
          obtain ⟨la, ua⟩ := ha a rfl
          obtain ⟨lb, ub⟩ := hb b rfl
          refine ⟨?_, fun h e => ?_⟩
          · simp only
            split
            · next one =>
                split
                · exact Nat.le_trans (Nat.pow_le_pow_left la _)
                    (Nat.pow_le_pow_right (by omega) lb)
                · exact Nat.pow_pos (by omega)
            · split
              · next zero =>
                  have := ub 0 zero
                  have : y = 0 := by omega
                  subst this
                  simp
              · exact Nat.zero_le _
          · rcases a with ⟨alo, _ | ahi⟩ <;> rcases b with ⟨blo, _ | bhi⟩ <;>
              simp only [reduceCtorEq] at e
            split at e
            · simp only [Option.some.injEq] at e
              subst e
              have hx := ua ahi rfl
              have hy := ub bhi rfl
              simp only at lb
              cases x with
              | zero =>
                  cases y with
                  | zero =>
                      have : blo = 0 := by omega
                      subst this
                      exact Nat.le_max_right _ _
                  | succ y => simp
              | succ x =>
                  exact Nat.le_trans (Nat.le_trans (Nat.pow_le_pow_left hx _)
                    (Nat.pow_le_pow_right (by omega) hy)) (Nat.le_max_left _ _)
            · cases e

end Range

/-! ## Operations on the ranges of their operands -/

/-- The range of the result of an operation on two naturals, from those of its operands. -/
def Range.onTwo (f : Option Range → Option Range → Option Range) :
    List (Option Range) → List (Option Range)
  | [a, b] => [f a b]
  | _ => []

/-- The range of the result of an operation that returns its one operand. -/
def Range.onOne : List (Option Range) → List (Option Range)
  | [a] => [a]
  | _ => []

theorem onTwo_has {f : Option Range → Option Range → Option Range} {known : List (Option Range)}
    {x y z : Nat}
    (sound : ∀ ka kb, (∀ r, ka = some r → r.Has x) → (∀ r, kb = some r → r.Has y) →
      ∀ r, f ka kb = some r → r.Has z)
    (hx : ∀ r, known[0]? = some (some r) → r.Has x)
    (hy : ∀ r, known[1]? = some (some r) → r.Has y) :
    ∀ (i : Nat) (r : Range), (Range.onTwo f known)[i]? = some (some r) → i = 0 ∧ r.Has z := by
  intro i r e
  match known, hx, hy with
  | [ka, kb], hx, hy =>
      simp only [Range.onTwo] at e
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at e
          exact ⟨rfl, sound ka kb (fun r h => hx r (by simp [h])) (fun r h => hy r (by simp [h]))
            r e⟩
      | succ i => simp at e
  | [], _, _ => simp [Range.onTwo] at e
  | [_], _, _ => simp [Range.onTwo] at e
  | _ :: _ :: _ :: _, _, _ => simp [Range.onTwo] at e

theorem onOne_has {known : List (Option Range)} {x : Nat}
    (hx : ∀ r, known[0]? = some (some r) → r.Has x) :
    ∀ (i : Nat) (r : Range), (Range.onOne known)[i]? = some (some r) → i = 0 ∧ r.Has x := by
  intro i r e
  match known, hx with
  | [ka], hx =>
      simp only [Range.onOne] at e
      cases i with
      | zero => exact ⟨rfl, hx r (by simpa using e)⟩
      | succ i => simp at e
  | [], _ => simp [Range.onOne] at e
  | _ :: _ :: _, _ => simp [Range.onOne] at e

/-! ## A natural after iterations that each add a term -/

/-- The range of a natural from an initial range, after at most `high` iterations that each add
a term of a range: it starts where the initial range starts (TY8). -/
def Range.afterSums (initial term : Range) (high : Option Nat) : Range :=
  ⟨initial.lo,
    match initial.hi, high, term.hi with
    | some h₀, some n, some ht => some (h₀ + n * ht)
    | _, _, _ => none⟩

namespace Range

theorem afterSums_zero {r₀ rt : Range} {n : Nat} (h : r₀.Has n) :
    (Range.afterSums r₀ rt (some 0)).Has n := by
  obtain ⟨lo, hi⟩ := h
  refine ⟨lo, fun h e => ?_⟩
  simp only [Range.afterSums] at e
  rcases r₀ with ⟨l₀, _ | h₀⟩ <;> rcases rt with ⟨lt, _ | ht⟩ <;> simp at e
  have := hi h₀ rfl
  omega

theorem afterSums_step {r₀ rt : Range} {i n t : Nat}
    (h : (Range.afterSums r₀ rt (some i)).Has n) (ht : rt.Has t) :
    (Range.afterSums r₀ rt (some (i + 1))).Has (n + t) := by
  obtain ⟨lo, hi⟩ := h
  obtain ⟨tlo, thi⟩ := ht
  simp only [Range.afterSums] at lo hi ⊢
  refine ⟨Nat.le_trans lo (Nat.le_add_right _ _), fun h e => ?_⟩
  rcases r₀ with ⟨l₀, _ | h₀⟩ <;> rcases rt with ⟨lt, _ | ht'⟩ <;> simp at e hi thi
  subst e
  have := hi
  have := thi
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem afterSums_widen {r₀ rt : Range} {N n : Nat} {high : Option Nat}
    (h : (Range.afterSums r₀ rt (some N)).Has n)
    (hhigh : ∀ m, high = some m → N ≤ m) : (Range.afterSums r₀ rt high).Has n := by
  obtain ⟨lo, hi⟩ := h
  simp only [Range.afterSums] at lo hi ⊢
  refine ⟨lo, fun h e => ?_⟩
  rcases r₀ with ⟨l₀, _ | h₀⟩ <;> rcases high with _ | m <;> rcases rt with ⟨lt, _ | ht⟩ <;>
    simp at e hi
  subst e
  have := hhigh m rfl
  exact Nat.le_trans hi (Nat.add_le_add_left (Nat.mul_le_mul_right _ this) _)

end Range

end Zkc.Core
