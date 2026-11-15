module

public import Zkc.Core.Facts.State
public import Zkc.Core.Program.Library

@[expose] public section

/-!
What the state of the check of facts says of a run.

A run gives identifiers values: a valuation, partial, that grows along the run. An identifier
has a value once a variable of the run has held it, and keeps it. Of a valuation, the table says
that where a result of an entry has a value, its operands have values and the operation applied
to them gives the results; what is known says that the region runs, that each range, order,
truth value and shape of a choice holds. The operations are a relation `Run` from a written
form and the values of its operands to the values of its results, and how the check reads a
value (as a natural, as a truth value) is a `Reading`: both are given by the dialect, with the
laws that `OpFacts` satisfies against them.
-/

namespace Zkc.Core

namespace FactCheck

/-- How the check reads a value: as a natural, as a truth value; nothing for a value that is
not one. -/
structure Reading (Val : Type) where
  nat : Val → Option Nat
  bool : Val → Option Bool

/-- A partial assignment of values to identifiers. -/
abbrev Valuation (Val : Type) : Type := Nat → Option Val

section
variable {Val : Type}

/-- `ρ'` keeps every value of `ρ`. -/
def Valuation.Le (ρ ρ' : Valuation Val) : Prop := ∀ i v, ρ i = some v → ρ' i = some v

/-- Nothing has a value from `n` on. -/
def Support (n : Nat) (ρ : Valuation Val) : Prop := ∀ i, n ≤ i → ρ i = none

/-- The valuation with the values given at `lo, lo + 1, ...`. -/
def Valuation.setFrom (ρ : Valuation Val) (lo : Nat) (vs : List Val) : Valuation Val :=
  fun i => if lo ≤ i ∧ i < lo + vs.length then vs[i - lo]? else ρ i

/-- The valuation below `t`. -/
def Valuation.below (ρ : Valuation Val) (t : Nat) : Valuation Val :=
  fun i => if i < t then ρ i else none

/-- The valuation with the values given at `lo, lo + 1, ...` where it has none. -/
def Valuation.fill (ρ : Valuation Val) (lo : Nat) (vs : List Val) : Valuation Val :=
  fun i => match ρ i with
    | some v => some v
    | none => if lo ≤ i ∧ i < lo + vs.length then vs[i - lo]? else none

/-- The values of identifiers, when each has one. -/
def valuesOf (ρ : Valuation Val) : List Nat → Option (List Val)
  | [] => some []
  | i :: is =>
      match ρ i, valuesOf ρ is with
      | some v, some vs => some (v :: vs)
      | _, _ => none

/-! ## What is known, of a valuation -/

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
  choices : ∀ c, c ∈ k.choices → ρ c.result ≠ none ∧ ∀ b, BoolAt R ρ c.result b →
    b = c.conjunction → BoolAt R ρ c.condition b ∧ BoolAt R ρ c.other b

/-! ## The table, of a valuation -/

variable {Raw : Type}

/-- Where an entry's operands and one of its results have values, the operation applied to the
operands' values gives results with that value there. -/
def Consistent (Run : Raw → List Val → List Val → Prop) (ρ : Valuation Val) (tbl : Table Raw) :
    Prop :=
  ∀ e, e ∈ tbl → ∀ vs, valuesOf ρ e.args = some vs → ∀ j, j < e.count → ∀ v,
    ρ (e.lo + j) = some v → ∃ rs, Run e.written vs rs ∧ rs[j]? = some v

/-- A result of an entry has a value only when its operands have. -/
def Closed (ρ : Valuation Val) (tbl : Table Raw) : Prop :=
  ∀ e, e ∈ tbl → ∀ j, j < e.count → ρ (e.lo + j) ≠ none → ∀ a, a ∈ e.args → ρ a ≠ none

/-- Entries, the latest first, are well formed below `n`: every entry's operands are below its
results, the results of every entry are below those of every later one, and all are below
`n`. -/
def EntriesWF : Nat → List (Entry Raw) → Prop
  | _, [] => True
  | n, e :: es => (∀ a, a ∈ e.args → a < e.lo) ∧ e.lo + e.count ≤ n ∧ EntriesWF e.lo es

/-- The table is well formed below `n`: its entries are. -/
def Table.WF (n : Nat) (tbl : Table Raw) : Prop := EntriesWF n tbl.entries

/-- The state and a valuation agree: nothing from the next identifier on has a value, the table
is well formed and true, and every value is valid. -/
structure Coherent {T : Type} (Run : Raw → List Val → List Val → Prop) (Valid : Val → Prop)
    (ρ : Valuation Val) (st : St T Raw) : Prop where
  support : Support st.next ρ
  wf : Table.WF st.next st.table
  consistent : Consistent Run ρ st.table
  closed : Closed ρ st.table
  valid : ∀ i v, ρ i = some v → Valid v

/-- A state grew from another: identifiers were made and entries added above the old ones. -/
structure St.Grows {T : Type} (st st' : St T Raw) : Prop where
  next : st.next ≤ st'.next
  table : ∃ new, st'.table.entries = new ++ st.table.entries ∧ ∀ e, e ∈ new → st.next ≤ e.lo

/-- One step of the walk, of a valuation and a state: the valuation grew and agrees with the
state, which grew and has the same refusals and bounds. -/
structure Stepped {T : Type} (Run : Raw → List Val → List Val → Prop) (Valid : Val → Prop)
    (ρ ρ' : Valuation Val) (st st' : St T Raw) : Prop where
  le : ρ.Le ρ'
  coherent : Coherent Run Valid ρ' st'
  grows : St.Grows st st'
  refusals : st'.refusals = st.refusals
  bounds : st'.bounds = st.bounds

end

/-! ## The laws of what the check knows of operations -/

section
variable {Val : Type} {Raw : Type}

/-- How a value reads, by the form of the operation that gave it, from its operands. -/
def FormHolds (R : Reading Val) : ResultForm → List Val → Val → Prop
  | .sum, args, r => ∃ a b x y, args = [a, b] ∧ R.nat a = some x ∧ R.nat b = some y ∧
      R.nat r = some (x + y)
  | .difference, args, r => ∃ a b x y, args = [a, b] ∧ R.nat a = some x ∧ R.nat b = some y ∧
      y ≤ x ∧ R.nat r = some (x - y)
  | .less, args, r => ∃ a b x y, args = [a, b] ∧ R.nat a = some x ∧ R.nat b = some y ∧
      R.bool r = some (decide (x < y))
  | .equal, args, r => ∃ a b x y, args = [a, b] ∧ R.nat a = some x ∧ R.nat b = some y ∧
      R.bool r = some (decide (x = y))
  | .negation, args, r => ∃ a x, args = [a] ∧ R.bool a = some x ∧ R.bool r = some (!x)
  | .conjunction, args, r => ∃ a b x y, args = [a, b] ∧ R.bool a = some x ∧
      R.bool b = some y ∧ R.bool r = some (x && y)
  | .disjunction, args, r => ∃ a b x y, args = [a, b] ∧ R.bool a = some x ∧
      R.bool b = some y ∧ R.bool r = some (x || y)
  | .truth value, _, r => R.bool r = some value

/-- What `OpFacts` says of written operations is true of a relation from a written operation and
its operands' values to its results' values: the relation is a function; the first result reads
by the form; the ranges of the results hold where those of the operands do. -/
structure OpFacts.Lawful (ops : OpFacts Raw) (R : Reading Val)
    (Run : Raw → List Val → List Val → Prop) : Prop where
  functional : ∀ w args rs rs', Run w args rs → Run w args rs' → rs = rs'
  form : ∀ w args rs f, ops.form w = some f → Run w args rs →
    ∃ r, rs.head? = some r ∧ FormHolds R f args r
  ranges : ∀ w args rs (known : List (Option Range)), Run w args rs →
    (∀ (i : Nat) (r : Range), known[i]? = some (some r) →
      ∃ v n, args[i]? = some v ∧ R.nat v = some n ∧ r.Has n) →
    ∀ (i : Nat) (r : Range), (ops.ranges w known)[i]? = some (some r) →
      ∃ v n, rs[i]? = some v ∧ R.nat v = some n ∧ r.Has n

/-! ## What a requirement says -/

/-- The value that an operand of a requirement names, among the operands' values. -/
def _root_.Zkc.Core.Operand.Denotes (Run : Raw → List Val → List Val → Prop) (args : List Val) :
    Operand Raw → Val → Prop
  | .arg position, v => args[position]? = some v
  | .apply written positions, v => ∃ operands rs, atPositions args positions = some operands ∧
      Run written operands rs ∧ rs.head? = some v

/-- The values that operands name, in order. -/
def DenotesAll (Run : Raw → List Val → List Val → Prop) (args : List Val) :
    List (Operand Raw) → List Val → Prop
  | [], [] => True
  | o :: os, v :: vs => Operand.Denotes Run args o v ∧ DenotesAll Run args os vs
  | _, _ => False

/-- What a requirement says of the values it names: an order, a bound, a number, a truth
value. -/
def _root_.Zkc.Core.Requirement.Relation (R : Reading Val) : Requirement Raw → List Val → Prop
  | .le .., [a, b] => ∀ x y, R.nat a = some x → R.nat b = some y → x ≤ y
  | .lt .., [a, b] => ∀ x y, R.nat a = some x → R.nat b = some y → x < y
  | .atLeast _ n, [a] => ∀ x, R.nat a = some x → n ≤ x
  | .below _ n, [a] => ∀ x, R.nat a = some x → x < n
  | .exactly _ n, [a] => ∀ x, R.nat a = some x → x = n
  | .difference _ _ n, [b, a] => ∀ x y, R.nat b = some x → R.nat a = some y → x - y = n
  | .holds _, [a] => R.bool a = some true
  | .bounded _, [a] => ∃ x, R.nat a = some x
  | _, _ => False

/-- The identifiers that the operands of a requirement resolve to have, where there is one,
values that the operands name. -/
def OperandsAt (Run : Raw → List Val → List Val → Prop) (args : List Val) (ρ : Valuation Val) :
    List (Operand Raw) → List (Option Nat) → Prop
  | [], [] => True
  | o :: os, i :: is => (∀ id, i = some id → ∃ v, ρ id = some v ∧ o.Denotes Run args v) ∧
      OperandsAt Run args ρ os is
  | _, _ => False

/-- A requirement holds of the operands' values: the values it names are there, and it says
of them what is true. -/
def _root_.Zkc.Core.Requirement.Holds (Run : Raw → List Val → List Val → Prop) (R : Reading Val)
    (args : List Val) (requirement : Requirement Raw) : Prop :=
  ∃ vs, DenotesAll Run args requirement.operands vs ∧ requirement.Relation R vs

end

/-! ## Lemmas -/

section
variable {Val : Type} {Raw : Type}

theorem Valuation.Le.refl (ρ : Valuation Val) : ρ.Le ρ := fun _ _ h => h

theorem Valuation.Le.trans {ρ ρ' ρ'' : Valuation Val} (a : ρ.Le ρ') (b : ρ'.Le ρ'') :
    ρ.Le ρ'' :=
  fun i v h => b i v (a i v h)

theorem Support.mono {ρ : Valuation Val} {n n' : Nat} (h : n ≤ n') (hs : Support n ρ) :
    Support n' ρ := fun i hi => hs i (by omega)

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
  choices c m := by
    obtain ⟨valued, imp⟩ := hk.choices c m
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp valued
    refine ⟨by rw [h _ _ hv]; simp, fun b hb e => ?_⟩
    have hb' : BoolAt R ρ c.result b := by
      obtain ⟨w, hw, hwb⟩ := hb
      rw [h _ _ hv] at hw
      cases hw
      exact ⟨v, hv, hwb⟩
    exact ⟨(imp b hb' e).1.le h, (imp b hb' e).2.le h⟩

/-! ### Lists of values -/

theorem valuesOf_congr {ρ ρ' : Valuation Val} :
    ∀ {ids : List Nat}, (∀ i, i ∈ ids → ρ i = ρ' i) → valuesOf ρ ids = valuesOf ρ' ids
  | [], _ => rfl
  | i :: is, h => by
      simp only [valuesOf]
      rw [h i List.mem_cons_self,
        valuesOf_congr (fun j hj => h j (List.mem_cons_of_mem _ hj))]

theorem valuesOf_length {ρ : Valuation Val} :
    ∀ {ids : List Nat} {vs : List Val}, valuesOf ρ ids = some vs → vs.length = ids.length
  | [], vs, h => by simp only [valuesOf, Option.some.injEq] at h; subst h; rfl
  | i :: is, vs, h => by
      simp only [valuesOf] at h
      split at h
      · next v vs' _ e2 =>
          cases h
          simp [valuesOf_length e2]
      · cases h

theorem valuesOf_get {ρ : Valuation Val} :
    ∀ {ids : List Nat} {vs : List Val}, valuesOf ρ ids = some vs →
      ∀ j, j < ids.length → ρ (ids.getD j 0) = vs[j]?
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | i :: is, vs, h, j, hj => by
      simp only [valuesOf] at h
      split at h
      · next v vs' e1 e2 =>
          cases h
          cases j with
          | zero => simpa using e1
          | succ j =>
              simp only [List.getD_cons_succ, List.getElem?_cons_succ]
              exact valuesOf_get e2 j (by simp at hj; omega)
      · cases h

theorem valuesOf_getElem {ρ : Valuation Val} {ids : List Nat} {vs : List Val}
    (h : valuesOf ρ ids = some vs) {j i : Nat} (hj : ids[j]? = some i) : ρ i = vs[j]? := by
  have lt : j < ids.length := by
    rcases List.getElem?_eq_some_iff.mp hj with ⟨lt, _⟩
    exact lt
  have := valuesOf_get h j lt
  rw [List.getD_eq_getElem?_getD, hj] at this
  exact this

theorem valuesOf_of_get {ρ : Valuation Val} :
    ∀ {ids : List Nat} {vs : List Val}, vs.length = ids.length →
      (∀ j, j < ids.length → ρ (ids.getD j 0) = vs[j]?) → valuesOf ρ ids = some vs
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => absurd h (fun h => Nat.succ_ne_zero _ h)
  | _ :: _, [], h, _ => absurd h (fun h => Nat.succ_ne_zero _ h.symm)
  | i :: is, v :: vs, hl, h => by
      have h0 := h 0 (by simp)
      simp only [List.getD_cons_zero, List.getElem?_cons_zero] at h0
      have hr : valuesOf ρ is = some vs :=
        valuesOf_of_get (by simpa using hl) (fun j hj => by
          have := h (j + 1) (by simp; omega)
          simpa using this)
      simp [valuesOf, h0, hr]

/-- Identifiers with values have them in every larger valuation. -/
theorem valuesOf_le {ρ ρ' : Valuation Val} (h : ρ.Le ρ') :
    ∀ {ids : List Nat} {vs : List Val}, valuesOf ρ ids = some vs → valuesOf ρ' ids = some vs
  | [], _, e => e
  | i :: is, vs, e => by
      simp only [valuesOf] at e
      split at e
      · next v vs' e1 e2 =>
          cases e
          simp [valuesOf, h i v e1, valuesOf_le h e2]
      · cases e

theorem valuesOf_mem {ρ : Valuation Val} :
    ∀ {ids : List Nat} {vs : List Val}, valuesOf ρ ids = some vs → ∀ i, i ∈ ids → ρ i ≠ none
  | [], _, _, _, h => nomatch h
  | j :: is, vs, e, i, h => by
      simp only [valuesOf] at e
      split at e
      · next v vs' e1 e2 =>
          rcases List.mem_cons.mp h with rfl | h
          · rw [e1]; simp
          · exact valuesOf_mem e2 i h
      · cases e

theorem valuesOf_of_mem {ρ : Valuation Val} :
    ∀ {ids : List Nat}, (∀ i, i ∈ ids → ρ i ≠ none) → ∃ vs, valuesOf ρ ids = some vs
  | [], _ => ⟨[], rfl⟩
  | i :: is, h => by
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (h i List.mem_cons_self)
      obtain ⟨vs, hvs⟩ := valuesOf_of_mem (ρ := ρ) (fun j hj => h j (List.mem_cons_of_mem _ hj))
      exact ⟨v :: vs, by simp [valuesOf, hv, hvs]⟩

/-- The items at positions, of the values of identifiers, are the values of the identifiers
at those positions. -/
theorem atPositions_valuesOf {ρ : Valuation Val} {ids : List Nat} {vs : List Val}
    (h : valuesOf ρ ids = some vs) :
    ∀ {positions : List Nat} {chosen : List Nat}, atPositions ids positions = some chosen →
      ∃ values, atPositions vs positions = some values ∧ valuesOf ρ chosen = some values
  | [], chosen, e => by
      simp only [atPositions, Option.some.injEq] at e
      subst e
      exact ⟨[], rfl, rfl⟩
  | p :: ps, chosen, e => by
      simp only [atPositions] at e
      split at e
      · next i rest e1 e2 =>
          cases e
          obtain ⟨values, hv, hl⟩ := atPositions_valuesOf h e2
          have hi := valuesOf_getElem h e1
          cases hvp : vs[p]? with
          | none => rw [hvp] at hi; exact absurd (valuesOf_mem h i (List.mem_of_getElem? e1)) (by
              rw [hi]; simp)
          | some v =>
              rw [hvp] at hi
              exact ⟨v :: values, by simp [atPositions, hvp, hv], by simp [valuesOf, hi, hl]⟩
      · cases e

/-! ### Growing valuations -/

theorem setFrom_le {ρ : Valuation Val} {lo : Nat} (hs : Support lo ρ) (vs : List Val) :
    ρ.Le (ρ.setFrom lo vs) := fun i v h => by
  simp only [Valuation.setFrom]
  rw [ite_eq_right (by intro hi; rw [hs i hi.1] at h; cases h)]
  exact h

theorem setFrom_at (ρ : Valuation Val) (lo : Nat) (vs : List Val) (j : Nat)
    (hj : j < vs.length) : ρ.setFrom lo vs (lo + j) = vs[j]? := by
  simp only [Valuation.setFrom]
  rw [ite_eq_left ⟨by omega, by omega⟩]
  simp

theorem setFrom_low (ρ : Valuation Val) (lo : Nat) (vs : List Val) {i : Nat} (hi : i < lo) :
    ρ.setFrom lo vs i = ρ i := by
  simp only [Valuation.setFrom]
  rw [ite_eq_right (by omega)]

theorem setFrom_support {ρ : Valuation Val} {lo : Nat} (hs : Support lo ρ) (vs : List Val) :
    Support (lo + vs.length) (ρ.setFrom lo vs) := fun i hi => by
  simp only [Valuation.setFrom]
  rw [ite_eq_right (by omega)]
  exact hs i (by omega)

theorem valuesOf_setFrom (ρ : Valuation Val) (lo : Nat) (vs : List Val) :
    valuesOf (ρ.setFrom lo vs) (List.range' lo vs.length) = some vs := by
  apply valuesOf_of_get (by simp)
  intro j hj
  simp only [List.length_range'] at hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_range' hj]
  simp only [Option.getD_some, Nat.one_mul]
  rw [setFrom_at _ _ _ _ hj]

theorem below_le {ρ ρ' : Valuation Val} {t : Nat} (hs : Support t ρ) (h : ρ.Le ρ') :
    ρ.Le (ρ'.below t) := fun i v e => by
  simp only [Valuation.below]
  by_cases hi : i < t
  · rw [ite_eq_left hi]; exact h i v e
  · rw [hs i (by omega)] at e; cases e

theorem below_support (ρ : Valuation Val) (t : Nat) : Support t (ρ.below t) := fun i hi => by
  simp only [Valuation.below]
  rw [ite_eq_right (by omega)]

theorem below_eq {ρ : Valuation Val} {t i : Nat} (hi : i < t) : ρ.below t i = ρ i := by
  simp only [Valuation.below]
  rw [ite_eq_left hi]

theorem below_self_le (ρ : Valuation Val) (t : Nat) : (ρ.below t).Le ρ := fun i v e => by
  simp only [Valuation.below] at e
  split at e
  · exact e
  · cases e

theorem fill_le (ρ : Valuation Val) (lo : Nat) (vs : List Val) : ρ.Le (ρ.fill lo vs) :=
  fun i v h => by simp only [Valuation.fill, h]

theorem fill_other {ρ : Valuation Val} {lo : Nat} {vs : List Val} {i : Nat}
    (hi : ¬ (lo ≤ i ∧ i < lo + vs.length)) : ρ.fill lo vs i = ρ i := by
  simp only [Valuation.fill]
  cases ρ i with
  | some v => rfl
  | none => simp only; rw [ite_eq_right hi]

/-! ### The table -/

theorem EntriesWF.mono {n n' : Nat} (h : n ≤ n') :
    ∀ {es : List (Entry Raw)}, EntriesWF n es → EntriesWF n' es
  | [], _ => trivial
  | _ :: _, ⟨h1, h2, h3⟩ => ⟨h1, Nat.le_trans h2 h, h3⟩

theorem EntriesWF.mem : ∀ {n : Nat} {es : List (Entry Raw)} {e : Entry Raw}, EntriesWF n es →
    e ∈ es → (∀ a, a ∈ e.args → a < e.lo) ∧ e.lo + e.count ≤ n
  | _, [], _, _, h => nomatch h
  | n, e' :: es, e, ⟨h1, h2, h3⟩, h => by
      cases h with
      | head => exact ⟨h1, h2⟩
      | tail _ h =>
          obtain ⟨a1, a2⟩ := EntriesWF.mem h3 h
          exact ⟨a1, Nat.le_trans a2 (Nat.le_trans (Nat.le_add_right _ _) h2)⟩

theorem EntriesWF.disjoint : ∀ {n : Nat} {es : List (Entry Raw)} {e e' : Entry Raw},
    EntriesWF n es → e ∈ es → e' ∈ es →
      ∀ j j', j < e.count → j' < e'.count → e.lo + j = e'.lo + j' → e = e'
  | _, [], _, _, _, h, _, _, _, _, _, _ => nomatch h
  | _, _ :: _, _, _, ⟨_, _, h3⟩, h, h', j, j', hj, hj', eq => by
      cases h with
      | head =>
          cases h' with
          | head => rfl
          | tail _ h' =>
              have := (EntriesWF.mem h3 h').2
              exfalso
              omega
      | tail _ h =>
          cases h' with
          | head =>
              have := (EntriesWF.mem h3 h).2
              exfalso
              omega
          | tail _ h' => exact EntriesWF.disjoint h3 h h' j j' hj hj' eq

theorem Table.WF.mono {n n' : Nat} (h : n ≤ n') {tbl : Table Raw} (wf : Table.WF n tbl) :
    Table.WF n' tbl :=
  EntriesWF.mono h wf

theorem Table.WF.mem {n : Nat} {tbl : Table Raw} {e : Entry Raw} (wf : Table.WF n tbl)
    (m : e ∈ tbl) : (∀ a, a ∈ e.args → a < e.lo) ∧ e.lo + e.count ≤ n :=
  EntriesWF.mem wf m

/-- Two entries of a well-formed table have disjoint results. -/
theorem Table.WF.disjoint {n : Nat} {tbl : Table Raw} {e e' : Entry Raw} (wf : Table.WF n tbl)
    (m : e ∈ tbl) (m' : e' ∈ tbl) :
    ∀ j j', j < e.count → j' < e'.count → e.lo + j = e'.lo + j' → e = e' :=
  EntriesWF.disjoint wf m m'

/-- Entries above the support have no values: a table that grows by them stays true. -/
theorem consistent_extend {Run : Raw → List Val → List Val → Prop} {ρ : Valuation Val}
    {tbl : Table Raw} {n : Nat} (hs : Support n ρ) (hc : Consistent Run ρ tbl) (hd : Closed ρ tbl)
    {tbl' : Table Raw} {new : List (Entry Raw)} (enew : tbl'.entries = new ++ tbl.entries)
    (hnew : ∀ e, e ∈ new → n ≤ e.lo) :
    Consistent Run ρ tbl' ∧ Closed ρ tbl' := by
  constructor
  · intro e he vs hvs j hj v hv
    rcases List.mem_append.mp (enew ▸ he : e ∈ new ++ tbl.entries) with h | h
    · rw [hs _ (by have := hnew e h; omega)] at hv; cases hv
    · exact hc e h vs hvs j hj v hv
  · intro e he j hj hv
    rcases List.mem_append.mp (enew ▸ he : e ∈ new ++ tbl.entries) with h | h
    · exact absurd (hs _ (by have := hnew e h; omega)) hv
    · exact hd e h j hj hv

/-- Values set above a well-formed table change no entry. -/
theorem consistent_setFrom {Run : Raw → List Val → List Val → Prop} {ρ : Valuation Val}
    {tbl : Table Raw} {lo : Nat} (wf : Table.WF lo tbl) (hc : Consistent Run ρ tbl)
    (hd : Closed ρ tbl) (vs : List Val) :
    Consistent Run (ρ.setFrom lo vs) tbl ∧ Closed (ρ.setFrom lo vs) tbl := by
  have low : ∀ e, e ∈ tbl → (∀ a, a ∈ e.args → ρ.setFrom lo vs a = ρ a) ∧
      ∀ j, j < e.count → ρ.setFrom lo vs (e.lo + j) = ρ (e.lo + j) := fun e he => by
    obtain ⟨h1, h2⟩ := wf.mem he
    exact ⟨fun a ha => setFrom_low _ _ _ (by have := h1 a ha; omega),
      fun j hj => setFrom_low _ _ _ (by omega)⟩
  constructor
  · intro e he vsa hvs j hj v hv
    rw [valuesOf_congr (fun a ha => (low e he).1 a ha)] at hvs
    rw [(low e he).2 j hj] at hv
    exact hc e he vsa hvs j hj v hv
  · intro e he j hj hv a ha
    rw [(low e he).2 j hj] at hv
    rw [(low e he).1 a ha]
    exact hd e he j hj hv a ha

/-- The valuation below `t` keeps the entries below `t`, and has no value for the others. -/
theorem consistent_below {Run : Raw → List Val → List Val → Prop} {ρ : Valuation Val}
    {tbl : Table Raw} {t : Nat} (split : ∀ e, e ∈ tbl → e.lo + e.count ≤ t ∨ t ≤ e.lo)
    (args : ∀ e, e ∈ tbl → ∀ a, a ∈ e.args → a < e.lo) (hc : Consistent Run ρ tbl)
    (hd : Closed ρ tbl) : Consistent Run (ρ.below t) tbl ∧ Closed (ρ.below t) tbl := by
  constructor
  · intro e he vs hvs j hj v hv
    rcases split e he with low | high
    · rw [valuesOf_congr (fun a ha => below_eq (by have := args e he a ha; omega))] at hvs
      rw [below_eq (by omega)] at hv
      exact hc e he vs hvs j hj v hv
    · rw [below_support ρ t _ (by omega)] at hv; cases hv
  · intro e he j hj hv a ha
    rcases split e he with low | high
    · rw [below_eq (by omega)] at hv
      rw [below_eq (by have := args e he a ha; omega)]
      exact hd e he j hj hv a ha
    · exact absurd (below_support ρ t _ (by omega)) hv

/-- An application of the operation of an entry at the values of its operands, which gives
`rs`: the results keep the values they have, which are those of `rs` because the operation is a
function of its operands, and get those of `rs` otherwise. The table stays true. -/
theorem fill_entry {Run : Raw → List Val → List Val → Prop} {ρ : Valuation Val}
    {tbl : Table Raw} {n : Nat} (wf : Table.WF n tbl) (hc : Consistent Run ρ tbl)
    (hcl : Closed ρ tbl) (hs : Support n ρ) {e : Entry Raw} (he : e ∈ tbl) {vs rs : List Val}
    (hvs : valuesOf ρ e.args = some vs) (hrun : Run e.written vs rs) (hlen : rs.length = e.count)
    (hfun : ∀ rs', Run e.written vs rs' → rs' = rs) :
    ρ.Le (ρ.fill e.lo rs) ∧ Support n (ρ.fill e.lo rs) ∧
      Consistent Run (ρ.fill e.lo rs) tbl ∧ Closed (ρ.fill e.lo rs) tbl ∧
      valuesOf (ρ.fill e.lo rs) (List.range' e.lo e.count) = some rs := by
  have le := fill_le ρ e.lo rs
  have hb := (wf.mem he).2
  have at_ : ∀ j, j < e.count → ρ.fill e.lo rs (e.lo + j) = rs[j]? := fun j hj => by
    cases hv : ρ (e.lo + j) with
    | some v =>
        obtain ⟨rs0, hr0, ho0⟩ := hc e he vs hvs j hj v hv
        rw [hfun rs0 hr0] at ho0
        rw [le _ _ hv, ho0]
    | none =>
        simp only [Valuation.fill, hv]
        rw [ite_eq_left ⟨by omega, by omega⟩]
        simp
  have other : ∀ e', e' ∈ tbl → e' ≠ e → ∀ j, j < e'.count →
      ρ.fill e.lo rs (e'.lo + j) = ρ (e'.lo + j) := fun e' he' hne j hj => by
    apply fill_other
    intro hin
    exact hne (Table.WF.disjoint wf he' he j (e'.lo + j - e.lo) hj (by omega) (by omega))
  have hargs : valuesOf (ρ.fill e.lo rs) e.args = some vs := valuesOf_le le hvs
  refine ⟨le, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hs i hi
    rw [fill_other (by omega)]
    exact this
  · intro e' he' vs' hvs' j hj v hv
    by_cases hin : e.lo ≤ e'.lo + j ∧ e'.lo + j < e.lo + e.count
    · have heq := Table.WF.disjoint wf he' he j (e'.lo + j - e.lo) hj (by omega) (by omega)
      subst heq
      rw [hargs] at hvs'
      cases hvs'
      rw [at_ j hj] at hv
      exact ⟨rs, hrun, hv⟩
    · have hne : e' ≠ e := fun h => by subst h; exact hin ⟨by omega, by omega⟩
      rw [other e' he' hne j hj] at hv
      obtain ⟨vs0, hvs0⟩ := valuesOf_of_mem (ρ := ρ) (hcl e' he' j hj (by rw [hv]; simp))
      rw [valuesOf_le le hvs0] at hvs'
      cases hvs'
      exact hc e' he' _ hvs0 j hj v hv
  · intro e' he' j hj hv a ha
    by_cases hin : e.lo ≤ e'.lo + j ∧ e'.lo + j < e.lo + e.count
    · have heq := Table.WF.disjoint wf he' he j (e'.lo + j - e.lo) hj (by omega) (by omega)
      subst heq
      exact valuesOf_mem hargs a ha
    · have hne : e' ≠ e := fun h => by subst h; exact hin ⟨by omega, by omega⟩
      rw [other e' he' hne j hj] at hv
      have := hcl e' he' j hj hv a ha
      intro h0
      apply this
      cases hρ : ρ a with
      | none => rfl
      | some v => rw [le _ _ hρ] at h0; cases h0
  · apply valuesOf_of_get (by simp [hlen])
    intro j hj
    simp only [List.length_range'] at hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_range' hj]
    simp only [Option.getD_some, Nat.one_mul]
    exact at_ j hj

theorem findIn_spec [DecidableEq Raw] {w : Raw} {args : List Nat} {count lo : Nat} :
    ∀ {es : List (Entry Raw)}, findIn w args count es = some lo →
      ∃ e, e ∈ es ∧ e.written = w ∧ e.args = args ∧ e.count = count ∧ e.lo = lo
  | [], h => by simp [findIn] at h
  | e :: es, h => by
      simp only [findIn] at h
      split at h
      · next hr =>
          cases h
          exact ⟨e, List.mem_cons_self, hr.2.2, hr.1, hr.2.1, rfl⟩
      · obtain ⟨e', m, r⟩ := findIn_spec h
        exact ⟨e', List.mem_cons_of_mem _ m, r⟩

theorem Table.find_spec [DecidableEq Raw] {w : Raw} {args : List Nat} {count lo : Nat}
    {tbl : Table Raw} (h : tbl.find w args count = some lo) :
    ∃ e, e ∈ tbl ∧ e.written = w ∧ e.args = args ∧ e.count = count ∧ e.lo = lo := by
  obtain ⟨e, m, r⟩ := findIn_spec h
  exact ⟨e, tbl.applications e (BitTree.mem_of_find _ _ _ e m), r⟩

theorem entryIn_spec {id : Nat} : ∀ {es : List (Entry Raw)} {e : Entry Raw},
    entryIn id es = some e → e ∈ es ∧ e.lo ≤ id ∧ id < e.lo + e.count
  | [], _, h => by simp [entryIn] at h
  | e' :: es, e, h => by
      simp only [entryIn] at h
      split at h
      · next hr =>
          cases h
          exact ⟨List.mem_cons_self, hr⟩
      · obtain ⟨m, r⟩ := entryIn_spec h
        exact ⟨List.mem_cons_of_mem _ m, r⟩

theorem Table.entryOf_spec {id : Nat} {tbl : Table Raw} {e : Entry Raw}
    (h : tbl.entryOf id = some e) : e ∈ tbl ∧ e.lo ≤ id ∧ id < e.lo + e.count := by
  obtain ⟨m, r⟩ := entryIn_spec h
  exact ⟨tbl.results e (BitTree.mem_of_find _ _ _ e m), r⟩

/-- An identifier that reads by a form is the first result of an entry of that form. -/
theorem Table.formOf_spec {ops : OpFacts Raw} {tbl : Table Raw} {id : Nat} {f : ResultForm}
    {args : List Nat} (h : tbl.formOf ops id = some (f, args)) :
    ∃ e, e ∈ tbl ∧ e.lo = id ∧ 0 < e.count ∧ ops.form e.written = some f ∧ e.args = args := by
  simp only [Table.formOf] at h
  split at h
  · next e he =>
      obtain ⟨m, lo, hi⟩ := Table.entryOf_spec he
      split at h
      · next same =>
          cases hf : ops.form e.written with
          | none => rw [hf] at h; cases h
          | some f' =>
              rw [hf] at h
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨e, m, same, by omega, hf, rfl⟩
      · cases h
  · cases h

end

end FactCheck

end Zkc.Core
