module

public import Zkc.Core.Value.Table
public import Zkc.Core.Program.Library

@[expose] public section

/-!
Valuations of identifiers, what the table says of one, and how the state grows.

A run gives identifiers values: a valuation, partial, that grows along the run. An identifier
has a value once a variable of the run has held it, and keeps it. The operations are a relation
`Run` from a written form and the values of its operands to the values of its results. Of a
valuation, the table says that where a result of an entry has a value, its operands have values
and the operation applied to them gives the results (`Consistent`, `Closed`). A state and a
valuation agree when, besides, nothing from the next identifier on has a value, the table is well
formed (`Table.WF`: every entry's operands below its results, and its results below those of
every later entry and the next identifier) and every value is valid (`Coherent`).

A state grows (`St.Grows`) when identifiers are made and entries added above the old ones. New
identifiers (`fresh`) and an application shared (`share`) grow the state and keep its table well
formed (`fresh_grows`, `share_grows`), and the names of a binding bound to identifiers below the
next keep every name in scope with an identifier below the next (`InScope`).
-/

namespace Zkc.Core

namespace FactCheck

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

end

/-! ## The identifiers of the names in scope -/

section
variable {α : Type}

/-- Every name in scope has an identifier below `next`. -/
def InScope (Γ : Ctx α) (ids : Ctx Nat) (next : Nat) : Prop :=
  ∀ name a, Γ.find? name = some a → ∃ i, ids.find? name = some i ∧ i < next

theorem InScope.mono {Γ : Ctx α} {ids : Ctx Nat} {next next' : Nat} (h : InScope Γ ids next)
    (le : next ≤ next') : InScope Γ ids next' := fun name a found => by
  obtain ⟨i, hi, lt⟩ := h name a found
  exact ⟨i, hi, Nat.lt_of_lt_of_le lt le⟩

/-- A name bound to an identifier below `next` keeps every name in scope with one. -/
theorem InScope.insert {Γ : Ctx α} {ids : Ctx Nat} {next : Nat} (h : InScope Γ ids next)
    (bound : Name) (a : α) {i : Nat} (lt : i < next) :
    InScope (Γ.insert bound a) (ids.insert bound i) next := fun name b found => by
  rw [Ctx.find?_insert] at found
  rw [Ctx.find?_insert]
  by_cases same : name = bound
  · exact ⟨i, by simp [same], lt⟩
  · simp only [same, ↓reduceIte] at found ⊢
    exact h name b found

/-- The names of a binding bound to as many identifiers below `next` keep every name in scope
with one. -/
theorem InScope.bind {next : Nat} : ∀ {Γ : Ctx α} {ids : Ctx Nat} {types : List α}
    (names : Names types) (made : List Nat), InScope Γ ids next →
    made.length = types.length → (∀ i, i ∈ made → i < next) →
    InScope (Γ.extend names) (bindIds ids names made) next
  | _, _, [], .nil, _, h, _, _ => h
  | _, _, _ :: _, .cons _ _, [], _, len, _ => nomatch len
  | _, _, _ :: _, .cons name rest, i :: is, h, len, lt =>
      InScope.bind rest is (h.insert name _ (lt i List.mem_cons_self))
        (Nat.succ.inj len) (fun j m => lt j (List.mem_cons_of_mem _ m))

theorem idsOf_lt {Γ : Ctx α} {ids : Ctx Nat} {next : Nat} (h : InScope Γ ids next) :
    ∀ {items : List α} (xs : HList (Var Γ) items) (i : Nat), i ∈ idsOf ids xs → i < next
  | [], .nil, _, m => nomatch m
  | _ :: _, .cons x rest, i, m => by
      simp only [idsOf, List.mem_cons] at m
      rcases m with rfl | m
      · obtain ⟨j, hj, lt⟩ := h x.name _ x.typed
        simp only [idOf, hj, Option.getD_some]
        exact lt
      · exact idsOf_lt h rest i m

end

/-! ## Steps that grow the state -/

section
variable {Raw : Type} [DecidableEq Raw] {T : Type}

omit [DecidableEq Raw] in
theorem St.Grows.refl (st : St T Raw) : St.Grows st st :=
  ⟨Nat.le_refl _, [], rfl, fun _ m => nomatch m⟩

omit [DecidableEq Raw] in
theorem fresh_grows (n : Nat) (st : St T Raw) (wf : Table.WF st.next st.table) :
    Table.WF (fresh n st).2.next (fresh n st).2.table ∧ St.Grows st (fresh n st).2 ∧
      ∀ i, i ∈ (fresh n st).1 → i < (fresh n st).2.next := by
  refine ⟨wf.mono (by simp [fresh]), ⟨by simp [fresh], [], rfl, fun _ m => nomatch m⟩, ?_⟩
  intro i m
  have m := mem_range'_bounds m
  simp only [fresh] at m ⊢
  omega

theorem share_grows (w : Raw) (args : List Nat) (count : Nat) (st : St T Raw)
    (wf : Table.WF st.next st.table) (hlt : ∀ a, a ∈ args → a < st.next) :
    Table.WF (share w args count st).2.next (share w args count st).2.table ∧
      St.Grows st (share w args count st).2 ∧
      ∀ i, i ∈ (share w args count st).1 → i < (share w args count st).2.next := by
  simp only [share]
  split
  · next lo found =>
      obtain ⟨e, m, _, _, ec, el⟩ := Table.find_spec found
      refine ⟨wf, St.Grows.refl st, fun i hi => ?_⟩
      have := (wf.mem m).2
      have hi := mem_range'_bounds hi
      simp only
      omega
  · refine ⟨⟨hlt, Nat.le_refl _, wf⟩, ⟨Nat.le_add_right _ _, [_], rfl, ?_⟩, ?_⟩
    · intro e m
      simp at m
      subst m
      exact Nat.le_refl _
    · intro i hi
      have hi := mem_range'_bounds hi
      simp only
      omega

end

section
variable {Raw : Type}

theorem St.Grows.trans {T : Type} {a b c : St T Raw} (h1 : St.Grows a b) (h2 : St.Grows b c) :
    St.Grows a c := by
  obtain ⟨n1, new1, e1, low1⟩ := h1
  obtain ⟨n2, new2, e2, low2⟩ := h2
  refine ⟨Nat.le_trans n1 n2, new2 ++ new1, by rw [e2, e1, List.append_assoc], ?_⟩
  intro e m
  rcases List.mem_append.mp m with m | m
  · exact Nat.le_trans n1 (low2 e m)
  · exact low1 e m

end

end FactCheck

end Zkc.Core
