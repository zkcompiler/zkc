module

public import Zkc.Core.Facts.State
public import Zkc.Core.Value.Valuation
public import Zkc.Core.Meaning.Requirement

@[expose] public section

/-!
What what is known and the requirements say of a run.

A run gives identifiers values: a valuation (`Value/Valuation.lean`), with what the table says of
it. Of a valuation, what is known says that the region runs, that each range, order, truth value
and shape of a choice holds (`Known.Holds`). The operations are a relation `Run` from a written
form and the values of its operands to the values of its results, and how the check reads a
value (as a natural, as a truth value) is a `Reading`: both are given by the dialect, with the
laws that `OpFacts` satisfies against them (`OpFacts.Lawful`). What a requirement says of values
(`Reading`, `Requirement.Holds`) is in `Meaning/Requirement.lean`; here, the identifiers that the
operands of a requirement resolve to have values that they name (`OperandsAt`). One step of the
walk, of a valuation and a state, grows both and keeps the refusals and the bounds (`Stepped`).
-/

namespace Zkc.Core

namespace FactCheck

section
variable {Val : Type}

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

/-! ## A step of the walk, of a valuation -/

variable {Raw : Type}

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

/-! ## The values that a requirement names, of a valuation -/

/-- The identifiers that the operands of a requirement resolve to have, where there is one,
values that the operands name. -/
def OperandsAt (Run : Raw → List Val → List Val → Prop) (args : List Val) (ρ : Valuation Val) :
    List (Operand Raw) → List (Option Nat) → Prop
  | [], [] => True
  | o :: os, i :: is => (∀ id, i = some id → ∃ v, ρ id = some v ∧ o.Denotes Run args v) ∧
      OperandsAt Run args ρ os is
  | _, _ => False

end

/-! ## Lemmas -/

section
variable {Val : Type} {Raw : Type}

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
