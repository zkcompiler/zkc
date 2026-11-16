module

public import Zkc.Core.Facts.Laws
public import Zkc.Core.Facts.Growth
public import Zkc.Core.Facts.Facts
public import Zkc.Core.Meaning.Validity

@[expose] public section

/-!
The walk of the analysis is sound, for any dialect and any semantics that satisfy the laws of
`FactRules.Lawful` (`Facts/Laws.lean`).

The proof is one induction over the term. Along a run, identifiers get values: a valuation that
grows. At every point that the run reaches, the state of the walk and the valuation agree
(nothing from the next identifier on has a value, the table is true of the valuation), every
name in scope has an identifier whose value is the name's value in the environment (`Agree`),
and what is known holds (`Inv`). A region that does not run is walked all the same: it only adds
entries above the identifiers that have values, which keeps the table true. Each iteration of a
loop starts from the valuation before the loop, with the iteration number and the carried values
set at the leaves of the loop's body.

The facts of the table are about the results of a written operation on valid operands
(`ValidRun`). At every operation the requirements are decided first: where none is refused they
hold of the operands' values, and the applications that they enter in the table get values
(`requirements_sound`, by the law `named`). A shared operation is then entered with its operands
in the table's order; the law `binding` gives the results on the operands in that order, and the
law `defined` that it returns (`value_sound`). An operation kept in order gets new leaves, whose
values are what it returned, valid where its requirements hold (`laws.effect`), and so does an
attempt, at its number and at its results (`laws.begin`, `laws.settle`).
-/

namespace Zkc.Core.Analysis.Facts

open FactCheck

/-- What the soundness of the walk is about: the rules of a dialect and what following decides
for it, a semantics with its permitted replies, how the facts read its values, the relation of
written operations, which values are valid and which stops are `undefined`, the definition and
the role of the places, and the bounds of an annotation. -/
structure Setting (D : Dialect) (Raw : Type) where
  rules : FactRules D Raw
  checks : SkelRules D
  sem : Semantics D
  permitted : ∀ op, sem.S.Reply op → Prop
  R : Reading sem.Dyn
  Run : Raw → List sem.Dyn → List sem.Dyn → Prop
  Valid : sem.Dyn → Prop
  undefined : sem.H → Prop
  definition : Key
  role : Option Role
  F : List (Place × Nat)

namespace Setting
variable {D : Dialect} {Raw : Type} (σ : Setting D Raw)

/-- The relation that the facts of the table are about. -/
abbrev Runs : Raw → List σ.sem.Dyn → List σ.sem.Dyn → Prop := ValidRun σ.sem σ.Run σ.Valid

/-- The laws of the setting. -/
abbrev Lawful : Prop := σ.rules.Lawful σ.sem σ.permitted σ.R σ.Run σ.Valid σ.undefined

/-- Values, each with its type, are valid. -/
def AllValid {items : List D.Ty} (vs : HList σ.sem.Val items) : Prop :=
  ∀ v, v ∈ σ.sem.dyns vs → σ.Valid v

end Setting

/-! ## What the walk has at a point of a run -/

section
variable {D : Dialect} {Raw : Type} (σ : Setting D Raw)

/-- Every name in scope has an identifier, and the valuation of that identifier is the name's
value. -/
def Agree {Γ : Ctx D.Ty} (ρ : Valuation σ.sem.Dyn) (ids : Ctx Nat) (env : Env σ.sem.Val Γ) :
    Prop :=
  ∀ τ (x : Var Γ τ), ∃ i, ids.find? x.name = some i ∧ ρ i = some ⟨τ, env.get x⟩

/-- What the walk has at a point of a run agrees with the run: the state with the valuation, the
identifiers of the names in scope with their values, and what is known holds. -/
structure Inv {Γ : Ctx D.Ty} (ρ : Valuation σ.sem.Dyn) (ids : Ctx Nat) (env : Env σ.sem.Val Γ)
    (k : Known) (st : St D.Ty Raw) : Prop where
  coherent : Coherent σ.Runs σ.Valid ρ st
  agree : Agree σ ρ ids env
  holds : k.Holds σ.R ρ

/-- Where a region returns: the state with the valuation, the identifiers that it returns with
the values, and what is known at its end holds. -/
structure ExitInv (ρ : Valuation σ.sem.Dyn) (e : FactCheck.Exit D.Ty Raw) (st : St D.Ty Raw)
    {outs : List D.Ty} (vs : HList σ.sem.Val outs) : Prop where
  coherent : Coherent σ.Runs σ.Valid ρ st
  rets : valuesOf ρ e.rets = some (σ.sem.dyns vs)
  holds : e.known.Holds σ.R ρ

end

section
variable {D : Dialect} {Raw : Type} {σ : Setting D Raw}

theorem allValid_cons {a : D.Ty} {rest : List D.Ty} {v : σ.sem.Val a} {vs : HList σ.sem.Val rest} :
    σ.AllValid (HList.cons v vs) ↔ σ.Valid ⟨a, v⟩ ∧ σ.AllValid vs := by
  constructor
  · intro h
    exact ⟨h _ List.mem_cons_self, fun d m => h d (List.mem_cons_of_mem _ m)⟩
  · intro h d m
    rcases List.mem_cons.mp m with rfl | m
    · exact h.1
    · exact h.2 d m

theorem allValid_append {as bs : List D.Ty} (xs : HList σ.sem.Val as) (ys : HList σ.sem.Val bs) :
    σ.AllValid (xs.append ys) ↔ σ.AllValid xs ∧ σ.AllValid ys := by
  unfold Setting.AllValid
  rw [Semantics.dyns_append]
  constructor
  · intro h
    exact ⟨fun d m => h d (List.mem_append_left _ m), fun d m => h d (List.mem_append_right _ m)⟩
  · intro h d m
    rcases List.mem_append.mp m with m | m
    · exact h.1 d m
    · exact h.2 d m

/-! ## Agreement -/

theorem Agree.le {Γ : Ctx D.Ty} {ρ ρ' : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} (h : Agree σ ρ ids env) (le : ρ.Le ρ') : Agree σ ρ' ids env :=
  fun τ x => by
    obtain ⟨i, hi, hv⟩ := h τ x
    exact ⟨i, hi, le _ _ hv⟩

/-- The identifier of a variable has its value. -/
theorem Agree.idOf {Γ : Ctx D.Ty} {ρ : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} (h : Agree σ ρ ids env) {τ : D.Ty} (x : Var Γ τ) :
    ρ (FactCheck.idOf ids x.name) = some ⟨τ, env.get x⟩ := by
  obtain ⟨i, hi, hv⟩ := h τ x
  simp only [FactCheck.idOf, hi, Option.getD_some]
  exact hv

/-- Where nothing from `n` on has a value, every name in scope has an identifier below `n`. -/
theorem Agree.inScope {Γ : Ctx D.Ty} {ρ : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} (h : Agree σ ρ ids env) {n : Nat} (support : Support n ρ) :
    InScope Γ ids n := fun name τ found => by
  obtain ⟨i, hi, hv⟩ := h τ ⟨name, found⟩
  refine ⟨i, hi, Nat.lt_of_not_le fun le => ?_⟩
  rw [support i le] at hv
  cases hv

theorem valuesOf_idsOf {Γ : Ctx D.Ty} {ρ : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} (h : Agree σ ρ ids env) :
    ∀ {items : List D.Ty} (xs : HList (Var Γ) items),
      valuesOf ρ (idsOf ids xs) = some (σ.sem.dyns (env.all xs))
  | [], .nil => rfl
  | _ :: _, .cons x rest => by
      simp only [idsOf, valuesOf, h.idOf x, valuesOf_idsOf h rest, Env.all, Semantics.dyns]

/-- A name bound to an identifier that has the value bound keeps the agreement. -/
theorem agree_insert {Γ : Ctx D.Ty} {ρ : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} (h : Agree σ ρ ids env) (bound : Name) {τ : D.Ty} (v : σ.sem.Val τ)
    {i : Nat} (hi : ρ i = some ⟨τ, v⟩) : Agree σ ρ (ids.insert bound i) (env.insert bound v) := by
  intro τ' x
  obtain ⟨name, found⟩ := x
  have look := found
  rw [Ctx.find?_insert] at look
  by_cases same : name = bound
  · subst same
    rw [ite_eq_left rfl] at look
    cases look
    refine ⟨i, by rw [Ctx.find?_insert, ite_eq_left rfl], ?_⟩
    show ρ i = some ⟨τ, env.insert name v name τ found⟩
    rw [eq_of_heq (Env.insert_at_bound env name v rfl found)]
    exact hi
  · rw [ite_eq_right same] at look
    obtain ⟨j, hj, hv⟩ := h τ' ⟨name, look⟩
    refine ⟨j, by rw [Ctx.find?_insert, ite_eq_right same]; exact hj, ?_⟩
    show ρ j = some ⟨τ', env.insert bound v name τ' found⟩
    rw [Env.insert_at_other env bound v same]
    exact hv

/-- The names of a binding bound to identifiers that have the values bound keep the agreement:
the invariant of the walk goes along `Env.extend`, a later name hiding an earlier one in both. -/
theorem agree_extend {ρ : Valuation σ.sem.Dyn} : ∀ {Γ : Ctx D.Ty} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} {res : List D.Ty} (names : Names res) (vs : HList σ.sem.Val res)
    (made : List Nat), Agree σ ρ ids env → valuesOf ρ made = some (σ.sem.dyns vs) →
      Agree σ ρ (bindIds ids names made) (env.extend names vs)
  | _, _, _, [], .nil, .nil, _, h, _ => h
  | _, _, _, _ :: _, .cons _ _, .cons _ _, [], _, hr => by
      simp [valuesOf, Semantics.dyns] at hr
  | _, _, _, _ :: _, .cons name rest, .cons v vs, r :: made, h, hr => by
      simp only [valuesOf, Semantics.dyns] at hr
      split at hr
      · next d ds' e1 e2 =>
          simp only [Option.some.injEq, List.cons.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact agree_extend rest vs made (agree_insert h name v e1) e2
      · cases hr

theorem agree_valid {Γ : Ctx D.Ty} {ρ : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} (h : Agree σ ρ ids env) (valid : ∀ i v, ρ i = some v → σ.Valid v) :
    ∀ τ (x : Var Γ τ), σ.Valid ⟨τ, env.get x⟩ := fun τ x => by
  obtain ⟨i, _, hv⟩ := h τ x
  exact valid _ _ hv

/-- Values that identifiers have are valid when every value is. -/
theorem allValid_of_valuesOf {ρ : Valuation σ.sem.Dyn} {made : List Nat} {items : List D.Ty}
    {vs : HList σ.sem.Val items} (look : valuesOf ρ made = some (σ.sem.dyns vs))
    (valid : ∀ i v, ρ i = some v → σ.Valid v) : σ.AllValid vs :=
  valuesOf_valid look valid

/-! ## The state grows -/

theorem Coherent.grow {ρ : Valuation σ.sem.Dyn} {st st' : St D.Ty Raw}
    (coh : Coherent σ.Runs σ.Valid ρ st) (grows : St.Grows st st')
    (wf : Table.WF st'.next st'.table) : Coherent σ.Runs σ.Valid ρ st' := by
  obtain ⟨n, new, e, low⟩ := grows
  obtain ⟨cons, clo⟩ := consistent_extend coh.support coh.consistent coh.closed e low
  exact ⟨coh.support.mono n, wf, cons, clo, coh.valid⟩

theorem Coherent.fresh {ρ : Valuation σ.sem.Dyn} {st : St D.Ty Raw}
    (coh : Coherent σ.Runs σ.Valid ρ st) (vs : List σ.sem.Dyn) (valid : ∀ v, v ∈ vs → σ.Valid v) :
    Coherent σ.Runs σ.Valid (ρ.setFrom st.next vs) (FactCheck.fresh vs.length st).2 := by
  obtain ⟨cons, clo⟩ := consistent_setFrom coh.wf coh.consistent coh.closed vs
  exact ⟨setFrom_support coh.support vs, coh.wf.mono (by simp [FactCheck.fresh]), cons, clo,
    setFrom_valid coh.valid valid⟩

/-- Where the walk agrees with a run, its state is well formed and every name in scope has an
identifier below the next. -/
theorem Inv.scoped {Γ : Ctx D.Ty} {ρ : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} {k : Known} {st : St D.Ty Raw} (inv : Inv σ ρ ids env k st) :
    Scoped Γ ids st :=
  ⟨inv.coherent.wf, inv.agree.inScope inv.coherent.support⟩

/-- Identifiers that look up a list of values give, at each position, a value of the type
there. -/
theorem valuesOf_typed {ρ : Valuation σ.sem.Dyn} {made : List Nat} {res : List D.Ty}
    {vs : HList σ.sem.Val res} (look : valuesOf ρ made = some (σ.sem.dyns vs)) :
    ∀ (j m : Nat), made[j]? = some m → ∃ d, ρ m = some d ∧ res[j]? = some d.1 := by
  intro j m e1
  have hv := valuesOf_getElem look e1
  cases hd : (σ.sem.dyns vs)[j]? with
  | none => rw [hd] at hv; exact absurd hv (valuesOf_mem look m (List.mem_of_getElem? e1))
  | some d =>
      rw [hd] at hv
      exact ⟨d, hv, σ.sem.dyns_typed vs j d hd⟩

/-! ## What the types say -/

variable (laws : σ.Lawful)
include laws

/-- What the types of values at identifiers say holds of them. -/
theorem addTypeRanges_holds {k : Known} {ρ : Valuation σ.sem.Dyn}
    (hk : k.Holds σ.R ρ) (valid : ∀ i v, ρ i = some v → σ.Valid v)
    {ms : List Nat} {τs : List D.Ty}
    (h : ∀ (j m : Nat), ms[j]? = some m → ∃ d, ρ m = some d ∧ τs[j]? = some d.1) :
    (k.addRanges ms (τs.map σ.rules.range)).Holds σ.R ρ := by
  refine hk.addRanges fun j id r e1 e2 => ?_
  obtain ⟨d, hd, hτ⟩ := h j id e1
  rw [List.getElem?_map, hτ] at e2
  simp only [Option.map_some, Option.some.injEq] at e2
  obtain ⟨n, hn, has⟩ := laws.range d.1 r d.2 e2 (valid id d hd)
  exact ⟨n, ⟨d, hd, hn⟩, has⟩

/-- Valid values have types that have a value. -/
theorem any_noValue_of_valid : ∀ {τs : List D.Ty} (vs : HList σ.sem.Val τs), σ.AllValid vs →
    τs.any σ.rules.noValue = false
  | [], .nil, _ => rfl
  | _ :: _, .cons v rest, valid => by
      simp only [List.any_cons, laws.noValue _ v (allValid_cons.mp valid).1,
        any_noValue_of_valid rest (allValid_cons.mp valid).2, Bool.false_or]

/-- Valid values of the types come into scope: what is known stays as it is. -/
theorem enter_of_valid {k : Known} {τs : List D.Ty} {vs : HList σ.sem.Val τs}
    (valid : σ.AllValid vs) : k.enter σ.rules τs = k := by
  simp only [Known.enter, any_noValue_of_valid laws vs valid, Bool.false_eq_true,
    ↓reduceIte]

end

/-! ## Values at leaves -/

section
variable {D : Dialect} {Raw : Type} {σ : Setting D Raw}

/-- Values set at new identifiers keep the state and the valuation in agreement, and the new
identifiers have them. -/
theorem leaves_fresh {ρ : Valuation σ.sem.Dyn} {s : State D.Ty Raw}
    (coh : Coherent σ.Runs σ.Valid ρ s.st) (vs : List σ.sem.Dyn)
    (valid : ∀ v, v ∈ vs → σ.Valid v) :
    Coherent σ.Runs σ.Valid (ρ.setFrom s.st.next vs) (leaves none vs.length s).2.st ∧
      ρ.Le (ρ.setFrom s.st.next vs) ∧
      valuesOf (ρ.setFrom s.st.next vs) (leaves none vs.length s).1 = some vs :=
  ⟨Coherent.fresh coh vs valid, setFrom_le coh.support vs, valuesOf_setFrom ρ s.st.next vs⟩

/-- Values set at identifiers below the next one that have no value and are no results of
entries keep the state and the valuation in agreement. -/
theorem Coherent.setAt {ρ : Valuation σ.sem.Dyn} {st : St D.Ty Raw}
    (coh : Coherent σ.Runs σ.Valid ρ st) {base : Nat} (vs : List σ.sem.Dyn)
    (valid : ∀ v, v ∈ vs → σ.Valid v) (inside : base + vs.length ≤ st.next)
    (apart : LeavesApart st.table base vs.length)
    (unvalued : ∀ i, base ≤ i → i < base + vs.length → ρ i = none) :
    Coherent σ.Runs σ.Valid (ρ.setFrom base vs) st ∧ ρ.Le (ρ.setFrom base vs) := by
  have le : ρ.Le (ρ.setFrom base vs) := fun i v h => by
    simp only [Valuation.setFrom]
    rw [ite_eq_right fun within => by rw [unvalued i within.1 within.2] at h; cases h]
    exact h
  have results : ∀ e, e ∈ st.table → ∀ j, j < e.count →
      ρ.setFrom base vs (e.lo + j) = ρ (e.lo + j) := fun e m j lt => by
    simp only [Valuation.setFrom]
    rw [ite_eq_right fun within => apart e m j lt (e.lo + j - base) (by omega) (by omega)]
  refine ⟨⟨fun i hi => ?_, coh.wf, fun e m vals hvals j lt v hv => ?_,
    fun e m j lt hv a ha => ?_, setFrom_valid coh.valid valid⟩, le⟩
  · simp only [Valuation.setFrom]
    rw [ite_eq_right (by omega)]
    exact coh.support i hi
  · rw [results e m j lt] at hv
    obtain ⟨vals', hvals'⟩ := valuesOf_of_mem (ρ := ρ) (coh.closed e m j lt (by rw [hv]; simp))
    rw [valuesOf_le le hvals'] at hvals
    cases hvals
    exact coh.consistent e m _ hvals' j lt v hv
  · rw [results e m j lt] at hv
    have := coh.closed e m j lt hv a ha
    intro h0
    apply this
    cases hρ : ρ a with
    | none => rfl
    | some v => rw [le _ _ hρ] at h0; cases h0

end

/-! ## What is known after regions -/

/-- What the regions that ran say of a returned value, joined with what others say: nothing, or
a range that holds of the value. -/
def Joined (P : Range → Prop) (o : Option (Option Range)) : Prop :=
  o = some none ∨ ∃ r, o = some (some r) ∧ P r

theorem Joined.hull {P : Range → Prop} (hull : ∀ a b, P a ∨ P b → P (a.hull b))
    {acc : Option (Option Range)} (h : Joined P acc) (o : Option (Option Range)) :
    Joined P (hullOf acc o) := by
  rcases h with rfl | ⟨r, rfl, pr⟩
  · rcases o with _ | _ | b <;> exact Or.inl rfl
  · rcases o with _ | _ | b
    · exact Or.inr ⟨r, rfl, pr⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, hull r b (Or.inl pr)⟩

theorem Joined.into {P : Range → Prop} (hull : ∀ a b, P a ∨ P b → P (a.hull b))
    {o : Option (Option Range)} (h : Joined P o) (acc : Option (Option Range)) :
    Joined P (hullOf acc o) := by
  rcases h with rfl | ⟨r, rfl, pr⟩
  · rcases acc with _ | _ | a
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
  · rcases acc with _ | _ | a
    · exact Or.inr ⟨r, rfl, pr⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, hull a r (Or.inr pr)⟩

theorem joined_fold {T Raw : Type} {P : Range → Prop} (hull : ∀ a b, P a ∨ P b → P (a.hull b))
    {e : FactCheck.Exit T Raw} {position : Nat} (good : Joined P (e.rangeAt position)) :
    ∀ (exits : List (FactCheck.Exit T Raw)) (acc : Option (Option Range)), (Joined P acc ∨ e ∈ exits) →
      Joined P (exits.foldl (fun acc e' => hullOf acc (e'.rangeAt position)) acc)
  | [], acc, h => by
      rcases h with h | h
      · exact h
      · cases h
  | e' :: rest, acc, h => by
      simp only [List.foldl_cons]
      apply joined_fold hull good rest
      rcases h with h | h
      · exact Or.inl (h.hull hull _)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (good.into hull acc)
        · exact Or.inr h

section
variable {D : Dialect} {Raw : Type} {σ : Setting D Raw} (laws : σ.Lawful)
include laws

/-- What is known after regions, one of which ran and returned values that the new identifiers
have, holds. -/
theorem afterRegions_holds {exits : List (FactCheck.Exit D.Ty Raw)} {e : FactCheck.Exit D.Ty Raw}
    (he : e ∈ exits) {ρe ρ' : Valuation σ.sem.Dyn}
    (hek : e.known.Holds σ.R ρe) (valid : ∀ i v, ρ' i = some v → σ.Valid v) :
    ∀ (ms : List Nat) (τs : List D.Ty) (p : Nat) (k : Known), k.Holds σ.R ρ' →
      (∀ j m, ms[j]? = some m → ∃ d, ρ' m = some d ∧ ρe (e.rets.getD (p + j) 0) = some d ∧
        τs[j]? = some d.1) →
      (afterRegions σ.rules exits k ms τs p).Holds σ.R ρ'
  | m :: ms, τ :: τs, p, k, hk, h => by
      simp only [afterRegions]
      obtain ⟨d, hm, hr, hτ⟩ := h 0 m rfl
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hτ
      subst hτ
      apply afterRegions_holds he hek valid ms τs (p + 1)
      · refine (hk.addRange? fun r e1 => ?_).addRange? fun r e2 => ?_
        · have good : Joined (fun r => ∃ n, σ.R.nat d = some n ∧ r.Has n)
              (e.rangeAt p) := by
            simp only [FactCheck.Exit.rangeAt, hek.alive, Bool.false_eq_true, ↓reduceIte]
            cases hr' : e.known.rangeOf (e.rets.getD p 0) with
            | none => exact Or.inl rfl
            | some r0 =>
                obtain ⟨n, ⟨w, hw, hn⟩, has⟩ := hek.rangeOf hr'
                rw [Nat.add_zero] at hr
                rw [hr] at hw
                cases hw
                exact Or.inr ⟨r0, rfl, n, hn, has⟩
          have joined := joined_fold (fun a b h => by
            rcases h with ⟨n, hn, ha⟩ | ⟨n, hn, hb⟩
            · exact ⟨n, hn, ha.hull_left⟩
            · exact ⟨n, hn, hb.hull_right⟩) good exits none (Or.inr he)
          rcases joined with j | ⟨r', j, n, hn, has⟩
          · rw [j] at e1
            cases e1
          · rw [j] at e1
            simp only [Option.getD_some, Option.some.injEq] at e1
            subst e1
            exact ⟨n, ⟨d, hm, hn⟩, has⟩
        · obtain ⟨n, hn, has⟩ := laws.range d.1 r d.2 e2 (valid m d hm)
          exact ⟨n, ⟨d, hm, hn⟩, has⟩
      · intro j m e'
        obtain ⟨d', h1, h2, h3⟩ := h (j + 1) m (by simpa using e')
        refine ⟨d', h1, by rw [show p + 1 + j = p + (j + 1) by omega]; exact h2,
          by simpa using h3⟩
  | [], _, _, k, hk, _ => by
      simp only [afterRegions]
      have : exits.all (fun x => x.known.dead) = false := Bool.eq_false_iff.mpr fun h => by
        have := List.all_eq_true.mp h e he
        rw [hek.alive] at this
        cases this
      rw [this]
      exact hk
  | _ :: _, [], _, k, hk, _ => by
      simp only [afterRegions]
      have : exits.all (fun x => x.known.dead) = false := Bool.eq_false_iff.mpr fun h => by
        have := List.all_eq_true.mp h e he
        rw [hek.alive] at this
        cases this
      rw [this]
      exact hk

/-- After regions one of which ran: the new values are at the identifiers made for them, and what
is known of them holds. -/
theorem afterRegions_inv {Γ : Ctx D.Ty} {mid : List D.Ty} {exits : List (FactCheck.Exit D.Ty Raw)}
    {e : FactCheck.Exit D.Ty Raw} (he : e ∈ exits) {ρ ρ₁ ρ₂ : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} {k : Known} {st₀ st' st'' : St D.Ty Raw}
    (inv : Inv σ ρ ids env k st₀) (le : ρ.Le ρ₁) {mids : HList σ.sem.Val mid}
    (ex : ExitInv σ ρ₁ e st' mids) (results : Names mid) {made : List Nat}
    (coh : Coherent σ.Runs σ.Valid ρ₂ st'') (le₂ : ρ₁.Le ρ₂)
    (look : valuesOf ρ₂ made = some (σ.sem.dyns mids)) :
    Inv σ ρ₂ (bindIds ids results made) (env.extend results mids)
      ((afterRegions σ.rules exits k made mid 0).enter σ.rules mid) st'' := by
  have valid : σ.AllValid mids := allValid_of_valuesOf ex.rets ex.coherent.valid
  refine ⟨coh, agree_extend results mids _ (inv.agree.le (le.trans le₂)) look, ?_⟩
  rw [enter_of_valid laws valid]
  apply afterRegions_holds laws he ex.holds coh.valid _ _ 0 k (inv.holds.le (le.trans le₂))
  intro j m em
  have e1 := valuesOf_getElem look em
  cases hd : (σ.sem.dyns mids)[j]? with
  | none => rw [hd] at e1; exact absurd e1 (valuesOf_mem look m (List.mem_of_getElem? em))
  | some d =>
      rw [hd] at e1
      refine ⟨d, e1, ?_, σ.sem.dyns_typed mids j d hd⟩
      have lt : j < e.rets.length := by
        have h1 := valuesOf_length ex.rets
        have h2 := (List.getElem?_eq_some_iff.mp hd).1
        omega
      rw [Nat.zero_add, valuesOf_get ex.rets j lt, hd]

end

/-! ## The shapes of a choice -/

section
variable {D : Dialect} {Raw : Type} {σ : Setting D Raw}

/-- A choice fact holds of a valuation. -/
abbrev ChoiceHolds (ρ : Valuation σ.sem.Dyn) (c : ChoiceFact) : Prop :=
  ρ c.result ≠ none ∧ ∀ b, BoolAt σ.R ρ c.result b → b = c.conjunction →
    BoolAt σ.R ρ c.condition b ∧ BoolAt σ.R ρ c.other b

/-- The shapes of a choice hold where its condition has a value, the region that it chose ran,
and the results of the choice have the values that the region returned. -/
theorem choiceFacts_holds (lawful : OpFacts.Lawful σ.rules.ops σ.R σ.Runs)
    {ρ : Valuation σ.sem.Dyn} {tbl : Table Raw}
    (hc : Consistent σ.Runs ρ tbl) (hcl : Closed ρ tbl) {condition : Nat}
    {b0 : Bool} (hcond : BoolAt σ.R ρ condition b0)
    {first second : FactCheck.Exit D.Ty Raw} :
    ∀ (ms : List Nat) (p : Nat),
      (∀ j m, ms[j]? = some m → ∃ d, ρ m = some d ∧
        ρ ((if b0 then first else second).rets.getD (p + j) 0) = some d) →
      ∀ c, c ∈ choiceFacts σ.rules.ops tbl condition first second ms p → ChoiceHolds (σ := σ) ρ c
  | [], _, _, c, m => by simp [choiceFacts] at m
  | m :: ms, p, h, c, mem => by
      obtain ⟨d, hm, hran⟩ := h 0 m rfl
      rw [Nat.add_zero] at hran
      simp only [choiceFacts, List.mem_append] at mem
      rcases mem with (mem | mem) | mem
      · split at mem
        · next written e =>
            simp only [List.mem_singleton] at mem
            subst mem
            refine ⟨by rw [hm]; simp, fun b hb same => ?_⟩
            simp only at same
            subst same
            cases b0
            · simp only [Bool.false_eq_true, ↓reduceIte] at hran
              obtain ⟨vals, _, hf⟩ := formOf_values lawful hc hcl e hran
              obtain ⟨w, hw, hwb⟩ := hb
              rw [hm] at hw
              cases hw
              simp only [FormHolds] at hf
              rw [hf] at hwb
              cases hwb
            · simp only [↓reduceIte] at hran
              refine ⟨hcond, ?_⟩
              obtain ⟨w, hw, hwb⟩ := hb
              rw [hm] at hw
              cases hw
              exact ⟨d, hran, hwb⟩
        · simp at mem
      · split at mem
        · next written e =>
            simp only [List.mem_singleton] at mem
            subst mem
            refine ⟨by rw [hm]; simp, fun b hb same => ?_⟩
            simp only at same
            subst same
            cases b0
            · simp only [Bool.false_eq_true, ↓reduceIte] at hran
              refine ⟨hcond, ?_⟩
              obtain ⟨w, hw, hwb⟩ := hb
              rw [hm] at hw
              cases hw
              exact ⟨d, hran, hwb⟩
            · simp only [↓reduceIte] at hran
              obtain ⟨vals, _, hf⟩ := formOf_values lawful hc hcl e hran
              obtain ⟨w, hw, hwb⟩ := hb
              rw [hm] at hw
              cases hw
              simp only [FormHolds] at hf
              rw [hf] at hwb
              cases hwb
        · simp at mem
      · exact choiceFacts_holds lawful hc hcl hcond ms (p + 1) (fun j m' e' => by
          obtain ⟨d', h1, h2⟩ := h (j + 1) m' (by simpa using e')
          exact ⟨d', h1, by rw [show p + 1 + j = p + (j + 1) by omega]; exact h2⟩) c mem

theorem Known.Holds.addChoices {ρ : Valuation σ.sem.Dyn} {k : Known}
    (hk : k.Holds σ.R ρ) {cs : List ChoiceFact}
    (h : ∀ c, c ∈ cs → ChoiceHolds (σ := σ) ρ c) : (cs.foldl Known.addChoice k).Holds σ.R ρ :=
  foldl_invariant (P := fun k => k.Holds σ.R ρ) _ cs k hk
    (fun _ c m hk' => hk'.addChoice (h c m))

end

/-! ## The statement of soundness -/

section
variable {Raw : Type}

/-- Every identifier from `lo` on that has a value is a result of an entry of the table: no leaf
of a skeleton made from `lo` on and apart from the table has a value. -/
def Quiet {Val : Type} (lo : Nat) (ρ : Valuation Val) (tbl : Table Raw) : Prop :=
  ∀ i, lo ≤ i → ρ i ≠ none → ∃ e, e ∈ tbl ∧ ∃ j, j < e.count ∧ i = e.lo + j

variable {D : Dialect} {Val : Type}

/-- What a walk that follows a skeleton has at its start: the skeleton's leaves are made in order
from `lo` on, below `hi` and the next identifier, apart from the table, and none of them has a
value. Nothing when no skeleton is followed. -/
def Following {outs : List D.Ty} :
    Option (Skel D outs) → Nat → Nat → Valuation Val → St D.Ty Raw → Prop
  | none, _, _, _, _ => True
  | some skel, lo, hi, ρ, st =>
      Skel.Ordered skel lo hi ∧ hi ≤ st.next ∧ skel.Apart st.table ∧ Quiet lo ρ st.table

/-- What a walk of arms that follows the arms of a skeleton has at its start, as `Following`. -/
def ArmsFollowing {mid payloads : List D.Ty} :
    Option (SkelArms D mid payloads) → Nat → Nat → Valuation Val → St D.Ty Raw → Prop
  | none, _, _, _, _ => True
  | some arms, lo, hi, ρ, st =>
      SkelArms.Ordered arms lo hi ∧ hi ≤ st.next ∧ arms.Apart st.table ∧ Quiet lo ρ st.table

/-- What a walk that followed a skeleton has at its end: no identifier from `hi` on has a value
unless it is a result of an entry. Nothing when no skeleton is followed. -/
def Followed {outs : List D.Ty} : Option (Skel D outs) → Nat → Valuation Val → St D.Ty Raw → Prop
  | none, _, _, _ => True
  | some _, hi, ρ, st => Quiet hi ρ st.table

/-- What a walk of arms that followed the arms of a skeleton has at its end, as `Followed`. -/
def ArmsFollowed {mid payloads : List D.Ty} :
    Option (SkelArms D mid payloads) → Nat → Valuation Val → St D.Ty Raw → Prop
  | none, _, _, _ => True
  | some _, hi, ρ, st => Quiet hi ρ st.table

end

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

/-- No bound recorded yet is at one of the addresses. -/
def BoundsApart (st : St D.Ty Raw) (addresses : List (List (Key × Nat) × Key)) : Prop :=
  ∀ q, q ∈ st.bounds → ∀ bl key, q.1 = ⟨σ.definition, bl, some key, σ.role⟩ →
    (bl, key) ∉ addresses

/-- Every bound of the annotation at one of the addresses is one that the state records. -/
def Recorded (addresses : List (List (Key × Nat) × Key)) (st : St D.Ty Raw) : Prop :=
  ∀ p b bl key, (p, b) ∈ σ.F → p = ⟨σ.definition, bl, some key, σ.role⟩ →
    (bl, key) ∈ addresses → (p, b) ∈ st.bounds

/-- What the walk of a term shows of its run: every loop that it reaches respects the bound of
the annotation, it never stops `undefined`, and what holds where it returns. -/
abbrev Shows (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs)
    (path : List Frame) (env : Env σ.sem.Val Γ) (post : HList σ.sem.Val outs → Prop) : Prop :=
  t.EveryLoop σ.sem σ.permitted (Annotation.Bounded ⟨σ.F⟩ σ.definition σ.role) path blocks env ∧
    (t.denote σ.sem path env).Every σ.permitted post (fun stop => ¬ σ.undefined stop)

/-- The walk of a term, following a skeleton or none, from any point of a run that agrees with
it, shows the run: when it adds no refusal and no place that differs, the addresses of the term
are distinct and apart from the bounds recorded before, and the annotation's bounds at them are
recorded. Where it returns, the valuation has grown, agrees with the exit of the walk, and, when a
skeleton is followed, no leaf of it from its end on has a value. -/
def Sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs)
    (followed : Option (Skel D outs)) : Prop :=
  ∀ (path : List Frame) (ρ : Valuation σ.sem.Dyn) (ids : Ctx Nat) (env : Env σ.sem.Val Γ)
    (k : Known) (s : State D.Ty Raw) (lo hi : Nat),
    Inv σ ρ ids env k s.st → Following followed lo hi ρ s.st →
    (walk σ.rules σ.checks σ.definition σ.role blocks t followed ids k s).state.differs =
      s.differs →
    (walk σ.rules σ.checks σ.definition σ.role blocks t followed ids k s).state.st.refusals = [] →
    (t.addresses blocks).Nodup → BoundsApart σ s.st (t.addresses blocks) →
    Recorded σ (t.addresses blocks)
      (walk σ.rules σ.checks σ.definition σ.role blocks t followed ids k s).state.st →
    Shows σ blocks t path env (fun vs => ∃ ρ', ρ.Le ρ' ∧
      ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks t followed ids k s).region
        (walk σ.rules σ.checks σ.definition σ.role blocks t followed ids k s).state.st vs ∧
      Followed followed hi ρ'
        (walk σ.rules σ.checks σ.definition σ.role blocks t followed ids k s).state.st)

/-- The walk of the arms of a case analysis, from any point of a run that agrees with it, shows
the run of the arm of the alternative, as `Sound`. -/
def ArmsSound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
    (arms : Arms D Γ mid payloads) (followed : Option (SkelArms D mid payloads)) : Prop :=
  ∀ (path : List Frame) (ρ : Valuation σ.sem.Dyn) (ids : Ctx Nat) (env : Env σ.sem.Val Γ)
    (k : Known) (s : State D.Ty Raw) (lo hi : Nat) (p : Pick σ.sem.Val payloads),
    PickValid σ.sem σ.Valid p →
    Inv σ ρ ids env k s.st → ArmsFollowing followed lo hi ρ s.st →
    (walkArms σ.rules σ.checks σ.definition σ.role blocks arms followed ids k s).state.differs =
      s.differs →
    (walkArms σ.rules σ.checks σ.definition σ.role blocks arms followed ids k s).state.st.refusals =
      [] →
    (Arms.addresses blocks arms).Nodup → BoundsApart σ s.st (Arms.addresses blocks arms) →
    Recorded σ (Arms.addresses blocks arms)
      (walkArms σ.rules σ.checks σ.definition σ.role blocks arms followed ids k s).state.st →
    Arms.EveryLoop σ.sem σ.permitted (Annotation.Bounded ⟨σ.F⟩ σ.definition σ.role) arms path
        blocks env p ∧
      (arms.denote σ.sem path env p).Every σ.permitted (fun mids => ∃ ρ', ρ.Le ρ' ∧ ∃ e,
        e ∈ (walkArms σ.rules σ.checks σ.definition σ.role blocks arms followed ids k s).exits ∧
        ExitInv σ ρ' e
          (walkArms σ.rules σ.checks σ.definition σ.role blocks arms followed ids k s).state.st
          mids ∧
        ArmsFollowed followed hi ρ'
          (walkArms σ.rules σ.checks σ.definition σ.role blocks arms followed ids k s).state.st)
        (fun stop => ¬ σ.undefined stop)

end

/-! ## Bounds at addresses -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] {σ : Setting D Raw}

omit [DecidableEq Raw] in
theorem BoundsApart.sub {st : St D.Ty Raw} {A B : List (List (Key × Nat) × Key)}
    (h : BoundsApart σ st A) (sub : ∀ x, x ∈ B → x ∈ A) : BoundsApart σ st B :=
  fun q m bl key e inB => h q m bl key e (sub _ inB)

omit [DecidableEq Raw] in
theorem Recorded.sub {st : St D.Ty Raw} {A B : List (List (Key × Nat) × Key)}
    (h : Recorded σ A st) (sub : ∀ x, x ∈ B → x ∈ A) : Recorded σ B st :=
  fun p b bl key m e inB => h p b bl key m e (sub _ inB)

omit [DecidableEq Raw] in
/-- Bounds added at other addresses keep a state apart from the addresses. -/
theorem BoundsApart.extend {st st' : St D.Ty Raw} {A Bnew : List (List (Key × Nat) × Key)}
    {new : List (Place × Nat)} (h : BoundsApart σ st A) (e : st'.bounds = new ++ st.bounds)
    (at_ : BoundsAt σ.definition σ.role Bnew new) (apart : ∀ x, x ∈ Bnew → x ∉ A) :
    BoundsApart σ st' A := by
  intro q m bl key eq inA
  rw [e] at m
  rcases List.mem_append.mp m with m | m
  · obtain ⟨bl', key', eq', mem⟩ := at_ q m
    rw [eq] at eq'
    simp only [Place.mk.injEq, Option.some.injEq, true_and, and_true] at eq'
    obtain ⟨rfl, rfl⟩ := eq'
    exact apart _ mem inA
  · exact h q m bl key eq inA

omit [DecidableEq Raw] in
/-- Bounds recorded at other addresses are not those of the addresses. -/
theorem Recorded.strip {st st' : St D.Ty Raw} {A Bnew : List (List (Key × Nat) × Key)}
    {new : List (Place × Nat)} (h : Recorded σ A st') (e : st'.bounds = new ++ st.bounds)
    (at_ : BoundsAt σ.definition σ.role Bnew new) (apart : ∀ x, x ∈ A → x ∉ Bnew) :
    Recorded σ A st := by
  intro p b bl key m eq inA
  have := h p b bl key m eq inA
  rw [e] at this
  rcases List.mem_append.mp this with this | this
  · obtain ⟨bl', key', eq', mem⟩ := at_ _ this
    simp only at eq'
    rw [eq] at eq'
    simp only [Place.mk.injEq, Option.some.injEq, true_and, and_true] at eq'
    obtain ⟨rfl, rfl⟩ := eq'
    exact (apart _ inA mem).elim
  · exact this

end

/-! ## Values given to results of entries only -/

section
variable {Raw Val : Type}

/-- An identifier is a result of an entry of the table. -/
def IsResult (tbl : Table Raw) (i : Nat) : Prop :=
  ∃ e, e ∈ tbl ∧ ∃ j, j < e.count ∧ i = e.lo + j

/-- The second valuation gives values that the first has not only to results of entries of the
table. -/
def Fills (ρ ρ' : Valuation Val) (tbl : Table Raw) : Prop :=
  ∀ i, ρ i = none → ρ' i ≠ none → IsResult tbl i

theorem IsResult.grow {tbl tbl' : Table Raw} (sub : ∀ e, e ∈ tbl → e ∈ tbl') {i : Nat}
    (h : IsResult tbl i) : IsResult tbl' i := by
  obtain ⟨e, m, j, lt, eq⟩ := h
  exact ⟨e, sub e m, j, lt, eq⟩

theorem Fills.refl (ρ : Valuation Val) (tbl : Table Raw) : Fills ρ ρ tbl :=
  fun _ none some => absurd none some

theorem Fills.trans {ρ ρ' ρ'' : Valuation Val} {tbl tbl' : Table Raw} (first : Fills ρ ρ' tbl)
    (second : Fills ρ' ρ'' tbl') (sub : ∀ e, e ∈ tbl → e ∈ tbl') : Fills ρ ρ'' tbl' := by
  intro i none some
  cases h : ρ' i with
  | none => exact second i h some
  | some v => exact (first i none (by rw [h]; simp)).grow sub

theorem Quiet.low {lo lo' : Nat} {ρ : Valuation Val} {tbl : Table Raw} (h : Quiet lo ρ tbl)
    (le : lo ≤ lo') : Quiet lo' ρ tbl :=
  fun i hi valued => h i (Nat.le_trans le hi) valued

theorem Quiet.grow {lo : Nat} {ρ : Valuation Val} {tbl tbl' : Table Raw} (h : Quiet lo ρ tbl)
    (sub : ∀ e, e ∈ tbl → e ∈ tbl') : Quiet lo ρ tbl' :=
  fun i hi valued => IsResult.grow sub (h i hi valued)

/-- What is filled with values keeps every identifier from `lo` on without a value, except
results of entries. -/
theorem Quiet.fills {lo : Nat} {ρ ρ' : Valuation Val} {tbl tbl' : Table Raw} (h : Quiet lo ρ tbl)
    (fills : Fills ρ ρ' tbl') (sub : ∀ e, e ∈ tbl → e ∈ tbl') : Quiet lo ρ' tbl' := by
  intro i hi valued
  cases hv : ρ i with
  | none => exact fills i hv valued
  | some v => exact IsResult.grow sub (h i hi (by rw [hv]; simp))

/-- Leaves apart from the table from `lo` on have no value. -/
theorem Quiet.unvalued {lo base count : Nat} {ρ : Valuation Val} {tbl : Table Raw}
    (h : Quiet lo ρ tbl) (apart : LeavesApart tbl base count) (low : lo ≤ base) :
    ∀ i, base ≤ i → i < base + count → ρ i = none := by
  intro i hi lt
  cases hv : ρ i with
  | none => rfl
  | some v =>
      obtain ⟨e, m, j, jl, eq⟩ := h i (by omega) (by rw [hv]; simp)
      exact (apart e m j jl (i - base) (by omega) (by omega)).elim

theorem setFrom_above (ρ : Valuation Val) (lo : Nat) (vs : List Val) {i : Nat}
    (hi : lo + vs.length ≤ i) : ρ.setFrom lo vs i = ρ i := by
  simp only [Valuation.setFrom]
  rw [ite_eq_right (by omega)]

/-- Values set at leaves keep every identifier above them without a value, except results of
entries. -/
theorem Quiet.setFrom {lo base : Nat} {ρ : Valuation Val} {tbl : Table Raw} (h : Quiet lo ρ tbl)
    (low : lo ≤ base) (vs : List Val) : Quiet (base + vs.length) (ρ.setFrom base vs) tbl := by
  intro i hi valued
  rw [setFrom_above ρ base vs (by omega)] at valued
  exact h i (by omega) valued

end

/-! ## Sharing fills results of entries -/

section
variable {Val Raw : Type} {R : Reading Val} {Run : Raw → List Val → List Val → Prop}
  {ops : OpFacts Raw} {Valid : Val → Prop}

theorem fill_fills {ρ : Valuation Val} {tbl : Table Raw} {e : Entry Raw} (m : e ∈ tbl)
    {rs : List Val} (len : rs.length = e.count) : Fills ρ (ρ.fill e.lo rs) tbl := by
  intro i none some
  simp only [Valuation.fill, none] at some
  split at some
  · next within => exact ⟨e, m, i - e.lo, by omega, by omega⟩
  · exact (some rfl).elim

/-- An application of a written operation, shared: as `share_sound`, and the new values are
results of entries. -/
theorem share_fills [DecidableEq Raw] (lawful : OpFacts.Lawful ops R Run) {T : Type}
    {ρ : Valuation Val} {st : St T Raw} (coh : Coherent Run Valid ρ st) {w : Raw}
    {argIds : List Nat} {as rs : List Val} (hargs : valuesOf ρ argIds = some as)
    (hlt : ∀ a, a ∈ argIds → a < st.next) (run : Run w as rs) (hvalid : ∀ r, r ∈ rs → Valid r) :
    ∃ ρ', Stepped Run Valid ρ ρ' st (share w argIds rs.length st).2 ∧
      valuesOf ρ' (share w argIds rs.length st).1 = some rs ∧
      Fills ρ ρ' (share w argIds rs.length st).2.table := by
  have hfun : ∀ rs', Run w as rs' → rs' = rs := fun rs' r' => lawful.functional _ _ _ _ r' run
  simp only [share]
  split
  · next lo found =>
      obtain ⟨e, m, ew, ea, ec, el⟩ := Table.find_spec found
      subst el
      have hvs : valuesOf ρ e.args = some as := by rw [ea]; exact hargs
      have hrun : Run e.written as rs := by rw [ew]; exact run
      obtain ⟨le, sup, cons, clo, look⟩ := fill_entry coh.wf coh.consistent coh.closed
        coh.support m hvs hrun ec.symm (by rw [ew]; exact hfun)
      refine ⟨ρ.fill e.lo rs, ⟨le, ⟨sup, coh.wf, cons, clo, fill_valid coh.valid hvalid⟩,
        ⟨Nat.le_refl _, [], rfl, fun _ m => nomatch m⟩, rfl, rfl⟩, ?_, fill_fills m ec.symm⟩
      rw [← ec]; exact look
  · let e : Entry Raw := ⟨w, argIds, st.next, rs.length⟩
    have wf' : Table.WF (st.next + rs.length) (st.table.add e) :=
      show EntriesWF _ (e :: st.table.entries) from ⟨hlt, Nat.le_refl _, coh.wf⟩
    obtain ⟨cons', clo'⟩ := consistent_extend (tbl' := st.table.add e) (new := [e]) coh.support
      coh.consistent coh.closed rfl (fun e' m => by simp at m; subst m; exact Nat.le_refl _)
    obtain ⟨le, sup, cons, clo, look⟩ := fill_entry wf' cons' clo'
      (coh.support.mono (Nat.le_add_right _ _)) (e := e) List.mem_cons_self hargs run rfl hfun
    exact ⟨ρ.fill st.next rs, ⟨le, ⟨sup, wf', cons, clo, fill_valid coh.valid hvalid⟩,
      ⟨Nat.le_add_right _ _, [e], rfl, fun e' m => by simp at m; subst m; exact Nat.le_refl _⟩,
      rfl, rfl⟩, look, fill_fills (e := e) List.mem_cons_self rfl⟩

/-- Resolving an operand of a requirement: as `operandId_sound`, and the new values are results
of entries. -/
theorem operandId_fills [DecidableEq Raw] (lawful : OpFacts.Lawful ops R Run)
    (runValid : ∀ w as rs, Run w as rs → (∀ a, a ∈ as → Valid a) → ∀ r, r ∈ rs → Valid r)
    {T : Type} {ρ : Valuation Val} {st : St T Raw} (coh : Coherent Run Valid ρ st)
    {argIds : List Nat} {args : List Val} (hargs : valuesOf ρ argIds = some args)
    (hlt : ∀ a, a ∈ argIds → a < st.next) {operand : Operand Raw}
    (runs : ∀ w ps, operand = .apply w ps →
      ∃ as rs, atPositions args ps = some as ∧ Run w as rs ∧ rs.length = 1) :
    ∃ ρ', Stepped Run Valid ρ ρ' st (operandId argIds st operand).2 ∧
      (∀ id, (operandId argIds st operand).1 = some id →
        ∃ v, ρ' id = some v ∧ operand.Denotes Run args v) ∧
      Fills ρ ρ' (operandId argIds st operand).2.table := by
  cases operand with
  | arg position =>
      refine ⟨ρ, Stepped.refl coh, fun id e => ?_, Fills.refl ρ _⟩
      simp only [operandId] at e
      have := valuesOf_getElem hargs e
      cases hv : args[position]? with
      | none =>
          rw [hv] at this
          exact absurd this (valuesOf_mem hargs id (List.mem_of_getElem? e))
      | some v =>
          rw [hv] at this
          exact ⟨v, this, hv⟩
  | apply w ps =>
      obtain ⟨as, rs, has, run, one⟩ := runs w ps rfl
      simp only [operandId]
      split
      · next ids' e =>
          obtain ⟨values, hvalues, hl⟩ := atPositions_valuesOf hargs e
          rw [has] at hvalues
          cases hvalues
          have hlt' : ∀ a, a ∈ ids' → a < st.next := fun a m => hlt a (atPositions_mem e a m)
          have hvalid : ∀ r, r ∈ rs → Valid r :=
            runValid w as rs run (valuesOf_valid hl coh.valid)
          obtain ⟨ρ', step, look, fills⟩ := share_fills lawful coh hl hlt' run hvalid
          rw [one] at step look fills
          refine ⟨ρ', step, fun id hid => ?_, fills⟩
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
              simpa using valuesOf_get look 0 (by simp)
      · refine ⟨ρ, Stepped.refl coh, fun id e => ?_, Fills.refl ρ _⟩
        cases e

theorem operandIds_fills [DecidableEq Raw] (lawful : OpFacts.Lawful ops R Run)
    (runValid : ∀ w as rs, Run w as rs → (∀ a, a ∈ as → Valid a) → ∀ r, r ∈ rs → Valid r)
    {T : Type} {argIds : List Nat} {args : List Val} :
    ∀ (os : List (Operand Raw)) {ρ : Valuation Val} {st : St T Raw},
      Coherent Run Valid ρ st → valuesOf ρ argIds = some args →
      (∀ a, a ∈ argIds → a < st.next) →
      (∀ o, o ∈ os → ∀ w ps, o = .apply w ps →
        ∃ as rs, atPositions args ps = some as ∧ Run w as rs ∧ rs.length = 1) →
      ∃ ρ', Stepped Run Valid ρ ρ' st (operandIds argIds os st).2 ∧
        OperandsAt Run args ρ' os (operandIds argIds os st).1 ∧
        Fills ρ ρ' (operandIds argIds os st).2.table
  | [], ρ, st, coh, _, _, _ => ⟨ρ, Stepped.refl coh, trivial, Fills.refl ρ _⟩
  | o :: os, ρ, st, coh, hargs, hlt, runs => by
      simp only [operandIds]
      obtain ⟨ρ₁, step₁, first, fills₁⟩ := operandId_fills lawful runValid coh hargs hlt
        (runs o List.mem_cons_self)
      obtain ⟨ρ₂, step₂, rest, fills₂⟩ := operandIds_fills lawful runValid os step₁.coherent
        (valuesOf_le step₁.le hargs) (fun a m => Nat.lt_of_lt_of_le (hlt a m) step₁.grows.next)
        (fun o' m => runs o' (List.mem_cons_of_mem _ m))
      refine ⟨ρ₂, step₁.trans step₂, ⟨fun id e => ?_, rest⟩, fills₁.trans fills₂ step₂.grows.sub⟩
      obtain ⟨v, hv, hd⟩ := first id e
      exact ⟨v, step₂.le _ _ hv, hd⟩

/-- The requirements of an application that the walk decides: as `checkRequirements_sound`, and
the new values are results of entries. -/
theorem checkRequirements_fills [DecidableEq Raw] (lawful : OpFacts.Lawful ops R Run)
    (runValid : ∀ w as rs, Run w as rs → (∀ a, a ∈ as → Valid a) → ∀ r, r ∈ rs → Valid r)
    {T : Type} {k : Known} {place : Place} {written : Raw} {argIds : List Nat}
    {args : List Val} :
    ∀ (reqs : List (Requirement Raw)) {ρ : Valuation Val} {st : St T Raw},
      Coherent Run Valid ρ st → k.Holds R ρ → valuesOf ρ argIds = some args →
      (∀ a, a ∈ argIds → a < st.next) →
      (∀ req, req ∈ reqs → ∀ o, o ∈ req.operands → ∀ w ps, o = .apply w ps →
        ∃ as rs, atPositions args ps = some as ∧ Run w as rs ∧ rs.length = 1) →
      (checkRequirements ops k place written argIds reqs st).refusals = [] →
      ∃ ρ', Stepped Run Valid ρ ρ' st (checkRequirements ops k place written argIds reqs st) ∧
        (∀ req, req ∈ reqs → req.Holds Run R args) ∧
        Fills ρ ρ' (checkRequirements ops k place written argIds reqs st).table
  | [], ρ, st, coh, _, _, _, _, _ =>
      ⟨ρ, Stepped.refl coh, fun _ m => (nomatch m), Fills.refl ρ _⟩
  | req :: rest, ρ, st, coh, hk, hargs, hlt, runs, hnone => by
      obtain ⟨ρ₁, step₁, res, fills₁⟩ := operandIds_fills lawful runValid req.operands coh hargs
        hlt (runs req List.mem_cons_self)
      simp only [checkRequirements] at hnone ⊢
      generalize operandIds argIds req.operands st = resolved at step₁ res fills₁ hnone ⊢
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
          exact operandRange_sound lawful hk₁ (valuesOf_le step₁.le hargs) hv' hd
        obtain ⟨ρ₂, step₂, others, fills₂⟩ := checkRequirements_fills lawful runValid rest
          step₁.coherent hk₁ (valuesOf_le step₁.le hargs)
          (fun a m => Nat.lt_of_lt_of_le (hlt a m) step₁.grows.next)
          (fun req' m => runs req' (List.mem_cons_of_mem _ m)) hnone
        refine ⟨ρ₂, step₁.trans step₂, fun req' m => ?_, fills₁.trans fills₂ step₂.grows.sub⟩
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

/-! ## The order of the operands of a value -/

section
variable {D : Dialect} {Raw : Type} {σ : Setting D Raw} (laws : σ.Lawful)
include laws

/-- Operands that have values, in the order in which the table places an application of a
written operation, have values on which the operation gives the same results: the two operands
of an operation that commutes, exchanged, by the law `binding`. -/
theorem order_values {ρ : Valuation σ.sem.Dyn} (raw : Raw) :
    ∀ {ids : List Nat} {vs results : List σ.sem.Dyn}, valuesOf ρ ids = some vs →
      σ.Runs raw vs results →
      ∃ vs', valuesOf ρ (σ.rules.values.order raw ids) = some vs' ∧ σ.Runs raw vs' results
  | [], _, _, h, r => ⟨_, h, r⟩
  | [_], _, _, h, r => ⟨_, h, r⟩
  | [a, b], vs, results, h, r => by
      simp only [ValueRules.order]
      split
      · next exchanged =>
          obtain ⟨va, vb, rfl, ha, hb⟩ := valuesOf_pair h
          refine ⟨[vb, va], by simp [valuesOf, ha, hb],
            laws.binding.commutative raw exchanged.1 va vb results r.1, fun v m => ?_, r.2.2⟩
          apply r.2.1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at m ⊢
          exact m.symm
      · exact ⟨_, h, r⟩
  | _ :: _ :: _ :: _, _, _, h, r => ⟨_, h, r⟩

end

/-! ## What a step adds, read backwards -/

section
variable {D : Dialect} {Raw : Type}

/-- A list that is another with a prefix added is that list only when the prefix is empty. -/
theorem prefix_nil {α : Type} {l m : List α} (h : l ++ m = m) : l = [] := by
  have := congrArg List.length h
  rw [List.length_append] at this
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- Of two steps that together add no place that differs, neither adds one. -/
theorem differs_both {s s' s'' : State D.Ty Raw} (first : ∃ n, s'.differs = n ++ s.differs)
    (second : ∃ n, s''.differs = n ++ s'.differs) (same : s''.differs = s.differs) :
    s'.differs = s.differs ∧ s''.differs = s'.differs := by
  obtain ⟨n1, e1⟩ := first
  obtain ⟨n2, e2⟩ := second
  rw [e2, e1, ← List.append_assoc] at same
  have := prefix_nil same
  rw [List.append_eq_nil_iff] at this
  obtain ⟨rfl, rfl⟩ := this
  exact ⟨e1, e2⟩

/-- Of three steps that together add no place that differs, none adds one. -/
theorem differs_three {s s₁ s₂ s₃ : State D.Ty Raw} (first : ∃ n, s₁.differs = n ++ s.differs)
    (second : ∃ n, s₂.differs = n ++ s₁.differs) (third : ∃ n, s₃.differs = n ++ s₂.differs)
    (same : s₃.differs = s.differs) :
    s₁.differs = s.differs ∧ s₂.differs = s₁.differs ∧ s₃.differs = s₂.differs := by
  obtain ⟨n1, e1⟩ := first
  obtain ⟨n2, e2⟩ := second
  obtain ⟨n3, e3⟩ := third
  have chain := same
  rw [e3, e2, e1] at chain
  have := congrArg List.length chain
  simp only [List.length_append] at this
  rw [List.eq_nil_of_length_eq_zero (show n1.length = 0 by omega)] at e1
  rw [List.eq_nil_of_length_eq_zero (show n2.length = 0 by omega)] at e2
  rw [List.eq_nil_of_length_eq_zero (show n3.length = 0 by omega)] at e3
  exact ⟨e1, e2, e3⟩

/-- Where a later state has no refusal, neither has an earlier one that it adds to. -/
theorem refusals_before {s s' : St D.Ty Raw} (adds : ∃ n, s'.refusals = n ++ s.refusals)
    (none : s'.refusals = []) : s.refusals = [] := by
  obtain ⟨n, e⟩ := adds
  rw [none] at e
  exact (List.append_eq_nil_iff.mp e.symm).2

end

/-! ## Each construct, when no skeleton is followed -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] {σ : Setting D Raw} (laws : σ.Lawful)

omit [DecidableEq Raw] in
@[simp] theorem Exit.region_skel {outs : List D.Ty} (e : Exit D Raw outs) (skel : Skel D outs) :
    ({ e with skel := skel } : Exit D Raw outs).region = e.region := rfl

theorem ret_sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (xs : HList (Var Γ) outs) : Sound σ blocks (.ret xs) none := by
  intro path ρ ids env k s lo hi inv _ _ _ _ _ _
  simp only [Shows, walk, Term.EveryLoop, Term.denote, Process.Every, Option.isSome_none,
    miss_free]
  exact ⟨trivial, ρ, Valuation.Le.refl ρ, ⟨inv.coherent, valuesOf_idsOf inv.agree xs, inv.holds⟩,
    trivial⟩

include laws in
/-- The requirements of an operation, decided where it is applied: where none is refused, they
hold of the values of its operands, and the valuation, grown by the values of the applications
that they enter in the table, which are results of entries, agrees with the state after them. -/
theorem requirements_sound {Γ : Ctx D.Ty} {ins res : List D.Ty} (place : Place)
    (o : D.Op ins res) (args : HList (Var Γ) ins) {ρ : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} {k : Known} {st : St D.Ty Raw} (inv : Inv σ ρ ids env k st)
    (refusals : (checkRequirements σ.rules.ops k place (σ.rules.written o) (idsOf ids args)
      (σ.rules.ops.requires (σ.rules.written o)) st).refusals = []) :
    ∃ ρ₁ : Valuation σ.sem.Dyn, ρ.Le ρ₁ ∧
      Inv σ ρ₁ ids env k (checkRequirements σ.rules.ops k place (σ.rules.written o)
        (idsOf ids args) (σ.rules.ops.requires (σ.rules.written o)) st) ∧
      σ.rules.Required σ.sem σ.R σ.Run σ.Valid o (env.all args) ∧
      Fills ρ ρ₁ (checkRequirements σ.rules.ops k place (σ.rules.written o) (idsOf ids args)
        (σ.rules.ops.requires (σ.rules.written o)) st).table := by
  have lawful : OpFacts.Lawful σ.rules.ops σ.R σ.Runs := laws.ops
  have runValid : ∀ w as rs, σ.Runs w as rs → (∀ a, a ∈ as → σ.Valid a) → ∀ r, r ∈ rs →
      σ.Valid r := fun _ _ _ run _ => run.2.2
  have va : σ.AllValid (env.all args) :=
    env_all_valid (agree_valid inv.agree inv.coherent.valid) args
  obtain ⟨ρ₁, step₁, hreq, fills₁⟩ := checkRequirements_fills lawful runValid
    (σ.rules.ops.requires (σ.rules.written o)) inv.coherent inv.holds
    (valuesOf_idsOf inv.agree args) (idsOf_lt inv.scoped.2 args)
    (fun req m operand mo w ps e => laws.named o (env.all args) va req m operand mo w ps e)
    refusals
  exact ⟨ρ₁, step₁.le, ⟨step₁.coherent, inv.agree.le step₁.le, inv.holds.le step₁.le⟩, hreq,
    fills₁⟩

include laws in
/-- A shared operation whose requirements hold: it returns; its results have the identifiers that
the table gives, with what is learned of them. -/
theorem value_sound {Γ : Ctx D.Ty} {ins res : List D.Ty} (key : Key) (o : D.Op ins res)
    (shared : σ.rules.shared o = true) (args : HList (Var Γ) ins) (results : Names res)
    (path : List Frame) (ρ : Valuation σ.sem.Dyn) (ids : Ctx Nat) (env : Env σ.sem.Val Γ)
    (k : Known) (st : St D.Ty Raw) (inv : Inv σ ρ ids env k st)
    (required : σ.rules.Required σ.sem σ.R σ.Run σ.Valid o (env.all args)) :
    ∃ values : HList σ.sem.Val res, ∃ ρ₂ : Valuation σ.sem.Dyn,
      σ.sem.op key o path (env.all args) = .done values ∧ ρ.Le ρ₂ ∧
      Inv σ ρ₂ (bindIds ids results
          (valueStep σ.rules (σ.rules.written o) res (idsOf ids args) k st).1)
        (env.extend results values)
        (valueStep σ.rules (σ.rules.written o) res (idsOf ids args) k st).2.1
        (valueStep σ.rules (σ.rules.written o) res (idsOf ids args) k st).2.2 ∧
      Fills ρ ρ₂ (valueStep σ.rules (σ.rules.written o) res (idsOf ids args) k st).2.2.table := by
  have lawful : OpFacts.Lawful σ.rules.ops σ.R σ.Runs := laws.ops
  have va : σ.AllValid (env.all args) :=
    env_all_valid (agree_valid inv.agree inv.coherent.valid) args
  have hargs := valuesOf_idsOf inv.agree args
  have hlt : ∀ a, a ∈ idsOf ids args → a < st.next := idsOf_lt inv.scoped.2 args
  obtain ⟨values, ran⟩ := laws.defined o shared key path (env.all args) va required
  have run : σ.Run (σ.rules.written o) (σ.sem.dyns (env.all args)) (σ.sem.dyns values) := by
    rcases laws.binding.computes o (σ.rules.written o) (σ.rules.values_written_shared shared) key
      path (env.all args) with ⟨values', ran', run⟩ | ⟨stop, halted, _⟩
    · rw [ran] at ran'
      cases ran'
      exact run
    · rw [ran] at halted
      cases halted
  have vr : σ.AllValid values := laws.keeps (σ.rules.written o) _ _ run va
  have runs : σ.Runs (σ.rules.written o) (σ.sem.dyns (env.all args)) (σ.sem.dyns values) :=
    ⟨run, va, vr⟩
  obtain ⟨ordered, hordered, runOrdered⟩ := order_values laws (σ.rules.written o) hargs runs
  simp only [valueStep]
  obtain ⟨ρ₂, step₂, look, fills₂⟩ := share_fills lawful inv.coherent hordered
    (σ.rules.values.order_lt hlt) runOrdered vr
  rw [σ.sem.dyns_length] at step₂ look fills₂
  have le := step₂.le
  refine ⟨values, ρ₂, ran, le, ⟨step₂.coherent, agree_extend results values _
    (inv.agree.le le) look, ?_⟩, fills₂⟩
  · rw [enter_of_valid laws vr]
    refine addTypeRanges_holds laws (Known.Holds.addOffset lawful step₂.coherent.consistent
      step₂.coherent.closed (inv.holds.le le)
      ((inv.holds.le le).addRanges fun j id rr e1 e2 => ?_) (valuesOf_le le hargs) look
      fun f hf => lawful.form _ _ _ f hf runs)
      step₂.coherent.valid (valuesOf_typed look)
    have known : ∀ (i : Nat) (rr : Range),
        (List.map k.rangeOf (idsOf ids args))[i]? = some (some rr) →
        ∃ v n, (σ.sem.dyns (env.all args))[i]? = some v ∧ σ.R.nat v = some n ∧ rr.Has n := by
      intro i rr e
      rw [List.getElem?_map] at e
      cases ha : (idsOf ids args)[i]? with
      | none => rw [ha] at e; cases e
      | some a =>
          rw [ha] at e
          simp only [Option.map_some, Option.some.injEq] at e
          obtain ⟨n, ⟨v, hv, hn⟩, has⟩ := inv.holds.rangeOf e
          have := valuesOf_getElem hargs ha
          rw [hv] at this
          exact ⟨v, n, this.symm, hn, has⟩
    obtain ⟨v, n, hv, hn, has⟩ := lawful.ranges _ _ _ _ runs known j rr e2
    have := valuesOf_getElem look e1
    rw [hv] at this
    exact ⟨n, ⟨v, this, hn⟩, has⟩

include laws in
/-- An operation, when no skeleton is followed: its requirements hold, since none is refused; a
shared operation returns, with its results where the table places them; an operation kept in
order returns valid values on permitted replies, or stops with a stop that is not `undefined`,
and its results are at new leaves. -/
theorem op_sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs ins res : List D.Ty}
    (key : Key) (o : D.Op ins res) (args : HList (Var Γ) ins) (results : Names res)
    (rest : Term D (Γ.extend results) outs) (ih : Sound σ blocks rest none) :
    Sound σ blocks (.op key o args results rest) none := by
  intro path ρ ids env k s lo hi inv _ differs hnone nodup apart recorded
  have nodup' := (List.nodup_cons.mp nodup).2
  have recorded' := fun (st : St D.Ty Raw) (h : Recorded σ (Term.addresses blocks
    (.op key o args results rest)) st) =>
      Recorded.sub (σ := σ) h fun _ m => List.mem_cons_of_mem _ m
  obtain ⟨-, b₁⟩ := checkRequirements_state σ.rules.ops k ⟨σ.definition, blocks, some key, σ.role⟩
    (σ.rules.written o) (idsOf ids args) (σ.rules.ops.requires (σ.rules.written o)) s.st
  cases hs : σ.rules.shared o with
  | true =>
      simp only [walk, hs] at differs hnone recorded ⊢
      generalize hst₁ : checkRequirements σ.rules.ops k ⟨σ.definition, blocks, some key, σ.role⟩
        (σ.rules.written o) (idsOf ids args) (σ.rules.ops.requires (σ.rules.written o)) s.st = st₁
        at b₁ differs hnone recorded ⊢
      obtain ⟨r₂, b₂⟩ := valueStep_state σ.rules (σ.rules.written o) res (idsOf ids args) k st₁
      have refs₁ : st₁.refusals = [] := by
        rw [← r₂]
        exact refusals_before (walk_adds σ.rules σ.checks σ.definition σ.role blocks rest none
          _ _ { s with st := (valueStep σ.rules (σ.rules.written o) res (idsOf ids args) k
            st₁).2.2 }).1 hnone
      obtain ⟨ρ₁, le₁, inv₁, required, -⟩ := requirements_sound laws
        ⟨σ.definition, blocks, some key, σ.role⟩ o args inv (by rw [hst₁]; exact refs₁)
      rw [hst₁] at inv₁
      obtain ⟨values, ρ₂, ran, le, inv', -⟩ := value_sound laws key o hs args results path ρ₁ ids
        env k st₁ inv₁ required
      have shows := ih path ρ₂ _ _ _ _ lo hi inv' trivial differs hnone nodup'
        (fun q m bl key' eq inR => apart q (by rw [← b₁, ← b₂]; exact m) bl key' eq
          (List.mem_cons_of_mem _ inR)) (recorded' _ recorded)
      simp only [Shows, Term.EveryLoop, Term.denote, ran, Process.bind, Process.Every]
      exact ⟨shows.1, Process.every_mono _ _ (fun vs h => by
        obtain ⟨ρ', le', ex, f⟩ := h
        exact ⟨ρ', le₁.trans (le.trans le'), ex, f⟩) (fun _ h => h) shows.2⟩
  | false =>
      simp only [walk, hs, effectEntry, Option.map_none, Option.isSome_none, miss_free, leaves,
        Exit.region_skel] at differs hnone recorded ⊢
      generalize hst₁ : checkRequirements σ.rules.ops k ⟨σ.definition, blocks, some key, σ.role⟩
        (σ.rules.written o) (idsOf ids args) (σ.rules.ops.requires (σ.rules.written o)) s.st = st₁
        at b₁ differs hnone recorded ⊢
      have refs₁ : st₁.refusals = [] :=
        refusals_before (walk_adds σ.rules σ.checks σ.definition σ.role blocks rest none
          _ _ { s with st := (fresh res.length st₁).2 }).1 hnone
      obtain ⟨ρ₁, le₁, inv₁, required, -⟩ := requirements_sound laws
        ⟨σ.definition, blocks, some key, σ.role⟩ o args inv (by rw [hst₁]; exact refs₁)
      rw [hst₁] at inv₁
      have apart₁ : BoundsApart σ st₁ (Term.addresses blocks (.op key o args results rest)) :=
        fun q m => apart q (by rw [← b₁]; exact m)
      have va : σ.AllValid (env.all args) :=
        env_all_valid (agree_valid inv.agree inv.coherent.valid) args
      have restShows : ∀ values : HList σ.sem.Val res, σ.AllValid values →
          Shows σ blocks rest path (env.extend results values) (fun vs => ∃ ρ', ρ.Le ρ' ∧
            ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks rest none
              (bindIds ids results (fresh res.length st₁).1)
              ((k.addRanges (fresh res.length st₁).1 (res.map σ.rules.range)).enter
                σ.rules res) { s with st := (fresh res.length st₁).2 }).region
              (walk σ.rules σ.checks σ.definition σ.role blocks rest none
                (bindIds ids results (fresh res.length st₁).1)
                ((k.addRanges (fresh res.length st₁).1 (res.map σ.rules.range)).enter
                  σ.rules res) { s with st := (fresh res.length st₁).2 }).state.st vs ∧
            Followed (none : Option (Skel D outs)) hi ρ'
              (walk σ.rules σ.checks σ.definition σ.role blocks rest none
                (bindIds ids results (fresh res.length st₁).1)
                ((k.addRanges (fresh res.length st₁).1 (res.map σ.rules.range)).enter
                  σ.rules res) { s with st := (fresh res.length st₁).2 }).state.st) := by
        intro values valid
        obtain ⟨coh, le, look⟩ := leaves_fresh (s := { s with st := st₁ }) inv₁.coherent
          (σ.sem.dyns values) valid
        simp only [leaves, σ.sem.dyns_length] at coh look
        have inv' : Inv σ (ρ₁.setFrom st₁.next (σ.sem.dyns values))
            (bindIds ids results (fresh res.length st₁).1) (env.extend results values)
            ((k.addRanges (fresh res.length st₁).1 (res.map σ.rules.range)).enter
              σ.rules res) (fresh res.length st₁).2 := by
          refine ⟨coh, agree_extend results values _ (inv₁.agree.le le) look, ?_⟩
          rw [enter_of_valid laws valid]
          exact addTypeRanges_holds laws (inv₁.holds.le le) coh.valid (valuesOf_typed look)
        have shows := ih path _ _ _ _ { s with st := (fresh res.length st₁).2 } lo hi inv' trivial
          differs hnone nodup' (BoundsApart.sub apart₁ fun _ m => List.mem_cons_of_mem _ m)
          (recorded' _ recorded)
        exact ⟨shows.1, Process.every_mono _ _ (fun vs h => by
          obtain ⟨ρ', le', ex, f⟩ := h
          exact ⟨ρ', le₁.trans (le.trans le'), ex, f⟩) (fun _ h => h) shows.2⟩
      have effect := laws.effect o hs key path (env.all args) va required
      simp only [Shows, Term.EveryLoop, Term.denote]
      refine ⟨Process.every_mono _ _ (fun values valid => (restShows values valid).1)
        (fun _ _ => trivial) effect, ?_⟩
      rw [Process.every_bind]
      exact Process.every_mono _ _ (fun values valid => (restShows values valid).2) (fun _ h => h)
        effect

include laws in
/-- A guard: where its condition is false it stops, with a stop that is not `undefined`; where it
is true, what it teaches holds. -/
theorem guard_sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs : List D.Ty} {t : D.Ty}
    (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t) (why : Reason)
    (rest : Term D Γ outs) (ih : Sound σ blocks rest none) :
    Sound σ blocks (.guard key w c ok why rest) none := by
  intro path ρ ids env k s lo hi inv _ differs hnone nodup apart recorded
  have lawful : OpFacts.Lawful σ.rules.ops σ.R σ.Runs := laws.ops
  simp only [walk, guardEntry, Option.isSome_none, miss_free, Exit.region_skel]
    at differs hnone recorded ⊢
  have hc := inv.agree.idOf c
  have read := laws.condition ok (env.get c) (inv.coherent.valid _ _ hc)
  simp only [Shows, Term.EveryLoop, Term.denote]
  cases hv : σ.sem.holds ok (env.get c) with
  | false =>
      simp only [Bool.cond_false, Process.Every, Bool.false_eq_true, false_implies]
      exact ⟨trivial, laws.stop w why ⟨path, key⟩⟩
  | true =>
      rw [hv] at read
      have k' := assume_holds lawful inv.coherent.consistent inv.coherent.closed s.st.next inv.holds
        ⟨_, hc, read⟩
      have shows := ih path ρ ids env _ s lo hi ⟨inv.coherent, inv.agree, k'⟩ trivial differs hnone
        (List.nodup_cons.mp nodup).2 (BoundsApart.sub apart fun x m => List.mem_cons_of_mem _ m)
        (Recorded.sub recorded fun x m => List.mem_cons_of_mem _ m)
      simp only [Bool.cond_true, forall_const]
      exact ⟨shows.1, shows.2⟩

include laws in
/-- A block: its body under the blocks with it, then what is known after it, of the values it
returns at new leaves. -/
theorem block_sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs mid : List D.Ty}
    (key : Key) (number : Nat) (body : Term D Γ mid) (results : Names mid)
    (rest : Term D (Γ.extend results) outs)
    (ihb : Sound σ (blocks ++ [(key, number)]) body none) (ihr : Sound σ blocks rest none) :
    Sound σ blocks (.block key number body results rest) none := by
  intro path ρ ids env k s lo hi inv _ differs hnone nodup apart recorded
  simp only [walk, blockEntry, Option.map_none, Option.isSome_none, miss_free, leaves,
    Exit.region_skel] at differs hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  obtain ⟨⟨rb, eb⟩, ⟨nb, ebb, atb⟩, db⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    (blocks ++ [(key, number)]) body none ids k s
  generalize he : walk σ.rules σ.checks σ.definition σ.role (blocks ++ [(key, number)]) body none
    ids k s = e at differs hnone recorded eb ebb db ⊢
  obtain ⟨⟨nr, er⟩, ⟨nbr, ebr, atr⟩, dr⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks rest none (bindIds ids results (fresh mid.length e.state.st).1)
    ((afterRegions σ.rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
      σ.rules mid)
    { e.state with st := (fresh mid.length e.state.st).2 }
  obtain ⟨differsB, differsR⟩ := differs_both db dr differs
  have refs : e.state.st.refusals = [] := refusals_before ⟨nr, er⟩ hnone
  have nodupB := (List.nodup_append.mp nodup).1
  have nodupR := (List.nodup_append.mp nodup).2.1
  have recB : Recorded σ (body.addresses (blocks ++ [(key, number)])) e.state.st :=
    (Recorded.sub recorded fun x m => List.mem_append_left _ m).strip ebr atr
      (fun x m mr => nodup_apart nodup m mr)
  have showsB := ihb (path ++ [.iteration key number]) ρ ids env k s lo lo inv trivial
    (by rw [he]; exact differsB) (by rw [he]; exact refs) nodupB
    (BoundsApart.sub apart fun x m => List.mem_append_left _ m) (by rw [he]; exact recB)
  rw [he] at showsB
  have afterRest : ∀ mids : HList σ.sem.Val mid, (∃ ρ₁, ρ.Le ρ₁ ∧
      ExitInv σ ρ₁ e.region e.state.st mids ∧ Followed (none : Option (Skel D mid)) lo ρ₁
        e.state.st) →
      Shows σ blocks rest path (env.extend results mids) (fun vs => ∃ ρ', ρ.Le ρ' ∧
        ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks rest none
          (bindIds ids results (fresh mid.length e.state.st).1)
          ((afterRegions σ.rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
            σ.rules mid) { e.state with st := (fresh mid.length e.state.st).2 }).region
          (walk σ.rules σ.checks σ.definition σ.role blocks rest none
            (bindIds ids results (fresh mid.length e.state.st).1)
            ((afterRegions σ.rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
              σ.rules mid) { e.state with st := (fresh mid.length e.state.st).2 }).state.st
          vs ∧
        Followed (none : Option (Skel D outs)) hi ρ'
          (walk σ.rules σ.checks σ.definition σ.role blocks rest none
            (bindIds ids results (fresh mid.length e.state.st).1)
            ((afterRegions σ.rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
              σ.rules mid) { e.state with st := (fresh mid.length e.state.st).2 }).state.st) := by
    intro mids h
    obtain ⟨ρ₁, le, ex, -⟩ := h
    have valid : σ.AllValid mids := allValid_of_valuesOf ex.rets ex.coherent.valid
    obtain ⟨coh, le₂, look⟩ := leaves_fresh (s := e.state) ex.coherent (σ.sem.dyns mids) valid
    simp only [leaves, σ.sem.dyns_length] at coh look
    have inv' := afterRegions_inv laws (List.mem_singleton_self e.region) inv le ex results coh
      le₂ look
    have shows := ihr path _ _ _ _ { e.state with st := (fresh mid.length e.state.st).2 } hi hi
      inv' trivial differsR hnone nodupR
      (BoundsApart.extend (BoundsApart.sub apart fun x m => List.mem_append_right _ m)
        (by simp only [fresh]; exact ebb) atb (fun x m mr => nodup_apart nodup m mr))
      (Recorded.sub recorded fun x m => List.mem_append_right _ m)
    exact ⟨shows.1, Process.every_mono _ _ (fun vs h' => by
      obtain ⟨ρ'', le'', ex', f⟩ := h'
      exact ⟨ρ'', le.trans (le₂.trans le''), ex', f⟩) (fun _ h => h) shows.2⟩
  simp only [Shows, Term.EveryLoop, Term.denote]
  refine ⟨⟨showsB.1, Process.every_mono _ _ (fun mids h => (afterRest mids h).1)
    (fun _ _ => trivial) showsB.2⟩, ?_⟩
  rw [Process.every_bind]
  exact Process.every_mono _ _ (fun mids h => (afterRest mids h).2) (fun _ h => h) showsB.2

omit [DecidableEq Raw] in
/-- Where a region returns, of a state that grows. -/
theorem exit_grow {ρ : Valuation σ.sem.Dyn} {e : FactCheck.Exit D.Ty Raw} {st st' : St D.Ty Raw}
    {outs : List D.Ty} {vs : HList σ.sem.Val outs} (ex : ExitInv σ ρ e st vs)
    (grows : St.Grows st st') (wf : Table.WF st'.next st'.table) : ExitInv σ ρ e st' vs :=
  ⟨Coherent.grow ex.coherent grows wf, ex.rets, ex.holds⟩

include laws in
/-- An attempt: its beginning gives a valid number, which its body has at a new leaf; the end of
its body never stops `undefined`; then what is known after it, of the values its body returned
at new leaves. -/
theorem attempt_sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs mid : List D.Ty}
    (key : Key) (w : D.Who) (owns : D.Attempt w) (inputs : Names [D.index w])
    (body : Term D (Γ.extend inputs) mid) (results : Names mid)
    (rest : Term D (Γ.extend results) outs)
    (ihb : Sound σ blocks body none) (ihr : Sound σ blocks rest none) :
    Sound σ blocks (.attempt key w owns inputs body results rest) none := by
  intro path ρ ids env k s lo hi inv _ differs hnone nodup apart recorded
  simp only [walk, attemptEntry, Option.map_none, Option.isSome_none, miss_free, leaves,
    Exit.region_skel] at differs hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  have notHere := (List.nodup_cons.mp nodup).1
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupB := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  obtain ⟨⟨rb, eb⟩, ⟨nb, ebb, atb⟩, db⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks body none (bindIds ids inputs (fresh 1 s.st).1)
    ((k.addRanges (fresh 1 s.st).1 [σ.rules.range (D.index w)]).enter σ.rules [D.index w])
    { s with st := (fresh 1 s.st).2 }
  generalize he : walk σ.rules σ.checks σ.definition σ.role blocks body none
    (bindIds ids inputs (fresh 1 s.st).1)
    ((k.addRanges (fresh 1 s.st).1 [σ.rules.range (D.index w)]).enter σ.rules [D.index w])
    { s with st := (fresh 1 s.st).2 } = e at differs hnone recorded eb ebb db ⊢
  obtain ⟨⟨nr, er⟩, ⟨nbr, ebr, atr⟩, dr⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks rest none (bindIds ids results (fresh mid.length e.state.st).1)
    ((afterRegions σ.rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
      σ.rules mid)
    { e.state with st := (fresh mid.length e.state.st).2 }
  obtain ⟨differsB, differsR⟩ := differs_both db dr differs
  have refs : e.state.st.refusals = [] := refusals_before ⟨nr, er⟩ hnone
  have recB : Recorded σ (body.addresses blocks) e.state.st :=
    (Recorded.sub recorded fun x m => List.mem_cons_of_mem _ (List.mem_append_left _ m)).strip
      ebr atr (fun x m mr => nodup_apart nodup₁ m mr)
  have apartB : BoundsApart σ { s with st := (fresh 1 s.st).2 }.st (body.addresses blocks) :=
    BoundsApart.sub apart fun x m => List.mem_cons_of_mem _ (List.mem_append_left _ m)
  have apartR : BoundsApart σ { e.state with st := (fresh mid.length e.state.st).2 }.st
      (rest.addresses blocks) :=
    BoundsApart.extend (BoundsApart.sub apart fun x m =>
        List.mem_cons_of_mem _ (List.mem_append_right _ m))
      (by simp only [fresh]; exact ebb) atb (fun x m mr => nodup_apart nodup₁ m mr)
  have bodyShows : ∀ n : σ.sem.Val (D.index w), σ.Valid ⟨D.index w, n⟩ →
      Shows σ blocks body path (env.extend inputs (.cons n .nil)) (fun mids => ∃ ρ', ρ.Le ρ' ∧
        ExitInv σ ρ' e.region e.state.st mids ∧ Followed (none : Option (Skel D mid)) lo ρ'
          e.state.st) := by
    intro n valid
    have validN : σ.AllValid (HList.cons n HList.nil : HList σ.sem.Val [D.index w]) :=
      allValid_cons.mpr ⟨valid, fun _ m => nomatch m⟩
    obtain ⟨coh, le, look⟩ := leaves_fresh (s := s) inv.coherent [⟨D.index w, n⟩]
      (fun d m => by simp only [List.mem_singleton] at m; subst m; exact valid)
    simp only [leaves, List.length_singleton] at coh look
    have inv' : Inv σ (ρ.setFrom s.st.next [⟨D.index w, n⟩]) (bindIds ids inputs (fresh 1 s.st).1)
        (env.extend inputs (.cons n .nil))
        ((k.addRanges (fresh 1 s.st).1 [σ.rules.range (D.index w)]).enter σ.rules
          [D.index w]) (fresh 1 s.st).2 := by
      refine ⟨coh, agree_extend inputs (HList.cons n HList.nil) _ (inv.agree.le le) look, ?_⟩
      rw [enter_of_valid laws validN]
      exact addTypeRanges_holds laws (τs := [D.index w]) (inv.holds.le le) coh.valid
        (valuesOf_typed (vs := HList.cons n HList.nil) look)
    have shows := ihb path _ _ _ _ { s with st := (fresh 1 s.st).2 } lo lo inv' trivial
      (by rw [he]; exact differsB) (by rw [he]; exact refs) nodupB apartB
      (by rw [he]; exact recB)
    rw [he] at shows
    exact ⟨shows.1, Process.every_mono _ _ (fun vs h' => by
      obtain ⟨ρ'', le'', ex', f⟩ := h'
      exact ⟨ρ'', le.trans le'', ex', f⟩) (fun _ h => h) shows.2⟩
  have afterRest : ∀ mids : HList σ.sem.Val mid, (∃ ρ₁, ρ.Le ρ₁ ∧
      ExitInv σ ρ₁ e.region e.state.st mids ∧ Followed (none : Option (Skel D mid)) lo ρ₁
        e.state.st) →
      Shows σ blocks rest path (env.extend results mids) (fun vs => ∃ ρ', ρ.Le ρ' ∧
        ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks rest none
          (bindIds ids results (fresh mid.length e.state.st).1)
          ((afterRegions σ.rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
            σ.rules mid) { e.state with st := (fresh mid.length e.state.st).2 }).region
          (walk σ.rules σ.checks σ.definition σ.role blocks rest none
            (bindIds ids results (fresh mid.length e.state.st).1)
            ((afterRegions σ.rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
              σ.rules mid) { e.state with st := (fresh mid.length e.state.st).2 }).state.st
          vs ∧
        Followed (none : Option (Skel D outs)) hi ρ'
          (walk σ.rules σ.checks σ.definition σ.role blocks rest none
            (bindIds ids results (fresh mid.length e.state.st).1)
            ((afterRegions σ.rules [e.region] k (fresh mid.length e.state.st).1 mid 0).enter
              σ.rules mid) { e.state with st := (fresh mid.length e.state.st).2 }).state.st) := by
    intro mids h
    obtain ⟨ρ₁, le, ex, -⟩ := h
    have valid : σ.AllValid mids := allValid_of_valuesOf ex.rets ex.coherent.valid
    obtain ⟨coh, le₂, look⟩ := leaves_fresh (s := e.state) ex.coherent (σ.sem.dyns mids) valid
    simp only [leaves, σ.sem.dyns_length] at coh look
    have inv' := afterRegions_inv laws (List.mem_singleton_self e.region) inv le ex results coh
      le₂ look
    have shows := ihr path _ _ _ _ { e.state with st := (fresh mid.length e.state.st).2 } hi hi
      inv' trivial differsR hnone nodupR apartR
      (Recorded.sub recorded fun x m => List.mem_cons_of_mem _ (List.mem_append_right _ m))
    exact ⟨shows.1, Process.every_mono _ _ (fun vs h' => by
      obtain ⟨ρ'', le'', ex', f⟩ := h'
      exact ⟨ρ'', le.trans (le₂.trans le''), ex', f⟩) (fun _ h => h) shows.2⟩
  have began := laws.begin w key path
  have settled := laws.settle w key path
  simp only [Shows, Term.EveryLoop, Term.denote]
  refine ⟨Process.every_mono _ _ (fun n valid => ⟨(bodyShows n valid).1,
    Process.every_mono _ _ (fun mids h => Process.every_mono _ _
      (fun _ _ => (afterRest mids h).1) (fun _ _ => trivial) settled) (fun _ _ => trivial)
      (bodyShows n valid).2⟩) (fun _ _ => trivial) began, ?_⟩
  rw [Process.every_bind]
  refine Process.every_mono _ _ (fun n valid => ?_) (fun _ h => h) began
  rw [Process.every_bind]
  refine Process.every_mono _ _ (fun mids h => ?_) (fun _ h => h) (bodyShows n valid).2
  rw [Process.every_bind]
  exact Process.every_mono _ _ (fun _ _ => (afterRest mids h).2) (fun _ h => h) settled

include laws in
/-- A choice: the region that its condition chooses runs, with what the condition teaches; the
other region's entries are above the values; then what is known after the choice, of the values
that the region returned at new leaves, with the shapes of its results. -/
theorem choose_sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs mid : List D.Ty} {t : D.Ty}
    (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (onTrue onFalse : Term D Γ mid) (results : Names mid)
    (rest : Term D (Γ.extend results) outs)
    (iht : Sound σ blocks onTrue none) (ihf : Sound σ blocks onFalse none)
    (ihr : Sound σ blocks rest none) :
    Sound σ blocks (.choose key w c ok gives onTrue onFalse results rest) none := by
  intro path ρ ids env k s lo hi inv _ differs hnone nodup apart recorded
  have lawful : OpFacts.Lawful σ.rules.ops σ.R σ.Runs := laws.ops
  simp only [walk, chooseEntry, Option.map_none, Option.isSome_none, miss_free, leaves,
    Exit.region_skel] at differs hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  have hc := inv.agree.idOf c
  have read := laws.condition ok (env.get c) (inv.coherent.valid _ _ hc)
  generalize idOf ids c.name = cid at hc differs hnone recorded ⊢
  obtain ⟨⟨ra, ea⟩, ⟨na, eba, ata⟩, da⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks onTrue none ids (assume σ.rules.ops s.st.table s.st.next k cid true) s
  have ga := walk_grows σ.rules σ.checks σ.definition σ.role blocks onTrue none ids
    (assume σ.rules.ops s.st.table s.st.next k cid true) s inv.scoped trivial
  generalize hfirst : walk σ.rules σ.checks σ.definition σ.role blocks onTrue none ids
    (assume σ.rules.ops s.st.table s.st.next k cid true) s = first
    at differs hnone recorded ea eba da ga ⊢
  have fitsB : Scoped Γ ids first.state.st := ⟨ga.1.1, inv.scoped.2.mono ga.2.next⟩
  obtain ⟨⟨rb, eb⟩, ⟨nb, ebb, atb⟩, db⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks onFalse none ids
    (assume σ.rules.ops first.state.st.table first.state.st.next k cid false) first.state
  have gb := walk_grows σ.rules σ.checks σ.definition σ.role blocks onFalse none ids
    (assume σ.rules.ops first.state.st.table first.state.st.next k cid false) first.state
    fitsB trivial
  generalize hsecond : walk σ.rules σ.checks σ.definition σ.role blocks onFalse none ids
    (assume σ.rules.ops first.state.st.table first.state.st.next k cid false) first.state = second
    at differs hnone recorded eb ebb db gb ⊢
  obtain ⟨⟨nr, er⟩, ⟨nbr, ebr, atr⟩, dr⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks rest none (bindIds ids results (fresh mid.length second.state.st).1)
    ((afterChoice σ.rules k cid first.region second.region
      (fresh mid.length second.state.st).1 mid).enter σ.rules mid)
    { second.state with st := (fresh mid.length second.state.st).2 }
  obtain ⟨differsA, differsB, differsR⟩ := differs_three da db dr differs
  have refsB : second.state.st.refusals = [] := refusals_before ⟨nr, er⟩ hnone
  have refsA : first.state.st.refusals = [] := refusals_before ⟨rb, eb⟩ refsB
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupAB := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  have nodupA := (List.nodup_append.mp nodupAB).1
  have nodupB := (List.nodup_append.mp nodupAB).2.1
  have apartR : BoundsApart σ { second.state with st := (fresh mid.length second.state.st).2 }.st
      (rest.addresses blocks) :=
    (((BoundsApart.sub apart fun x m => by simp [m]).extend eba ata (fun x m mr =>
      nodup_apart nodup₁ (List.mem_append_left _ m) mr)).extend ebb atb
      (fun x m mr => nodup_apart nodup₁ (List.mem_append_right _ m) mr) :)
  -- the rest, after either region
  have afterRest : ∀ (b0 : Bool) (ran : FactCheck.Exit D.Ty Raw),
      ran ∈ [first.region, second.region] →
      ran = (if b0 then first.region else second.region) → σ.sem.holds ok (env.get c) = b0 →
      ∀ (ρ₁ : Valuation σ.sem.Dyn) (mids : HList σ.sem.Val mid), ρ.Le ρ₁ →
        ExitInv σ ρ₁ ran second.state.st mids →
        Shows σ blocks rest path (env.extend results mids) (fun vs => ∃ ρ', ρ.Le ρ' ∧
          ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks rest none
            (bindIds ids results (fresh mid.length second.state.st).1)
            ((afterChoice σ.rules k cid first.region second.region
              (fresh mid.length second.state.st).1 mid).enter σ.rules mid)
            { second.state with st := (fresh mid.length second.state.st).2 }).region
            (walk σ.rules σ.checks σ.definition σ.role blocks rest none
              (bindIds ids results (fresh mid.length second.state.st).1)
              ((afterChoice σ.rules k cid first.region second.region
                (fresh mid.length second.state.st).1 mid).enter σ.rules mid)
              { second.state with st := (fresh mid.length second.state.st).2 }).state.st vs ∧
          Followed (none : Option (Skel D outs)) hi ρ'
            (walk σ.rules σ.checks σ.definition σ.role blocks rest none
              (bindIds ids results (fresh mid.length second.state.st).1)
              ((afterChoice σ.rules k cid first.region second.region
                (fresh mid.length second.state.st).1 mid).enter σ.rules mid)
              { second.state with st := (fresh mid.length second.state.st).2 }).state.st) := by
    intro b0 ran mem eran hb0 ρ₁ mids le ex
    have valid : σ.AllValid mids := allValid_of_valuesOf ex.rets ex.coherent.valid
    obtain ⟨coh, le₂, look⟩ := leaves_fresh (s := second.state) ex.coherent (σ.sem.dyns mids)
      valid
    simp only [leaves, σ.sem.dyns_length] at coh look
    have inv' := afterRegions_inv laws mem inv le ex results coh le₂ look
    have choices := choiceFacts_holds (first := first.region) (second := second.region) lawful
      inv'.coherent.consistent inv'.coherent.closed (b0 := b0)
      ⟨_, (le.trans le₂) _ _ hc, by rw [read, hb0]⟩ (fresh mid.length second.state.st).1 0 (by
        intro j m em
        have e1 := valuesOf_getElem look em
        cases hd : (σ.sem.dyns mids)[j]? with
        | none => rw [hd] at e1; exact absurd e1 (valuesOf_mem look m (List.mem_of_getElem? em))
        | some d =>
            rw [hd] at e1
            refine ⟨d, e1, ?_⟩
            rw [← eran, Nat.zero_add]
            have lt : j < ran.rets.length := by
              have h1 := valuesOf_length ex.rets
              have h2 := (List.getElem?_eq_some_iff.mp hd).1
              omega
            rw [le₂ _ _ (by rw [valuesOf_get ex.rets j lt, hd])])
    have inv'' : Inv σ (ρ₁.setFrom second.state.st.next (σ.sem.dyns mids))
        (bindIds ids results (fresh mid.length second.state.st).1) (env.extend results mids)
        ((afterChoice σ.rules k cid first.region second.region
          (fresh mid.length second.state.st).1 mid).enter σ.rules mid)
        (fresh mid.length second.state.st).2 := by
      refine ⟨inv'.coherent, inv'.agree, ?_⟩
      have holds := inv'.holds
      rw [enter_of_valid laws valid] at holds ⊢
      exact Known.Holds.addChoices holds choices
    have shows := ihr path _ _ _ _ { second.state with st := (fresh mid.length second.state.st).2 }
      hi hi inv'' trivial differsR hnone nodupR apartR
      (Recorded.sub recorded fun x m => by simp [m])
    exact ⟨shows.1, Process.every_mono _ _ (fun vs h' => by
      obtain ⟨ρ'', le'', ex', f⟩ := h'
      exact ⟨ρ'', le.trans (le₂.trans le''), ex', f⟩) (fun _ h => h) shows.2⟩
  simp only [Shows, Term.EveryLoop, Term.denote]
  cases hv : σ.sem.holds ok (env.get c) with
  | true =>
      have hcv : BoolAt σ.R ρ cid true := ⟨_, hc, by rw [read, hv]⟩
      have kt : (assume σ.rules.ops s.st.table s.st.next k cid true).Holds σ.R ρ :=
        assume_holds lawful inv.coherent.consistent inv.coherent.closed s.st.next inv.holds hcv
      have recA : Recorded σ (onTrue.addresses blocks) first.state.st :=
        ((Recorded.sub recorded fun x m => by simp [m]).strip ebr atr (fun x m mr =>
          nodup_apart nodup₁ (List.mem_append_left _ m) mr)).strip ebb atb
          (fun x m mr => nodup_apart nodupAB m mr)
      have showsT := iht path ρ ids env _ s lo lo ⟨inv.coherent, inv.agree, kt⟩ trivial
        (by rw [hfirst]; exact differsA) (by rw [hfirst]; exact refsA) nodupA
        (BoundsApart.sub apart fun x m => by simp [m]) (by rw [hfirst]; exact recA)
      rw [hfirst] at showsT
      simp only [Bool.cond_true]
      refine ⟨⟨showsT.1, ?_⟩, ?_⟩
      · refine Process.every_mono _ _ ?_ (fun _ _ => trivial) showsT.2
        intro mids h
        obtain ⟨ρ₁, le, ex, -⟩ := h
        exact (afterRest true first.region (by simp) rfl hv ρ₁ mids le
          (exit_grow ex gb.2 gb.1.1)).1
      · rw [Process.every_bind]
        refine Process.every_mono _ _ ?_ (fun _ h => h) showsT.2
        intro mids h
        obtain ⟨ρ₁, le, ex, -⟩ := h
        exact (afterRest true first.region (by simp) rfl hv ρ₁ mids le
          (exit_grow ex gb.2 gb.1.1)).2
  | false =>
      have coh₁ := Coherent.grow inv.coherent ga.2 ga.1.1
      have hcv : BoolAt σ.R ρ cid false := ⟨_, hc, by rw [read, hv]⟩
      have kf : (assume σ.rules.ops first.state.st.table first.state.st.next k cid false).Holds
          σ.R ρ :=
        assume_holds lawful coh₁.consistent coh₁.closed first.state.st.next inv.holds hcv
      have recB : Recorded σ (onFalse.addresses blocks) second.state.st :=
        (Recorded.sub recorded fun x m => by simp [m]).strip ebr atr (fun x m mr =>
          nodup_apart nodup₁ (List.mem_append_right _ m) mr)
      have apartB : BoundsApart σ first.state.st (onFalse.addresses blocks) :=
        (BoundsApart.sub apart fun x m => by simp [m]).extend eba ata
          (fun x m mr => nodup_apart nodupAB m mr)
      have showsF := ihf path ρ ids env _ first.state lo lo ⟨coh₁, inv.agree, kf⟩ trivial
        (by rw [hsecond]; exact differsB) (by rw [hsecond]; exact refsB) nodupB apartB
        (by rw [hsecond]; exact recB)
      rw [hsecond] at showsF
      simp only [Bool.cond_false]
      refine ⟨⟨showsF.1, ?_⟩, ?_⟩
      · refine Process.every_mono _ _ ?_ (fun _ _ => trivial) showsF.2
        intro mids h
        obtain ⟨ρ₁, le, ex, -⟩ := h
        exact (afterRest false second.region (by simp) rfl hv ρ₁ mids le ex).1
      · rw [Process.every_bind]
        refine Process.every_mono _ _ ?_ (fun _ h => h) showsF.2
        intro mids h
        obtain ⟨ρ₁, le, ex, -⟩ := h
        exact (afterRest false second.region (by simp) rfl hv ρ₁ mids le ex).2

theorem armsNil_sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {mid : List D.Ty} :
    ArmsSound σ blocks (.nil : Arms D Γ mid []) none :=
  fun _ _ _ _ _ _ _ _ p => nomatch p

include laws in
/-- The arms of a case analysis, when no skeleton is followed: the arm of the alternative runs,
with its payload at a new leaf; the other arms' entries are above the values. -/
theorem armsCons_sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
    {payload : D.Ty} (inputs : Names [payload]) (arm : Term D (Γ.extend inputs) mid)
    (rest : Arms D Γ mid payloads) (iha : Sound σ blocks arm none)
    (ihr : ArmsSound σ blocks rest none) :
    ArmsSound σ blocks (.cons inputs arm rest) none := by
  intro path ρ ids env k s lo hi p valid inv _ differs hnone nodup apart recorded
  simp only [walkArms, armEntry, Option.map_none, leaves, Option.getD_none]
    at differs hnone recorded ⊢
  simp only [Arms.addresses] at nodup apart recorded
  obtain ⟨⟨ra, ea⟩, ⟨na, eba, ata⟩, da⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks arm none (bindIds ids inputs (fresh 1 s.st).1)
    ((k.addRanges (fresh 1 s.st).1 [σ.rules.range payload]).enter σ.rules [payload])
    { s with st := (fresh 1 s.st).2 }
  obtain ⟨wfi, gi, lti⟩ := fresh_grows 1 s.st inv.coherent.wf
  have ga := walk_grows σ.rules σ.checks σ.definition σ.role blocks arm none
    (bindIds ids inputs (fresh 1 s.st).1)
    ((k.addRanges (fresh 1 s.st).1 [σ.rules.range payload]).enter σ.rules [payload])
    { s with st := (fresh 1 s.st).2 }
    ⟨wfi, (inv.scoped.2.mono gi.next).bind inputs _ (by simp [fresh]) lti⟩ trivial
  generalize he : walk σ.rules σ.checks σ.definition σ.role blocks arm none
    (bindIds ids inputs (fresh 1 s.st).1)
    ((k.addRanges (fresh 1 s.st).1 [σ.rules.range payload]).enter σ.rules [payload])
    { s with st := (fresh 1 s.st).2 } = e at differs hnone recorded ea eba da ga ⊢
  obtain ⟨⟨rr, er⟩, ⟨nr, ebr, atr⟩, dr⟩ := walkArms_adds σ.rules σ.checks σ.definition σ.role
    blocks rest none ids k e.state
  have growsE : St.Grows s.st e.state.st := gi.trans ga.2
  have gr := walkArms_grows σ.rules σ.checks σ.definition σ.role blocks rest none ids k e.state
    ⟨ga.1.1, inv.scoped.2.mono growsE.next⟩ trivial
  obtain ⟨differsA, differsR⟩ := differs_both da dr differs
  have refsE : e.state.st.refusals = [] := refusals_before ⟨rr, er⟩ hnone
  have nodupA := (List.nodup_append.mp nodup).1
  have nodupR := (List.nodup_append.mp nodup).2.1
  cases p with
  | here v =>
      have validV : σ.AllValid (HList.cons v HList.nil : HList σ.sem.Val [payload]) :=
        allValid_cons.mpr ⟨valid, fun _ m => nomatch m⟩
      obtain ⟨coh, le, look⟩ := leaves_fresh (s := s) inv.coherent [⟨payload, v⟩]
        (fun d m => by simp only [List.mem_singleton] at m; subst m; exact valid)
      simp only [leaves, List.length_singleton] at coh look
      have inv' : Inv σ (ρ.setFrom s.st.next [⟨payload, v⟩]) (bindIds ids inputs (fresh 1 s.st).1)
          (env.extend inputs (.cons v .nil))
          ((k.addRanges (fresh 1 s.st).1 [σ.rules.range payload]).enter σ.rules [payload])
          (fresh 1 s.st).2 := by
        refine ⟨coh, agree_extend inputs (HList.cons v HList.nil) _ (inv.agree.le le) look, ?_⟩
        rw [enter_of_valid laws validV]
        exact addTypeRanges_holds laws (τs := [payload]) (inv.holds.le le) coh.valid
          (valuesOf_typed (vs := HList.cons v HList.nil) look)
      have recA : Recorded σ (arm.addresses blocks) e.state.st :=
        (Recorded.sub recorded fun x m => List.mem_append_left _ m).strip ebr atr
          (fun x m mr => nodup_apart nodup m mr)
      have shows := iha path _ _ _ _ { s with st := (fresh 1 s.st).2 } lo lo inv' trivial
        (by rw [he]; exact differsA) (by rw [he]; exact refsE) nodupA
        (BoundsApart.sub apart fun x m => List.mem_append_left _ m) (by rw [he]; exact recA)
      rw [he] at shows
      refine ⟨shows.1, Process.every_mono _ _ ?_ (fun _ h => h) shows.2⟩
      intro mids h
      obtain ⟨ρ₁, le₁, ex, -⟩ := h
      exact ⟨ρ₁, le.trans le₁, e.region, List.mem_cons_self, exit_grow ex gr.2.2 gr.2.1.1, trivial⟩
  | there p =>
      have apartR : BoundsApart σ e.state.st (Arms.addresses blocks rest) :=
        (BoundsApart.sub apart fun x m => List.mem_append_right _ m).extend
          (by rw [eba]; rfl) ata (fun x m mr => nodup_apart nodup m mr)
      have shows := ihr path ρ ids env k e.state lo hi p valid
        ⟨Coherent.grow inv.coherent growsE ga.1.1, inv.agree, inv.holds⟩ trivial
        differsR hnone nodupR apartR (Recorded.sub recorded fun x m => List.mem_append_right _ m)
      refine ⟨shows.1, Process.every_mono _ _ ?_ (fun _ h => h) shows.2⟩
      intro mids h
      obtain ⟨ρ₁, le₁, e', m, ex, -⟩ := h
      exact ⟨ρ₁, le₁, e', List.mem_cons_of_mem _ m, ex, trivial⟩

include laws in
/-- A case analysis, when no skeleton is followed: the arm of the alternative of its subject
runs; then what is known after it, of the values the arm returned at new leaves. -/
theorem cases_sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs mid payloads : List D.Ty}
    {t : D.Ty} (key : Key) (w : D.Who) (x : Var Γ t) (ok : D.Alternatives w t payloads)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (arms : Arms D Γ mid payloads) (results : Names mid)
    (rest : Term D (Γ.extend results) outs) (iha : ArmsSound σ blocks arms none)
    (ihr : Sound σ blocks rest none) :
    Sound σ blocks (.cases key w x ok gives arms results rest) none := by
  intro path ρ ids env k s lo hi inv _ differs hnone nodup apart recorded
  simp only [walk, casesEntry, Option.map_none, Option.isSome_none, miss_free, leaves,
    Exit.region_skel] at differs hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  obtain ⟨⟨ra, ea⟩, ⟨na, eba, ata⟩, da⟩ := walkArms_adds σ.rules σ.checks σ.definition σ.role
    blocks arms none ids k s
  generalize hregions : walkArms σ.rules σ.checks σ.definition σ.role blocks arms none ids k s =
    regions at differs hnone recorded ea eba da ⊢
  obtain ⟨⟨rr, er⟩, ⟨nr, ebr, atr⟩, dr⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks rest none (bindIds ids results (fresh mid.length regions.state.st).1)
    ((afterRegions σ.rules regions.exits k (fresh mid.length regions.state.st).1 mid
      0).enter σ.rules mid)
    { regions.state with st := (fresh mid.length regions.state.st).2 }
  obtain ⟨differsA, differsR⟩ := differs_both da dr differs
  have refsR : regions.state.st.refusals = [] := refusals_before ⟨rr, er⟩ hnone
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupA := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  have valid := agree_valid inv.agree inv.coherent.valid
  have recA : Recorded σ (Arms.addresses blocks arms) regions.state.st :=
    (Recorded.sub recorded fun x m => by simp [m]).strip ebr atr
      (fun x m mr => nodup_apart nodup₁ m mr)
  have shows := iha path ρ ids env k s lo lo _ (laws.pick ok (env.get x) (valid t x)) inv trivial
    (by rw [hregions]; exact differsA) (by rw [hregions]; exact refsR) nodupA
    (BoundsApart.sub apart fun x m => by simp [m]) (by rw [hregions]; exact recA)
  rw [hregions] at shows
  have apartR : BoundsApart σ { regions.state with st := (fresh mid.length regions.state.st).2 }.st
      (rest.addresses blocks) :=
    (BoundsApart.sub apart fun x m => by simp [m]).extend eba ata
      (fun x m mr => nodup_apart nodup₁ m mr)
  have afterRest : ∀ (mids : HList σ.sem.Val mid), (∃ ρ', ρ.Le ρ' ∧ ∃ e, e ∈ regions.exits ∧
      ExitInv σ ρ' e regions.state.st mids ∧
        ArmsFollowed (none : Option (SkelArms D mid payloads)) lo ρ' regions.state.st) →
      Shows σ blocks rest path (env.extend results mids) (fun vs => ∃ ρ', ρ.Le ρ' ∧
        ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks rest none
          (bindIds ids results (fresh mid.length regions.state.st).1)
          ((afterRegions σ.rules regions.exits k (fresh mid.length regions.state.st).1 mid
            0).enter σ.rules mid)
          { regions.state with st := (fresh mid.length regions.state.st).2 }).region
          (walk σ.rules σ.checks σ.definition σ.role blocks rest none
            (bindIds ids results (fresh mid.length regions.state.st).1)
            ((afterRegions σ.rules regions.exits k (fresh mid.length regions.state.st).1 mid
              0).enter σ.rules mid)
            { regions.state with st := (fresh mid.length regions.state.st).2 }).state.st vs ∧
        Followed (none : Option (Skel D outs)) hi ρ'
          (walk σ.rules σ.checks σ.definition σ.role blocks rest none
            (bindIds ids results (fresh mid.length regions.state.st).1)
            ((afterRegions σ.rules regions.exits k (fresh mid.length regions.state.st).1 mid
              0).enter σ.rules mid)
            { regions.state with st := (fresh mid.length regions.state.st).2 }).state.st) := by
    intro mids h
    obtain ⟨ρ₁, le, e, he, ex, -⟩ := h
    have validM : σ.AllValid mids := allValid_of_valuesOf ex.rets ex.coherent.valid
    obtain ⟨coh, le₂, look⟩ := leaves_fresh (s := regions.state) ex.coherent (σ.sem.dyns mids)
      validM
    simp only [leaves, σ.sem.dyns_length] at coh look
    have inv' := afterRegions_inv laws he inv le ex results coh le₂ look
    have shows' := ihr path _ _ _ _ { regions.state with st := (fresh mid.length regions.state.st).2 }
      hi hi inv' trivial differsR hnone nodupR apartR (Recorded.sub recorded fun x m => by simp [m])
    exact ⟨shows'.1, Process.every_mono _ _ (fun vs h' => by
      obtain ⟨ρ'', le'', ex', f⟩ := h'
      exact ⟨ρ'', le.trans (le₂.trans le''), ex', f⟩) (fun _ h => h) shows'.2⟩
  simp only [Shows, Term.EveryLoop, Term.denote]
  refine ⟨⟨shows.1, ?_⟩, ?_⟩
  · exact Process.every_mono _ _ (fun mids h => (afterRest mids h).1) (fun _ _ => trivial) shows.2
  · rw [Process.every_bind]
    exact Process.every_mono _ _ (fun mids h => (afterRest mids h).2) (fun _ h => h) shows.2

/-! ### Loops -/

include laws in
omit [DecidableEq Raw] in
/-- The value of the count of a loop as often as a count reads as the number of iterations. -/
theorem count_at {Γ : Ctx D.Ty} {ρ : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} (agree : Agree σ ρ ids env)
    (valid : ∀ i v, ρ i = some v → σ.Valid v) {w : D.Who} {t : D.Ty} (count : Var Γ t)
    (ok : D.Count w t) :
    NatAt σ.R ρ (idOf ids count.name) (σ.sem.times (Times.value count ok) env) := by
  have hc := agree.idOf count
  exact ⟨_, hc, laws.count ok (env.get count) (valid _ _ hc)⟩

include laws in
omit [DecidableEq Raw] in
/-- How often a loop runs is at most the bound that the walk computes. -/
theorem timesBound_ok {Γ : Ctx D.Ty} {ρ : Valuation σ.sem.Dyn} {ids : Ctx Nat}
    {env : Env σ.sem.Val Γ} {k : Known} (hk : k.Holds σ.R ρ) (agree : Agree σ ρ ids env)
    (valid : ∀ i v, ρ i = some v → σ.Valid v) {w : D.Who} (times : Times D w Γ) :
    ∀ m, timesBound k ids times = some m → σ.sem.times times env ≤ m := by
  cases times with
  | fixed n =>
      intro m e
      simp only [timesBound, Option.some.injEq] at e
      subst e
      exact Nat.le_refl _
  | value count ok =>
      intro m e
      simp only [timesBound] at e
      cases hr : k.rangeOf (idOf ids count.name) with
      | none => rw [hr] at e; cases e
      | some r =>
          rw [hr] at e
          simp only [Option.bind_some] at e
          exact (hk.rangeOf_at (count_at laws agree valid count ok) hr).2 m e

include laws in
omit [DecidableEq Raw] in
/-- What is known in the body of a loop holds at an iteration below its count. -/
theorem bodyKnown_holds {Γ : Ctx D.Ty} {carried : List D.Ty} {ρ : Valuation σ.sem.Dyn}
    {ids : Ctx Nat} {env : Env σ.sem.Val Γ} {k : Known} (hk : k.Holds σ.R ρ)
    (agree : Agree σ ρ ids env) (valid : ∀ i v, ρ i = some v → σ.Valid v) {w : D.Who}
    (times : Times D w Γ) {i index : Nat} (lt : i < σ.sem.times times env)
    (hi : ρ index = some ⟨D.index w, σ.sem.index w i⟩) {carriedIds : List Nat}
    {vs : HList σ.sem.Val carried} (look : valuesOf ρ carriedIds = some (σ.sem.dyns vs)) :
    (bodyKnown σ.rules k ids times index carriedIds carried).Holds σ.R ρ := by
  have hindex : NatAt σ.R ρ index i := ⟨_, hi, (laws.index w i).2⟩
  have k₁ : ((k.addRange index (indexRange k ids times)).addRange? index
      (σ.rules.range (D.index w))).Holds σ.R ρ := by
    refine (hk.addRange hindex ?_).addRange? fun r e => ⟨i, hindex, ?_⟩
    · cases times with
      | fixed n =>
          exact (Range.has_point.mpr rfl : (Range.point n).Has n).below lt
      | value count ok =>
          simp only [indexRange]
          cases hr : k.rangeOf (idOf ids count.name) with
          | none => exact ⟨Nat.zero_le _, fun _ e => nomatch e⟩
          | some r => exact (hk.rangeOf_at (count_at laws agree valid count ok) hr).below lt
    · obtain ⟨n, hn, has⟩ := laws.range (D.index w) r (σ.sem.index w i) e (laws.index w i).1
      rw [(laws.index w i).2] at hn
      cases hn
      exact has
  have carriedOK : ∀ (j m : Nat), carriedIds[j]? = some m →
      ∃ d, ρ m = some d ∧ carried[j]? = some d.1 := valuesOf_typed look
  have validCarried : σ.AllValid vs := allValid_of_valuesOf look valid
  have entered : ∀ k' : Known, k'.enter σ.rules (D.index w :: carried) = k' :=
    fun _ => enter_of_valid laws (vs := HList.cons (σ.sem.index w i) vs)
      (allValid_cons.mpr ⟨(laws.index w i).1, validCarried⟩)
  cases times with
  | fixed n =>
      cases n with
      | zero => exact absurd lt (Nat.not_lt_zero _)
      | succ n =>
          simp only [bodyKnown]
          rw [entered]
          exact addTypeRanges_holds laws k₁ valid carriedOK
  | value count ok =>
      simp only [bodyKnown]
      rw [entered]
      exact addTypeRanges_holds laws (k₁.addOrder hindex (count_at laws agree valid count ok)
        (by simpa using lt)) valid carriedOK

omit [DecidableEq Raw] in
/-- The bound that a loop records is its count's upper end. -/
theorem recordBound_mem {Γ : Ctx D.Ty} {place : Place} {k : Known} {ids : Ctx Nat}
    {st : St D.Ty Raw} {w : D.Who} {times : Times D w Γ} {q : Place × Nat}
    (m : q ∈ (recordBound place k ids st times).bounds) :
    q ∈ st.bounds ∨ ∃ t, ∃ count : Var Γ t, ∃ ok, times = .value count ok ∧ q.1 = place ∧
      (k.rangeOf (idOf ids count.name)).bind (·.hi) = some q.2 := by
  cases times with
  | fixed => exact Or.inl m
  | value count ok =>
      simp only [recordBound] at m
      split at m
      · next bound e =>
          rcases List.mem_cons.mp m with rfl | m
          · exact Or.inr ⟨_, count, ok, rfl, rfl, e⟩
          · exact Or.inl m
      · exact Or.inl m

include laws in
omit [DecidableEq Raw] in
/-- The base of what is known after a loop: what the types of the collected values say. -/
theorem afterLoop_holds {e : FactCheck.Exit D.Ty Raw} {iters : Option Nat}
    {ρ : Valuation σ.sem.Dyn} (valid : ∀ i v, ρ i = some v → σ.Valid v) :
    ∀ (ms : List Nat) (initials : List (Option Range)) (carriedIds returns : List Nat)
      (τs : List D.Ty) (k : Known), k.Holds σ.R ρ →
      (∀ (j m : Nat), ms[j]? = some m → ∃ d, ρ m = some d ∧ τs[j]? = some d.1 ∧
        ∀ initial cid ret, initials[j]? = some initial → carriedIds[j]? = some cid →
          returns[j]? = some ret → ∀ r,
            carriedRange σ.rules.ops e initial cid ret iters = some r →
            ∃ n, σ.R.nat d = some n ∧ r.Has n) →
      (afterLoop σ.rules e k iters ms initials carriedIds returns τs).Holds σ.R ρ := by
  intro ms
  induction ms with
  | nil =>
      intro initials carriedIds returns τs k hk _
      simp only [afterLoop]
      exact hk
  | cons m ms ih =>
      intro initials carriedIds returns τs k hk h
      have base : (k.addRanges (m :: ms) (τs.map σ.rules.range)).Holds σ.R ρ :=
        addTypeRanges_holds laws hk valid fun j m' e => by
          obtain ⟨d, hd, hτ, _⟩ := h j m' e
          exact ⟨d, hd, hτ⟩
      cases initials with
      | nil => exact base
      | cons initial initials =>
          cases carriedIds with
          | nil => exact base
          | cons cid cids =>
              cases returns with
              | nil => exact base
              | cons ret rets =>
                  cases τs with
                  | nil => exact base
                  | cons τ τs =>
                      simp only [afterLoop]
                      obtain ⟨d, hd, hτ, hr⟩ := h 0 m rfl
                      simp only [List.getElem?_cons_zero, Option.some.injEq] at hτ
                      subst hτ
                      apply ih initials cids rets τs
                      · refine (hk.addRange? fun r e1 => ?_).addRange? fun r e2 => ?_
                        · obtain ⟨n, hn, has⟩ := hr initial cid ret rfl rfl rfl r e1
                          exact ⟨n, ⟨d, hd, hn⟩, has⟩
                        · obtain ⟨n, hn, has⟩ := laws.range d.1 r d.2 e2 (valid m d hd)
                          exact ⟨n, ⟨d, hd, hn⟩, has⟩
                      · intro j m' e'
                        obtain ⟨d', h1, h2, h3⟩ := h (j + 1) m' (by simpa using e')
                        exact ⟨d', h1, by simpa using h2, fun a b c ea eb ec =>
                          h3 a b c (by simpa using ea) (by simpa using eb) (by simpa using ec)⟩

omit [DecidableEq Raw] in
/-- What the walk knows of a carried natural after a loop holds of its last value. -/
theorem carriedRange_has {e : FactCheck.Exit D.Ty Raw} {iters : Option Nat}
    {initial : Option Range} {cid ret N : Nat} {v : σ.sem.Dyn}
    (highOK : ∀ m, iters = some m → N ≤ m)
    (alive : 0 < N → e.known.dead = false)
    (initialOK : N = 0 → ∀ r, initial = some r → ∃ n, σ.R.nat v = some n ∧ r.Has n)
    (sumOK : ∀ r₀ t rt, initial = some r₀ →
      carriedTerm σ.rules.ops e cid ret = some t → e.known.rangeOf t = some rt →
      ∃ n, σ.R.nat v = some n ∧ (Range.afterSums r₀ rt (some N)).Has n) :
    ∀ r, carriedRange σ.rules.ops e initial cid ret iters = some r →
      ∃ n, σ.R.nat v = some n ∧ r.Has n := by
  intro r hr
  simp only [carriedRange] at hr
  split at hr
  · next none =>
      have : N = 0 := by
        simp only [Bool.or_eq_true, decide_eq_true_eq] at none
        rcases none with dead | zero
        · rcases Nat.eq_zero_or_pos N with h | h
          · exact h
          · have := alive h
            rw [this] at dead
            cases dead
        · have := highOK 0 zero
          omega
      exact initialOK this r hr
  · cases ht : carriedTerm σ.rules.ops e cid ret with
    | none => simp [ht] at hr
    | some t =>
        cases hi : initial with
        | none => simp [ht, hi] at hr
        | some r₀ =>
            simp only [ht, hi] at hr
            cases hrt : e.known.rangeOf t with
            | none => rw [hrt] at hr; cases hr
            | some rt =>
                rw [hrt] at hr
                simp only [Option.map_some, Option.some.injEq] at hr
                subst hr
                obtain ⟨n, hn, has⟩ := sumOK r₀ t rt hi ht hrt
                exact ⟨n, hn, Range.afterSums_widen has highOK⟩

omit [DecidableEq Raw] in
theorem carriedTerm_spec {e : FactCheck.Exit D.Ty Raw} {cid ret t : Nat}
    (h : carriedTerm σ.rules.ops e cid ret = some t) :
    ∃ x y, e.st.table.formOf σ.rules.ops ret = some (.sum, [x, y]) ∧
      ((x = cid ∧ t = y) ∨ (y = cid ∧ t = x)) := by
  simp only [carriedTerm] at h
  split at h
  · next x y hform =>
      refine ⟨x, y, hform, ?_⟩
      by_cases hx : x = cid
      · simp only [hx, ↓reduceIte, Option.some.injEq] at h
        exact Or.inl ⟨hx, h.symm⟩
      · by_cases hy : y = cid
        · simp only [hx, hy, ↓reduceIte, Option.some.injEq] at h
          exact Or.inr ⟨hy, h.symm⟩
        · simp [hx, hy] at h
  · cases h

theorem valuesOf_tail {Val : Type} {ρ : Valuation Val} {i : Nat} {is : List Nat} {v : Val}
    {vs : List Val} (h : valuesOf ρ (i :: is) = some (v :: vs)) : valuesOf ρ is = some vs := by
  simp only [valuesOf] at h
  split at h
  · next w ws _ e2 =>
      simp only [Option.some.injEq, List.cons.injEq] at h
      rw [e2, h.2]
  · cases h

/-- What holds at an iteration of a loop: the carried values are valid, as many collected values
as iterations, the body's end was reached when an iteration was, the carried values are the
initial ones before any iteration, and each carried natural that the body returns as itself plus
a term has the range of the sum so far. -/
structure LoopAt (e : FactCheck.Exit D.Ty Raw) (initials : List (Option Range))
    (carriedIds : List Nat) {carried each : List D.Ty} (init0 : HList σ.sem.Val carried) (i : Nat)
    (state : HList σ.sem.Val carried × HList (fun a => List (σ.sem.Val a)) each) : Prop where
  carriedValid : σ.AllValid state.1
  collected : CollectedOK σ.sem σ.Valid state.2 i
  alive : 0 < i → e.known.dead = false
  initial : i = 0 → state.1 = init0
  sums : ∀ (j : Nat) (r₀ : Range) (t : Nat) (rt : Range), initials[j]? = some (some r₀) →
    carriedTerm σ.rules.ops e (carriedIds.getD j 0) (e.rets.getD j 0) = some t →
    e.known.rangeOf t = some rt → ∃ d n, (σ.sem.dyns state.1)[j]? = some d ∧
      σ.R.nat d = some n ∧ (Range.afterSums r₀ rt (some i)).Has n

include laws in
/-- A loop, when no skeleton is followed: each iteration starts from the valuation before the
loop, with its number and the carried values at the leaves of the body, and keeps what holds at
an iteration; after the last, the carried naturals have the range of their sums, and the loop has
run at most as often as the bound recorded for it. -/
theorem loop_sound (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs carried each : List D.Ty}
    (key : Key) (w : D.Who) (times : Times D w Γ)
    (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (init : HList (Var Γ) carried)
    (inputs : Names (D.index w :: carried)) (body : Term D (Γ.extend inputs) (carried ++ each))
    (results : Names (carried ++ each.map (D.collected times.size)))
    (rest : Term D (Γ.extend results) outs)
    (ihb : Sound σ blocks body none) (ihr : Sound σ blocks rest none) :
    Sound σ blocks (.loop key w times gives init inputs body results rest) none := by
  intro path ρ ids env k s lo hi inv _ differs hnone nodup apart recorded
  have lawful : OpFacts.Lawful σ.rules.ops σ.R σ.Runs := laws.ops
  simp only [walk, loopEntry, Option.map_none, Option.isSome_none, miss_free, leaves,
    Exit.region_skel] at differs hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  have notHere := (List.nodup_cons.mp nodup).1
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupB := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  have fitsIn := fresh_grows (carried.length + 1) s.st inv.coherent.wf
  generalize hin : fresh (carried.length + 1) s.st = inBody at differs hnone recorded fitsIn ⊢
  have in1 : inBody.1 = List.range' s.st.next (carried.length + 1) := by rw [← hin]; rfl
  have in2next : inBody.2.next = s.st.next + (carried.length + 1) := by rw [← hin]; rfl
  have in2table : inBody.2.table = s.st.table := by rw [← hin]; rfl
  have in2bounds : inBody.2.bounds = s.st.bounds := by rw [← hin]; rfl
  have headIn : inBody.1.headD 0 = s.st.next := by rw [in1, List.range'_succ]; rfl
  have tailIn : inBody.1.tail = List.range' (s.st.next + 1) carried.length := by
    rw [in1, List.range'_succ]; rfl
  have scopeB : Scoped (Γ.extend inputs) (bindIds ids inputs inBody.1) inBody.2 :=
    ⟨fitsIn.1, (inv.scoped.2.mono fitsIn.2.1.next).bind inputs inBody.1 (by simp [in1])
      fitsIn.2.2⟩
  obtain ⟨⟨rb, eb⟩, ⟨nb, ebb, atb⟩, db⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks body none (bindIds ids inputs inBody.1)
    (bodyKnown σ.rules k ids times (inBody.1.headD 0) inBody.1.tail carried)
    { s with st := inBody.2 }
  have gb := walk_grows σ.rules σ.checks σ.definition σ.role blocks body none
    (bindIds ids inputs inBody.1)
    (bodyKnown σ.rules k ids times (inBody.1.headD 0) inBody.1.tail carried)
    { s with st := inBody.2 } scopeB trivial
  generalize he : walk σ.rules σ.checks σ.definition σ.role blocks body none
    (bindIds ids inputs inBody.1)
    (bodyKnown σ.rules k ids times (inBody.1.headD 0) inBody.1.tail carried)
    { s with st := inBody.2 } = e at differs hnone recorded eb ebb db gb ⊢
  have rbs := recordBound_state (D := D) ⟨σ.definition, blocks, some key, σ.role⟩ k ids
    e.state.st times
  generalize hst₁ : recordBound ⟨σ.definition, blocks, some key, σ.role⟩ k ids e.state.st times =
    st₁ at differs hnone recorded rbs ⊢
  obtain ⟨rbt, rbn, rbr, nbd, ebd, atd⟩ := rbs
  generalize hmade : fresh (carried.length + each.length) st₁ = made at differs hnone recorded ⊢
  have m2b : made.2.bounds = st₁.bounds := by rw [← hmade]; rfl
  have m2t : made.2.table = st₁.table := by rw [← hmade]; rfl
  have m1 : made.1 = List.range' st₁.next (carried.length + each.length) := by
    rw [← hmade]; rfl
  obtain ⟨⟨rr, er⟩, ⟨nbr, ebr, atr⟩, dr⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks rest none (bindIds ids results made.1)
    ((afterLoop σ.rules e.region k (timesBound k ids times) made.1
      ((idsOf ids init).map k.rangeOf) inBody.1.tail e.rets
      (carried ++ each.map (D.collected times.size))).enter σ.rules
      (carried ++ each.map (D.collected times.size))) { e.state with st := made.2 }
  obtain ⟨differsB, differsR⟩ := differs_both db dr differs
  have refsE : e.state.st.refusals = [] := by
    have := refusals_before ⟨rr, er⟩ hnone
    rw [← hmade] at this
    simp only [fresh] at this
    rw [rbr] at this
    exact this
  have apartB : BoundsApart σ { s with st := inBody.2 }.st (body.addresses blocks) :=
    fun q m bl key' eq inB => apart q (by simp only at m; rw [in2bounds] at m; exact m) bl key' eq
      (List.mem_cons_of_mem _ (List.mem_append_left _ inB))
  have recB : Recorded σ (body.addresses blocks) e.state.st :=
    ((Recorded.sub recorded fun x m => List.mem_cons_of_mem _ (List.mem_append_left _ m)).strip
      ebr atr (fun x m mr => nodup_apart nodup₁ m mr)).strip (by simp only; rw [m2b, ebd])
      (Bnew := [(blocks, key)]) (fun q m => ⟨blocks, key, atd q m, List.mem_singleton_self _⟩)
      (fun x m mr => by
        simp only [List.mem_singleton] at mr
        subst mr
        exact notHere (List.mem_append_left _ m))
  have growsE : St.Grows s.st e.state.st := fitsIn.2.1.trans gb.2
  -- the body at an iteration
  have bodyInv : ∀ (i : Nat) (state : σ.sem.LoopState carried each),
      i < σ.sem.times times env →
      LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf) inBody.1.tail (env.all init) i
        state →
      Inv σ (ρ.setFrom s.st.next (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)))
        (bindIds ids inputs inBody.1) (env.extend inputs (.cons (σ.sem.index w i) state.1))
        (bodyKnown σ.rules k ids times (inBody.1.headD 0) inBody.1.tail carried)
        inBody.2 := by
    intro i state lt la
    have validL : σ.AllValid (HList.cons (σ.sem.index w i) state.1) :=
      allValid_cons.mpr ⟨(laws.index w i).1, la.carriedValid⟩
    have lenL : (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)).length =
        carried.length + 1 := by rw [σ.sem.dyns_length]; rfl
    obtain ⟨coh, le₁, look⟩ := leaves_fresh (s := s) inv.coherent
      (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)) validL
    simp only [leaves, lenL, hin] at coh look
    refine ⟨coh, agree_extend inputs (HList.cons (σ.sem.index w i) state.1) inBody.1
      (inv.agree.le le₁) look, ?_⟩
    have hi : (ρ.setFrom s.st.next (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)))
        (inBody.1.headD 0) = some ⟨D.index w, σ.sem.index w i⟩ := by
      rw [headIn]
      have := setFrom_at ρ s.st.next (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)) 0
        (by rw [lenL]; omega)
      rw [Nat.add_zero] at this
      rw [this]
      rfl
    have lookC : valuesOf (ρ.setFrom s.st.next (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)))
        inBody.1.tail = some (σ.sem.dyns state.1) := by
      have shape : inBody.1 = s.st.next :: inBody.1.tail := by
        rw [tailIn, in1, List.range'_succ]
      rw [shape] at look
      exact valuesOf_tail look
    exact bodyKnown_holds laws (inv.holds.le le₁) (inv.agree.le le₁) coh.valid times lt hi lookC
  have bodyShows : ∀ (i : Nat) (state : σ.sem.LoopState carried each),
      i < σ.sem.times times env →
      LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf) inBody.1.tail (env.all init) i
        state →
      Shows σ blocks body (path ++ [.iteration key i])
        (env.extend inputs (.cons (σ.sem.index w i) state.1)) (fun out => ∃ ρ',
          (ρ.setFrom s.st.next (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1))).Le ρ' ∧
          ExitInv σ ρ' e.region e.state.st out ∧
          Followed (none : Option (Skel D (carried ++ each))) lo ρ' e.state.st) := by
    intro i state lt la
    have shows := ihb (path ++ [.iteration key i]) _ _ _ _ { s with st := inBody.2 } lo lo
      (bodyInv i state lt la) trivial (by rw [he]; exact differsB) (by rw [he]; exact refsE)
      nodupB apartB (by rw [he]; exact recB)
    rw [he] at shows
    exact shows
  -- one iteration keeps what holds
  have keeps : ∀ (i : Nat) (state : σ.sem.LoopState carried each),
      i < σ.sem.times times env →
      LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf) inBody.1.tail (env.all init) i
        state →
      (σ.sem.loopStep w inputs (fun path' env' => Term.denote σ.sem body path' env') key path env i
        state).Every σ.permitted (fun state' => LoopAt (σ := σ) e.region
          ((idsOf ids init).map k.rangeOf) inBody.1.tail (env.all init) (i + 1) state')
        (fun stop => ¬ σ.undefined stop) := by
    intro i state lt la
    have shows := bodyShows i state lt la
    simp only [Semantics.loopStep]
    rw [Process.every_bind]
    refine Process.every_mono _ _ ?_ (fun _ h => h) shows.2
    intro out h
    obtain ⟨ρ', le', ex, -⟩ := h
    simp only [Process.Every]
    have lenL : (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)).length =
        carried.length + 1 := by rw [σ.sem.dyns_length]; rfl
    have outValid : σ.AllValid out := allValid_of_valuesOf ex.rets ex.coherent.valid
    have parts := (allValid_append _ _).mp (by rw [split_append]; exact outValid :
      σ.AllValid ((HList.split carried out).1.append (HList.split carried out).2))
    refine ⟨parts.1, collectedOK_push la.collected parts.2, fun _ => ex.holds.alive,
      fun h => absurd h (Nat.succ_ne_zero i), ?_⟩
    intro j r₀ t rt hinit hterm hrt
    have jlt : j < carried.length := by
      have := (List.getElem?_eq_some_iff.mp hinit).1
      simp only [List.length_map, idsOf_length] at this
      exact this
    obtain ⟨d₀, n₀, hd₀, hn₀, has₀⟩ := la.sums j r₀ t rt hinit hterm hrt
    have retLt : j < e.region.rets.length := by
      have h1 := valuesOf_length ex.rets
      rw [σ.sem.dyns_length] at h1
      have h2 := List.length_append (as := carried) (bs := each)
      omega
    have hret : ρ' (e.region.rets.getD j 0) = (σ.sem.dyns out)[j]? := valuesOf_get ex.rets j retLt
    have outSplit : (σ.sem.dyns out)[j]? = (σ.sem.dyns (HList.split carried out).1)[j]? := by
      rw [σ.sem.dyns_split out, List.getElem?_append_left (by rw [σ.sem.dyns_length]; exact jlt)]
    have hcid : ρ' (inBody.1.tail.getD j 0) = some d₀ := by
      rw [tailIn, range'_getD jlt]
      have := setFrom_at ρ s.st.next (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)) (j + 1)
        (by rw [lenL]; omega)
      rw [show s.st.next + (j + 1) = s.st.next + 1 + j by omega] at this
      apply le'
      rw [this]
      exact hd₀
    cases hv : (σ.sem.dyns (HList.split carried out).1)[j]? with
    | none =>
        have := (List.getElem?_eq_none_iff.mp hv)
        rw [σ.sem.dyns_length] at this
        exfalso
        omega
    | some dv =>
        rw [outSplit, hv] at hret
        obtain ⟨x, y, hform, which⟩ := carriedTerm_spec hterm
        obtain ⟨vals, hvals, a, b, xa, yb, eqv, ha, hb, hsum⟩ :=
          formOf_values lawful ex.coherent.consistent ex.coherent.closed hform hret
        obtain ⟨va, vb, rfl, hxa, hyb⟩ := valuesOf_pair hvals
        cases eqv
        rcases which with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [hcid] at hxa
          cases hxa
          rw [hn₀] at ha
          cases ha
          have hbr := ex.holds.rangeOf_at ⟨_, hyb, hb⟩ hrt
          exact ⟨dv, _, rfl, hsum, Range.afterSums_step has₀ hbr⟩
        · rw [hcid] at hyb
          cases hyb
          rw [hn₀] at hb
          cases hb
          have har := ex.holds.rangeOf_at ⟨_, hxa, ha⟩ hrt
          rw [Nat.add_comm] at hsum
          exact ⟨dv, _, rfl, hsum, Range.afterSums_step has₀ har⟩
  -- before the first iteration
  have I0 : LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf) inBody.1.tail (env.all init)
      0 (env.all init, HList.empties each) := by
    refine ⟨env_all_valid (agree_valid inv.agree inv.coherent.valid) init,
      collectedOK_empties each, fun h => absurd h (Nat.lt_irrefl 0), fun _ => rfl, ?_⟩
    intro j r₀ t rt hinit _ _
    rw [List.getElem?_map] at hinit
    cases hid : (idsOf ids init)[j]? with
    | none => rw [hid] at hinit; cases hinit
    | some id =>
        rw [hid] at hinit
        simp only [Option.map_some, Option.some.injEq] at hinit
        obtain ⟨n, ⟨d, hd, hn⟩, has⟩ := inv.holds.rangeOf hinit
        have := valuesOf_getElem (valuesOf_idsOf inv.agree init) hid
        rw [hd] at this
        exact ⟨d, n, this.symm, hn, Range.afterSums_zero has⟩
  -- after the last iteration
  have apartR : BoundsApart σ { e.state with st := made.2 }.st (rest.addresses blocks) := by
    intro q m bl key' eq inR
    simp only at m
    rw [m2b, ebd] at m
    rcases List.mem_append.mp m with m | m
    · have := atd q m
      rw [eq] at this
      simp only [Place.mk.injEq, Option.some.injEq, true_and, and_true] at this
      obtain ⟨rfl, rfl⟩ := this
      exact notHere (List.mem_append_right _ inR)
    · rw [ebb] at m
      rcases List.mem_append.mp m with m | m
      · obtain ⟨bl', key'', eq', mem⟩ := atb q m
        rw [eq] at eq'
        simp only [Place.mk.injEq, Option.some.injEq, true_and, and_true] at eq'
        obtain ⟨rfl, rfl⟩ := eq'
        exact nodup_apart nodup₁ mem inR
      · simp only at m
        rw [in2bounds] at m
        exact apart q m bl key' eq (List.mem_cons_of_mem _ (List.mem_append_right _ inR))
  have afterRest : ∀ (state : σ.sem.LoopState carried each),
      LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf) inBody.1.tail (env.all init)
        (σ.sem.times times env) state →
      Shows σ blocks rest path
        (env.extend results (state.1.append (σ.sem.collected times.size state.2)))
        (fun vs => ∃ ρ', ρ.Le ρ' ∧ ExitInv σ ρ'
          (walk σ.rules σ.checks σ.definition σ.role blocks rest none (bindIds ids results made.1)
            ((afterLoop σ.rules e.region k (timesBound k ids times) made.1
              ((idsOf ids init).map k.rangeOf) inBody.1.tail e.rets
              (carried ++ each.map (D.collected times.size))).enter σ.rules
              (carried ++ each.map (D.collected times.size))) { e.state with st := made.2 }).region
          (walk σ.rules σ.checks σ.definition σ.role blocks rest none (bindIds ids results made.1)
            ((afterLoop σ.rules e.region k (timesBound k ids times) made.1
              ((idsOf ids init).map k.rangeOf) inBody.1.tail e.rets
              (carried ++ each.map (D.collected times.size))).enter σ.rules
              (carried ++ each.map (D.collected times.size))) { e.state with st := made.2 }).state.st
          vs ∧
          Followed (none : Option (Skel D outs)) hi ρ'
            (walk σ.rules σ.checks σ.definition σ.role blocks rest none (bindIds ids results made.1)
              ((afterLoop σ.rules e.region k (timesBound k ids times) made.1
                ((idsOf ids init).map k.rangeOf) inBody.1.tail e.rets
                (carried ++ each.map (D.collected times.size))).enter σ.rules
                (carried ++ each.map (D.collected times.size))) { e.state with st := made.2 }).state.st)
      := by
    intro state la
    have fits : ∀ m, times.size = some m → σ.sem.times times env = m := by
      intro m e'
      cases times with
      | fixed n => simp only [Times.size, Option.some.injEq] at e'; subst e'; rfl
      | value => cases e'
    have validR : σ.AllValid (state.1.append (σ.sem.collected times.size state.2)) :=
      (allValid_append _ _).mpr ⟨la.carriedValid,
        collected_valid laws.collect times.size fits la.collected⟩
    have lenR : (σ.sem.dyns (state.1.append (σ.sem.collected times.size state.2))).length =
        carried.length + each.length := by
      rw [σ.sem.dyns_length]
      simp
    have cohE : Coherent σ.Runs σ.Valid ρ st₁ := by
      have := Coherent.grow inv.coherent growsE gb.1.1
      exact ⟨by rw [rbn]; exact this.support, by rw [rbt, rbn]; exact this.wf,
        by rw [rbt]; exact this.consistent, by rw [rbt]; exact this.closed, this.valid⟩
    have coh₂ := Coherent.fresh cohE _ validR
    rw [lenR, hmade] at coh₂
    have le₂ := setFrom_le cohE.support (σ.sem.dyns (state.1.append
      (σ.sem.collected times.size state.2)))
    have look : valuesOf (ρ.setFrom st₁.next (σ.sem.dyns (state.1.append
        (σ.sem.collected times.size state.2)))) made.1 =
        some (σ.sem.dyns (state.1.append (σ.sem.collected times.size state.2))) := by
      rw [m1, ← lenR]
      exact valuesOf_setFrom _ _ _
    have bounds := timesBound_ok laws inv.holds inv.agree inv.coherent.valid times
    have inv' : Inv σ (ρ.setFrom st₁.next (σ.sem.dyns (state.1.append
        (σ.sem.collected times.size state.2)))) (bindIds ids results made.1)
        (env.extend results (state.1.append (σ.sem.collected times.size state.2)))
        ((afterLoop σ.rules e.region k (timesBound k ids times) made.1
          ((idsOf ids init).map k.rangeOf) inBody.1.tail e.rets
          (carried ++ each.map (D.collected times.size))).enter σ.rules
          (carried ++ each.map (D.collected times.size))) made.2 := by
      refine ⟨coh₂, agree_extend results _ made.1 (inv.agree.le le₂) look, ?_⟩
      rw [enter_of_valid laws validR]
      apply afterLoop_holds laws coh₂.valid _ _ _ _ _ k (inv.holds.le le₂)
      intro j m em
      have e1 := valuesOf_getElem look em
      cases hd : (σ.sem.dyns (state.1.append (σ.sem.collected times.size state.2)))[j]? with
      | none => rw [hd] at e1; exact absurd e1 (valuesOf_mem look m (List.mem_of_getElem? em))
      | some d =>
          rw [hd] at e1
          refine ⟨d, e1, σ.sem.dyns_typed _ j d hd, fun initial cid ret hinit hcid hret => ?_⟩
          have jlt : j < carried.length := by
            have := (List.getElem?_eq_some_iff.mp hinit).1
            simp only [List.length_map, idsOf_length] at this
            exact this
          have hdj : (σ.sem.dyns state.1)[j]? = some d := by
            rw [Semantics.dyns_append, List.getElem?_append_left (by rw [σ.sem.dyns_length]; exact jlt)]
              at hd
            exact hd
          refine carriedRange_has bounds la.alive ?_ ?_
          · intro zero r hr
            have := la.initial zero
            rw [this] at hdj
            rw [List.getElem?_map] at hinit
            cases hid : (idsOf ids init)[j]? with
            | none => rw [hid] at hinit; cases hinit
            | some id =>
                rw [hid] at hinit
                simp only [Option.map_some, Option.some.injEq] at hinit
                subst hinit
                obtain ⟨n, ⟨d', hd', hn⟩, has⟩ := inv.holds.rangeOf hr
                have := valuesOf_getElem (valuesOf_idsOf inv.agree init) hid
                rw [hd', hdj] at this
                cases this
                exact ⟨n, hn, has⟩
          · intro r₀ t rt hr₀ ht hrt
            have hcidD : inBody.1.tail.getD j 0 = cid := by
              rw [List.getD_eq_getElem?_getD, hcid]; rfl
            have hretD : e.region.rets.getD j 0 = ret := by
              show e.rets.getD j 0 = ret
              rw [List.getD_eq_getElem?_getD, hret]; rfl
            rw [← hcidD, ← hretD] at ht
            obtain ⟨d', n, hd', hn, has⟩ := la.sums j r₀ t rt (by rw [hinit, hr₀]) ht hrt
            rw [hdj] at hd'
            cases hd'
            exact ⟨n, hn, has⟩
    have shows := ihr path _ _ _ _ { e.state with st := made.2 } hi hi inv' trivial differsR hnone
      nodupR apartR
      (Recorded.sub recorded fun x m => List.mem_cons_of_mem _ (List.mem_append_right _ m))
    exact ⟨shows.1, Process.every_mono _ _ (fun vs h' => by
      obtain ⟨ρ'', le'', ex', f⟩ := h'
      exact ⟨ρ'', le₂.trans le'', ex', f⟩) (fun _ h => h) shows.2⟩
  have all := Process.every_iterate_below σ.permitted (fun stop => ¬ σ.undefined stop)
    (σ.sem.loopStep w inputs (fun path' env' => Term.denote σ.sem body path' env') key path env)
    (fun i state => LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf) inBody.1.tail
      (env.all init) i state)
    (σ.sem.times times env) keeps
  simp only [Shows, Term.EveryLoop, Term.denote]
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro bound hb
    simp only [Annotation.boundAt, Option.map_eq_some_iff] at hb
    obtain ⟨q, hq, rfl⟩ := hb
    have mq := List.mem_of_find?_eq_some hq
    have pq : q.1 = ⟨σ.definition, blocks, some key, σ.role⟩ := by
      have := List.find?_some hq
      simpa using this
    have inFinal := recorded q.1 q.2 blocks key mq pq List.mem_cons_self
    rw [ebr] at inFinal
    rcases List.mem_append.mp inFinal with m | m
    · obtain ⟨bl, key', eq, mem⟩ := atr _ m
      rw [pq] at eq
      simp only [Place.mk.injEq, Option.some.injEq, true_and, and_true] at eq
      obtain ⟨rfl, rfl⟩ := eq
      exact (notHere (List.mem_append_right _ mem)).elim
    · simp only at m
      rw [m2b, ← hst₁] at m
      rcases recordBound_mem m with m | ⟨t, count, ok, htimes, _, hb'⟩
      · rw [ebb] at m
        rcases List.mem_append.mp m with m | m
        · obtain ⟨bl, key', eq, mem⟩ := atb _ m
          rw [pq] at eq
          simp only [Place.mk.injEq, Option.some.injEq, true_and, and_true] at eq
          obtain ⟨rfl, rfl⟩ := eq
          exact (notHere (List.mem_append_left _ mem)).elim
        · simp only at m
          rw [in2bounds] at m
          exact (apart _ m blocks key pq List.mem_cons_self).elim
      · subst htimes
        cases hr : k.rangeOf (idOf ids count.name) with
        | none => rw [hr] at hb'; cases hb'
        | some r =>
            rw [hr] at hb'
            simp only [Option.bind_some] at hb'
            exact (inv.holds.rangeOf_at (count_at laws inv.agree inv.coherent.valid count ok)
              hr).2 _ hb'
  · intro i lt
    refine Process.every_mono _ _ ?_ (fun _ _ => trivial)
      (all i 0 (env.all init, HList.empties each) (by omega) I0)
    intro state h
    rw [Nat.zero_add] at h
    exact (bodyShows i state lt h).1
  · refine Process.every_mono _ _ ?_ (fun _ _ => trivial)
      (all _ 0 (env.all init, HList.empties each) (by omega) I0)
    intro state h
    rw [Nat.zero_add] at h
    exact (afterRest state h).1
  · rw [Process.every_bind]
    refine Process.every_mono _ _ ?_ (fun _ h => h)
      (all _ 0 (env.all init, HList.empties each) (by omega) I0)
    intro state h
    rw [Nat.zero_add] at h
    exact (afterRest state h).2

end

/-! ## Every term, when no skeleton is followed -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] {σ : Setting D Raw}

mutual
  /-- **The walk is sound where no skeleton is followed.** -/
  theorem walk_sound_fresh (laws : σ.Lawful) :
      ∀ (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs),
        Sound σ blocks t none
    | _, _, _, .ret xs => ret_sound _ xs
    | blocks, _, _, .op key o args results rest =>
        op_sound laws blocks key o args results rest (walk_sound_fresh laws blocks rest)
    | blocks, _, _, .guard key w c ok why rest =>
        guard_sound laws blocks key w c ok why rest (walk_sound_fresh laws blocks rest)
    | blocks, _, _, .choose key w c ok gives onTrue onFalse results rest =>
        choose_sound laws blocks key w c ok gives onTrue onFalse results rest
          (walk_sound_fresh laws blocks onTrue) (walk_sound_fresh laws blocks onFalse)
          (walk_sound_fresh laws blocks rest)
    | blocks, _, _, .cases key w x ok gives arms results rest =>
        cases_sound laws blocks key w x ok gives arms results rest
          (walkArms_sound_fresh laws blocks arms) (walk_sound_fresh laws blocks rest)
    | blocks, _, _, .loop key w times gives init inputs body results rest =>
        loop_sound laws blocks key w times gives init inputs body results rest
          (walk_sound_fresh laws blocks body) (walk_sound_fresh laws blocks rest)
    | blocks, _, _, .block key number body results rest =>
        block_sound laws blocks key number body results rest
          (walk_sound_fresh laws (blocks ++ [(key, number)]) body)
          (walk_sound_fresh laws blocks rest)
    | blocks, _, _, .attempt key w owns inputs body results rest =>
        attempt_sound laws blocks key w owns inputs body results rest
          (walk_sound_fresh laws blocks body) (walk_sound_fresh laws blocks rest)
  /-- The walk of arms is sound where no arms are followed. -/
  theorem walkArms_sound_fresh (laws : σ.Lawful) :
      ∀ (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
        (arms : Arms D Γ mid payloads), ArmsSound σ blocks arms none
    | blocks, _, _, _, .nil => armsNil_sound blocks
    | blocks, _, _, _, .cons inputs arm rest =>
        armsCons_sound laws blocks inputs arm rest (walk_sound_fresh laws blocks arm)
          (walkArms_sound_fresh laws blocks rest)
end

omit [DecidableEq Raw] in
/-- At the start of a body: its inputs, bound to their names, have the first identifiers, and the
table is empty. -/
theorem start_inv (laws : σ.Lawful) {types : List D.Ty} (inputs : Names types)
    (values : HList σ.sem.Val types) (valid : σ.AllValid values) (place : Raw → Nat) :
    Inv σ (Valuation.setFrom (fun _ => none) 0 (σ.sem.dyns values))
      (bindIds Ctx.empty inputs (List.range types.length)) (Env.empty.extend inputs values)
      (start σ.rules types) ⟨Table.empty place, types.length, [], []⟩ := by
  have support : Support types.length
      (Valuation.setFrom (fun _ => none : Valuation σ.sem.Dyn) 0 (σ.sem.dyns values)) := by
    have := setFrom_support (ρ := (fun _ => none : Valuation σ.sem.Dyn)) (lo := 0)
      (fun _ _ => rfl) (σ.sem.dyns values)
    rw [Nat.zero_add, σ.sem.dyns_length] at this
    exact this
  have validS := setFrom_valid (Valid := σ.Valid) (ρ := (fun _ => none : Valuation σ.sem.Dyn))
    (lo := 0) (fun _ _ e => by cases e) valid
  have look : valuesOf (Valuation.setFrom (fun _ => none : Valuation σ.sem.Dyn) 0
      (σ.sem.dyns values)) (List.range types.length) = some (σ.sem.dyns values) := by
    have := valuesOf_setFrom (fun _ => none : Valuation σ.sem.Dyn) 0 (σ.sem.dyns values)
    rw [σ.sem.dyns_length] at this
    rw [List.range_eq_range']
    exact this
  have nothing : Agree σ (Valuation.setFrom (fun _ => none : Valuation σ.sem.Dyn) 0
      (σ.sem.dyns values)) Ctx.empty (Env.empty : Env σ.sem.Val Ctx.empty) :=
    fun _ x => nomatch (Ctx.find?_empty (T := D.Ty) x.name).symm.trans x.typed
  refine ⟨⟨support, trivial, fun _ m => (List.not_mem_nil m).elim,
    fun _ m => (List.not_mem_nil m).elim, validS⟩, agree_extend inputs values _ nothing look, ?_⟩
  have empty : Known.empty.Holds σ.R
      (Valuation.setFrom (fun _ => none : Valuation σ.sem.Dyn) 0 (σ.sem.dyns values)) :=
    ⟨rfl, fun _ _ m => (BitTree.not_mem_empty _ m).elim,
      fun _ m => (BitTree.not_mem_empty _ m).elim,
      fun _ _ m => (BitTree.not_mem_empty _ m).elim,
      fun _ m => (BitTree.not_mem_empty _ m).elim⟩
  simp only [start]
  rw [enter_of_valid laws valid]
  exact addTypeRanges_holds laws empty validS (valuesOf_typed look)

end

end Zkc.Core.Analysis.Facts
