module

public import Zkc.Core.Facts.Growth
public import Zkc.Core.Facts.LocalLaws
public import Zkc.Core.Facts.Facts

@[expose] public section

/-!
The check of facts is sound for functions.

For a body that the walk refuses nothing of, against callees that never stop `undefined` and
keep validity, on valid inputs: the run never stops `undefined`, what it returns is valid, and
every loop as often as a count runs at most the bound that the walk gives its place.

The proof is one induction over the term. Along a run, identifiers get values: a valuation that
grows. At every point the run reaches, the state of the walk and the valuation agree (nothing
from the next identifier on has a value, the table is true), every variable in scope has its
identifier's value, and what is known holds. A region that does not run is walked all the same:
it only adds entries above the identifiers that have values, which keeps the table true. Each
iteration of a loop starts from the valuation below the first identifier of its body.
-/

namespace Zkc.Core

namespace FactCheck

section
variable {V : Vocabulary} (M : Model V) {fns : List (FnHeader V)} (table : FnTable M fns)

/-- Every variable in scope has its identifier's value. -/
def Agree {Γ : List V.Ty} (ρ : Valuation (Dyn M)) (ids : List Nat) (env : Env M.Val Γ) : Prop :=
  ∀ τ (x : Var Γ τ), ρ (ids.getD x.index 0) = some ⟨τ, env τ x⟩

/-- What the walk has at a point of a run agrees with the run: the state with the valuation,
the identifiers of the variables in scope with their values, and what is known holds. -/
structure Inv {Γ : List V.Ty} (ρ : Valuation (Dyn M)) (ids : List Nat) (env : Env M.Val Γ)
    (k : Known) (st : St V.Ty (LocalRaw V)) : Prop where
  coherent : Coherent (LocalRun M table) (ValidDyn M) ρ st
  length : ids.length = Γ.length
  below : ∀ i, i ∈ ids → i < st.next
  agree : Agree M ρ ids env
  holds : k.Holds (localReading M) ρ

/-- Where a region returns: the state with the valuation, the identifiers it returns with the
values, and what is known at its end holds. -/
structure ExitInv (ρ : Valuation (Dyn M)) (e : Exit V.Ty (LocalRaw V))
    (st : St V.Ty (LocalRaw V)) {outs : List V.Ty} (vs : HList M.Val outs) : Prop where
  coherent : Coherent (LocalRun M table) (ValidDyn M) ρ st
  rets : lookupAll ρ e.rets = some (toDyns vs)
  holds : e.known.Holds (localReading M) ρ

end

section
variable (definition : Key)

/-- No bound recorded yet is at one of the addresses. -/
def Apart {T Raw : Type} (st : St T Raw) (addresses : List (List (Key × Nat) × Key)) : Prop :=
  ∀ q, q ∈ st.bounds → ∀ bl key, q.1 = ⟨definition, bl, some key, none⟩ → (bl, key) ∉ addresses

/-- Every bound of the annotation at one of the addresses is one that the state records. -/
def Recorded {T Raw : Type} (F : List (Place × Nat)) (addresses : List (List (Key × Nat) × Key))
    (st : St T Raw) : Prop :=
  ∀ p b bl key, (p, b) ∈ F → p = ⟨definition, bl, some key, none⟩ → (bl, key) ∈ addresses →
    (p, b) ∈ st.bounds

end

/-! ## Agreement -/

section
variable {V : Vocabulary} {M : Model V}

theorem Agree.le {Γ : List V.Ty} {ρ ρ' : Valuation (Dyn M)} {ids : List Nat}
    {env : Env M.Val Γ} (h : Agree M ρ ids env) (le : ρ.Le ρ') : Agree M ρ' ids env :=
  fun τ x => le _ _ (h τ x)

theorem lookupAll_idsOf {Γ : List V.Ty} {ρ : Valuation (Dyn M)} {ids : List Nat}
    {env : Env M.Val Γ} (h : Agree M ρ ids env) :
    ∀ {items : List V.Ty} (xs : HList (Var Γ) items),
      lookupAll ρ (idsOf ids xs) = some (toDyns (env.all xs))
  | [], .nil => rfl
  | _ :: _, .cons x rest => by
      simp only [idsOf, lookupAll, h _ x, lookupAll_idsOf h rest, Env.all, toDyns]

theorem agree_extend {Γ : List V.Ty} {ρ : Valuation (Dyn M)} {ids : List Nat}
    {env : Env M.Val Γ} (h : Agree M ρ ids env) :
    ∀ {res : List V.Ty} (vs : HList M.Val res) (made : List Nat),
      lookupAll ρ made = some (toDyns vs) → Agree M ρ (made ++ ids) (Env.extend vs env)
  | [], .nil, made, hr => by
      have := lookupAll_length hr
      simp only [toDyns, List.length_nil] at this
      have : made = [] := List.eq_nil_of_length_eq_zero this.symm
      subst this
      exact h
  | _ :: _, .cons v vs, made, hr => by
      cases made with
      | nil => simp [lookupAll, toDyns] at hr
      | cons r made =>
          simp only [lookupAll, toDyns] at hr
          split at hr
          · next d ds' e1 e2 =>
              simp only [Option.some.injEq, List.cons.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              have ih := agree_extend h vs made e2
              intro τ x
              cases x with
              | head => exact e1
              | tail y =>
                  have := ih τ y
                  simpa [Var.index, Env.cons, Env.extend] using this
          · cases hr

theorem agree_valid {Γ : List V.Ty} {ρ : Valuation (Dyn M)} {ids : List Nat}
    {env : Env M.Val Γ} (h : Agree M ρ ids env) (valid : ∀ i v, ρ i = some v → ValidDyn M v) :
    ∀ τ (x : Var Γ τ), M.Valid τ (env τ x) := fun τ x => valid _ _ (h τ x)

theorem env_all_valid {Γ : List V.Ty} {env : Env M.Val Γ}
    (h : ∀ τ (x : Var Γ τ), M.Valid τ (env τ x)) :
    ∀ {items : List V.Ty} (xs : HList (Var Γ) items), (env.all xs).All M.Valid
  | [], .nil => trivial
  | _ :: _, .cons x rest => HList.all_cons.mpr ⟨h _ x, env_all_valid h rest⟩

/-! ## The state grows -/

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}

theorem Coherent.grow {ρ : Valuation (Dyn M)} {st st' : St V.Ty (LocalRaw V)}
    (coh : Coherent (LocalRun M table) (ValidDyn M) ρ st) (grows : St.Grows st st')
    (wf : Table.WF st'.next st'.table) : Coherent (LocalRun M table) (ValidDyn M) ρ st' := by
  obtain ⟨n, new, e, low⟩ := grows
  obtain ⟨cons, clo⟩ := consistent_extend coh.support coh.consistent coh.closed low
  rw [← e] at cons clo
  exact ⟨coh.support.mono n, wf, cons, clo, coh.valid⟩

theorem Coherent.fresh {ρ : Valuation (Dyn M)} {st : St V.Ty (LocalRaw V)}
    (coh : Coherent (LocalRun M table) (ValidDyn M) ρ st) (vs : List (Dyn M))
    (valid : ∀ v, v ∈ vs → ValidDyn M v) :
    Coherent (LocalRun M table) (ValidDyn M) (ρ.setFrom st.next vs)
      (FactCheck.fresh vs.length st).2 := by
  obtain ⟨cons, clo⟩ := consistent_setFrom coh.wf coh.consistent coh.closed vs
  exact ⟨setFrom_support coh.support vs, coh.wf.mono (by simp [FactCheck.fresh]), cons, clo,
    setFrom_valid coh.valid valid⟩

theorem toDyns_typed : ∀ {items : List V.Ty} (vs : HList M.Val items) (j : Nat) (d : Dyn M),
    (toDyns vs)[j]? = some d → items[j]? = some d.1
  | [], .nil, _, _, e => by simp [toDyns] at e
  | _ :: _, .cons v vs, j, d, e => by
      cases j with
      | zero =>
          simp only [toDyns, List.getElem?_cons_zero, Option.some.injEq] at e
          subst e
          rfl
      | succ j =>
          simp only [toDyns, List.getElem?_cons_succ] at e ⊢
          exact toDyns_typed vs j d e

/-- What the types of new values say holds of them. -/
theorem typeRanges_holds {k : Known} {ρ : Valuation (Dyn M)}
    (hk : k.Holds (localReading M) ρ) (valid : ∀ i v, ρ i = some v → ValidDyn M v)
    {made : List Nat} {res : List V.Ty} {vs : HList M.Val res}
    (look : lookupAll ρ made = some (toDyns vs)) :
    (k.addRanges made (res.map localRange)).Holds (localReading M) ρ := by
  refine hk.addRanges fun j id r e1 e2 => ?_
  have hv := lookupAll_getElem look e1
  cases hd : (toDyns vs)[j]? with
  | none => rw [hd] at hv; exact absurd hv (lookupAll_mem look id (List.mem_of_getElem? e1))
  | some d =>
      rw [hd] at hv
      have typed := toDyns_typed vs j d hd
      rw [List.getElem?_map, typed] at e2
      simp only [Option.map_some, Option.some.injEq] at e2
      obtain ⟨n, hn, has⟩ := localRange_has e2 d.2 (valid id d hv)
      exact ⟨n, ⟨d, hv, hn⟩, has⟩

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
    {e : Exit T Raw} {position : Nat} (good : Joined P (e.rangeAt position)) :
    ∀ (exits : List (Exit T Raw)) (acc : Option (Option Range)), (Joined P acc ∨ e ∈ exits) →
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

theorem Range.has_hull {n : Nat} : ∀ a b : Range, a.Has n ∨ b.Has n → (a.hull b).Has n
  | _, _, .inl h => h.hull_left
  | _, _, .inr h => h.hull_right

/-- What is known after regions, one of which ran and returned values that the new identifiers
have, holds. -/
theorem afterRegions_holds {exits : List (Exit V.Ty (LocalRaw V))} {e : Exit V.Ty (LocalRaw V)}
    (he : e ∈ exits) {ρe ρ' : Valuation (Dyn M)}
    (hek : e.known.Holds (localReading M) ρe) (valid : ∀ i v, ρ' i = some v → ValidDyn M v) :
    ∀ (ms : List Nat) (τs : List V.Ty) (p : Nat) (k : Known), k.Holds (localReading M) ρ' →
      (∀ j m, ms[j]? = some m → ∃ d, ρ' m = some d ∧ ρe (e.rets.getD (p + j) 0) = some d ∧
        τs[j]? = some d.1) →
      (afterRegions (localFactRules V fns) exits k ms τs p).Holds (localReading M) ρ'
  | m :: ms, τ :: τs, p, k, hk, h => by
      simp only [afterRegions]
      obtain ⟨d, hm, hr, hτ⟩ := h 0 m rfl
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hτ
      subst hτ
      apply afterRegions_holds he hek valid ms τs (p + 1)
      · refine (hk.addRange? fun r e1 => ?_).addRange? fun r e2 => ?_
        · have good : Joined (fun r => ∃ n, (localReading M).nat d = some n ∧ r.Has n)
              (e.rangeAt p) := by
            simp only [Exit.rangeAt, hek.alive, Bool.false_eq_true, ↓reduceIte]
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
        · obtain ⟨n, hn, has⟩ := localRange_has e2 d.2 (valid m d hm)
          exact ⟨n, ⟨d, hm, hn⟩, has⟩
      · intro j m' e'
        obtain ⟨d', h1, h2, h3⟩ := h (j + 1) m' (by simpa using e')
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

end

/-! ## The shapes of a choice -/

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}

/-- A choice fact holds of a valuation. -/
abbrev ChoiceHolds (ρ : Valuation (Dyn M)) (c : ChoiceFact) : Prop :=
  ρ c.result ≠ none ∧ ∀ b, BoolAt (localReading M) ρ c.result b → b = c.conjunction →
    BoolAt (localReading M) ρ c.condition b ∧ BoolAt (localReading M) ρ c.other b

/-- The shapes of a choice hold where its condition has a value, the region that it chose ran,
and the results of the choice have the values that the region returned. -/
theorem choiceFacts_holds (lawful : OpFacts.Lawful (localOpFacts V) (localReading M)
      (LocalRun M table))
    {ρ : Valuation (Dyn M)} {tbl : Table (LocalRaw V)}
    (hc : Consistent (LocalRun M table) ρ tbl) (hcl : Closed ρ tbl) {condition : Nat}
    {b0 : Bool} (hcond : BoolAt (localReading M) ρ condition b0)
    {first second : Exit V.Ty (LocalRaw V)} :
    ∀ (ms : List Nat) (p : Nat),
      (∀ j m, ms[j]? = some m → ∃ d, ρ m = some d ∧
        ρ ((if b0 then first else second).rets.getD (p + j) 0) = some d) →
      ∀ c, c ∈ choiceFacts (localOpFacts V) tbl condition first second ms p → ChoiceHolds ρ c
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

theorem Known.Holds.addChoices {ρ : Valuation (Dyn M)} {k : Known}
    (hk : k.Holds (localReading M) ρ) {cs : List ChoiceFact}
    (h : ∀ c, c ∈ cs → ChoiceHolds ρ c) : (cs.foldl Known.addChoice k).Holds (localReading M) ρ :=
  foldl_invariant (P := fun k => k.Holds (localReading M) ρ) _ cs k hk
    (fun _ c m hk' => hk'.addChoice (h c m))

end

/-! ## The alternative of a variant -/

section
variable {V : Vocabulary} {M : Model V}

/-- The payload of an alternative is valid. -/
def PickValid : {payloads : List V.Ty} → Pick M.Val payloads → Prop
  | _, .here v => M.Valid _ v
  | _, .there p => PickValid p

theorem Tys.pick_valid : ∀ (alts : Tys V.TypeKey) (c : alts.Choice M.toCarriers),
    Tys.ValidChoice M.toCarriers alts c → PickValid (Tys.pick M alts c)
  | .nil, c, _ => nomatch c
  | .cons _ _, .inl _, h => h
  | .cons _ rest, .inr c, h => Tys.pick_valid rest c h

theorem pickValid_cast {ps qs : List V.Ty} (h : ps = qs) (p : Pick M.Val ps) :
    PickValid (cast (congrArg (Pick M.Val) h) p) ↔ PickValid p := by
  subst h
  rfl

theorem valid_cast {τ τ' : V.Ty} (h : τ = τ') (v : M.Val τ) :
    M.Valid τ' (cast (congrArg M.Val h) v) ↔ M.Valid τ v := by
  subst h
  rfl

theorem localPick_valid {t : V.Ty} {payloads : List V.Ty}
    (h : ∃ key alternatives, t = .variant key alternatives ∧ payloads = alternatives.toList)
    (v : M.Val t) (valid : M.Valid t v) : PickValid (localPick M h v) := by
  simp only [localPick]
  rw [pickValid_cast (by obtain ⟨_, _, e, q⟩ := h; rw [Ty.alternatives_of e, q])]
  apply Tys.pick_valid
  have := (valid_cast (Ty.eq_variant h) v).mpr valid
  exact this

end

/-! ## The walk is sound -/

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}

theorem localFactRules_written {ins res : List V.Ty} (o : LocalOp V fns ins res) :
    (localFactRules V fns).written o = some o.print := rfl
theorem localFactRules_ops : (localFactRules V fns).ops = localOpFacts V := rfl
theorem localFactRules_range : (localFactRules V fns).range = localRange := rfl
theorem localSem_op {ins res : List V.Ty} (key : Key) (o : LocalOp V fns ins res)
    (path : List Frame) (xs : HList M.Val ins) :
    (localSem M fns table).op key o path xs = localOp M table o xs := rfl
theorem localSem_holds {t : V.Ty} (ok : t = .bool) (v : M.Val t) :
    (localSem M fns table).holds (w := ()) ok v = asBool M ok v := rfl
theorem localSem_stop (why : Reason) (at_ : Occurrence) :
    (localSem M fns table).stop () why at_ = .declared why at_ := rfl

/-- What the walk of a term shows of its run, with what holds where it returns. -/
abbrev Shows (F : List (Place × Nat)) (definition : Key) (blocks : List (Key × Nat))
    {Γ outs : List V.Ty} (t : Term (localDialect V fns) Γ outs) (path : List Frame)
    (env : Env M.Val Γ) (post : HList M.Val outs → Prop) : Prop :=
  t.Everywhere (localSem M fns table) (fun _ _ => True) (fun _ _ _ => True)
      (Annotation.Bounded ⟨F⟩ definition none) path blocks env ∧
    (t.denote (localSem M fns table) path env).Every (fun _ _ => True) post (· ≠ .undefined)

theorem Apart.sub {T Raw : Type} {definition : Key} {st : St T Raw}
    {A B : List (List (Key × Nat) × Key)} (h : Apart definition st A) (sub : ∀ x, x ∈ B → x ∈ A) :
    Apart definition st B := fun q m bl key e inB => h q m bl key e (sub _ inB)

theorem Recorded.sub {T Raw : Type} {definition : Key} {F : List (Place × Nat)} {st : St T Raw}
    {A B : List (List (Key × Nat) × Key)} (h : Recorded definition F A st)
    (sub : ∀ x, x ∈ B → x ∈ A) : Recorded definition F B st :=
  fun p b bl key m e inB => h p b bl key m e (sub _ inB)

/-- Bounds added at other addresses keep a state apart from the addresses. -/
theorem Apart.extend {T Raw : Type} {definition : Key} {st st' : St T Raw}
    {A Bnew : List (List (Key × Nat) × Key)} {new : List (Place × Nat)}
    (h : Apart definition st A) (e : st'.bounds = new ++ st.bounds)
    (at_ : BoundsAt definition none Bnew new) (apart : ∀ x, x ∈ Bnew → x ∉ A) :
    Apart definition st' A := by
  intro q m bl key eq inA
  rw [e] at m
  rcases List.mem_append.mp m with m | m
  · obtain ⟨bl', key', eq', mem⟩ := at_ q m
    rw [eq] at eq'
    simp only [Place.mk.injEq, Option.some.injEq, true_and, and_true] at eq'
    obtain ⟨rfl, rfl⟩ := eq'
    exact apart _ mem inA
  · exact h q m bl key eq inA

/-- Bounds recorded at other addresses are not those of the addresses. -/
theorem Recorded.strip {T Raw : Type} {definition : Key} {F : List (Place × Nat)}
    {st st' : St T Raw} {A Bnew : List (List (Key × Nat) × Key)} {new : List (Place × Nat)}
    (h : Recorded definition F A st') (e : st'.bounds = new ++ st.bounds)
    (at_ : BoundsAt definition none Bnew new) (apart : ∀ x, x ∈ A → x ∉ Bnew) :
    Recorded definition F A st := by
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

theorem nodup_apart {α : Type} {l₁ l₂ : List α} (h : (l₁ ++ l₂).Nodup) {x : α} (h₁ : x ∈ l₁)
    (h₂ : x ∈ l₂) : False :=
  (List.nodup_append.mp h).2.2 x h₁ x h₂ rfl

end

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}
  (distinct : (fns.map (·.key)).Nodup)
  (safe : ∀ hdr (callee : Var fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
    (table hdr callee args).Stops (· ≠ .undefined))
  (keeps : FnTable.KeepsValidity table)
  (definition : Key) (F : List (Place × Nat))

/-- The walk of a term from any point of a run that agrees with it shows the run. -/
def Sound (blocks : List (Key × Nat)) {Γ outs : List V.Ty} (t : Term (localDialect V fns) Γ outs) :
    Prop :=
  ∀ (path : List Frame) (ρ : Valuation (Dyn M)) (ids : List Nat) (env : Env M.Val Γ) (k : Known)
    (st : St V.Ty (LocalRaw V)), Inv M table ρ ids env k st →
    (walk (localFactRules V fns) definition none blocks t ids k st).st.refusals = [] →
    (t.addresses blocks).Nodup → Apart definition st (t.addresses blocks) →
    Recorded definition F (t.addresses blocks)
      (walk (localFactRules V fns) definition none blocks t ids k st).st →
    Shows (table := table) F definition blocks t path env (fun vs => ∃ ρ', ρ.Le ρ' ∧
      ExitInv M table ρ' (walk (localFactRules V fns) definition none blocks t ids k st)
        (walk (localFactRules V fns) definition none blocks t ids k st).st vs)

theorem localRun_valid (w : LocalRaw V) (as rs : List (Dyn M)) (h : LocalRun M table w as rs)
    (_ : ∀ a, a ∈ as → ValidDyn M a) : ∀ r, r ∈ rs → ValidDyn M r := by
  obtain ⟨_, _, _, _, r, _, _, rfl, _, vr, _⟩ := h
  exact toDyns_valid vr

include distinct safe keeps in
/-- An operation: its requirements hold, so it does not stop `undefined`; its results have the
identifiers that the table gives, with the ranges that are learned. -/
theorem op_sound (blocks : List (Key × Nat)) {Γ outs ins res : List V.Ty} (key : Key)
    (o : LocalOp V fns ins res) (args : HList (Var Γ) ins)
    (rest : Term (localDialect V fns) (res ++ Γ) outs)
    (ih : Sound (table := table) definition F blocks rest) :
    Sound (table := table) definition F blocks (.op key o args rest) := by
  intro path ρ ids env k st inv hnone nodup apart recorded
  have lawful := localOpFacts_lawful (table := table) distinct
  have nodup' := (List.nodup_cons.mp nodup).2
  have va : (env.all args).All M.Valid :=
    env_all_valid (agree_valid inv.agree inv.coherent.valid) args
  have hargs := lookupAll_idsOf inv.agree args
  have hlt : ∀ a, a ∈ idsOf ids args → a < st.next :=
    fun a m => inv.below a (idsOf_mem inv.length args a m)
  simp only [Shows, walk, opStep, localFactRules_written, localFactRules_ops,
    localFactRules_range, Term.Everywhere, Term.denote] at hnone recorded ⊢
  generalize hst₁ : checkRequirements (localOpFacts V) k ⟨definition, blocks, some key, none⟩
    o.print (idsOf ids args) ((localOpFacts V).requires o.print) st = st₁ at hnone recorded ⊢
  generalize hmade : share o.print (idsOf ids args) res.length st₁ = made at hnone recorded ⊢
  generalize hk₂ : (k.addRanges made.1 ((localOpFacts V).ranges o.print
    (List.map k.rangeOf (idsOf ids args)))).addRanges made.1 (List.map localRange res) = k₂
    at hnone recorded ⊢
  have refs₁ : st₁.refusals = [] := by
    obtain ⟨⟨new, e⟩, _⟩ := (walk_state (localFactRules V fns) definition none blocks rest
      (made.1 ++ ids) k₂ made.2).1
    rw [hnone] at e
    have := (share_state o.print (idsOf ids args) res.length st₁).1
    rw [hmade] at this
    rw [← this]
    exact (List.append_eq_nil_iff.mp e.symm).2
  obtain ⟨ρ₁, step₁, hreq⟩ := checkRequirements_sound lawful localRun_valid
    ((localOpFacts V).requires o.print) inv.coherent inv.holds hargs hlt
    (localRequires_runs o (env.all args) va) (by rw [hst₁]; exact refs₁)
  rw [hst₁] at step₁
  have defined := localOp_defined safe o (env.all args) va hreq
  rw [Process.every_bind]
  cases hrun : localOp M table o (env.all args) with
  | call op _ => exact nomatch op
  | halt h =>
      rw [hrun] at defined
      exact ⟨⟨trivial, trivial⟩, defined⟩
  | done r =>
      have vr := localOp_valid table keeps o (env.all args) r va hrun
      have run : LocalRun M table o.print (toDyns (env.all args)) (toDyns r) :=
        ⟨_, _, o, env.all args, r, rfl, rfl, rfl, va, vr, hrun⟩
      obtain ⟨ρ₂, step₂, look, below⟩ := share_sound lawful step₁.coherent
        (lookupAll_le step₁.le hargs) (fun a m => Nat.lt_of_lt_of_le (hlt a m) step₁.grows.next)
        run (toDyns_valid vr)
      rw [toDyns_length, hmade] at step₂ look below
      have le := step₁.le.trans step₂.le
      have inv' : Inv M table ρ₂ (made.1 ++ ids) (Env.extend r env) k₂ made.2 := by
        refine ⟨step₂.coherent, ?_, ?_, agree_extend (inv.agree.le le) r made.1 look, ?_⟩
        · have := lookupAll_length look
          rw [toDyns_length] at this
          simp [← this, inv.length]
        · intro i m
          rcases List.mem_append.mp m with m | m
          · exact below i m
          · exact Nat.lt_of_lt_of_le (inv.below i m)
              (Nat.le_trans step₁.grows.next step₂.grows.next)
        · rw [← hk₂]
          refine typeRanges_holds ((inv.holds.le le).addRanges fun j id rr e1 e2 => ?_)
            step₂.coherent.valid look
          have known : ∀ (i : Nat) (rr : Range),
              (List.map k.rangeOf (idsOf ids args))[i]? = some (some rr) →
              ∃ v n, (toDyns (env.all args))[i]? = some v ∧
                (localReading M).nat v = some n ∧ rr.Has n := by
            intro i rr e
            rw [List.getElem?_map] at e
            cases ha : (idsOf ids args)[i]? with
            | none => rw [ha] at e; cases e
            | some a =>
                rw [ha] at e
                simp only [Option.map_some, Option.some.injEq] at e
                obtain ⟨n, ⟨v, hv, hn⟩, has⟩ := inv.holds.rangeOf e
                have := lookupAll_getElem hargs ha
                rw [hv] at this
                exact ⟨v, n, this.symm, hn, has⟩
          obtain ⟨v, n, hv, hn, has⟩ := localRun_ranges _ run known j rr e2
          have := lookupAll_getElem look e1
          rw [hv] at this
          exact ⟨n, ⟨v, this, hn⟩, has⟩
      have apart' : Apart definition made.2 (rest.addresses blocks) := by
        intro q m bl key' eq inRest
        rw [step₂.bounds, step₁.bounds] at m
        exact apart q m bl key' eq (List.mem_cons_of_mem _ inRest)
      have shows := ih path ρ₂ (made.1 ++ ids) (Env.extend r env) k₂ made.2 inv' hnone nodup'
        apart' (recorded.sub fun x m => List.mem_cons_of_mem _ m)
      refine ⟨⟨trivial, shows.1⟩, ?_⟩
      simp only [Process.Every]
      refine Process.every_mono _ _ ?_ (fun _ h => h) shows.2
      intro vs h
      obtain ⟨ρ'', le'', ex⟩ := h
      exact ⟨ρ'', le.trans le'', ex⟩

end

/-! ### After regions -/

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}

/-- After regions one of which ran: the new values have new identifiers, and what is known of
them holds. -/
theorem afterRegions_inv {Γ mid : List V.Ty} {exits : List (Exit V.Ty (LocalRaw V))}
    {e : Exit V.Ty (LocalRaw V)} (he : e ∈ exits) {ρ ρ₁ : Valuation (Dyn M)} {ids : List Nat}
    {env : Env M.Val Γ} {k : Known} {st₀ st' : St V.Ty (LocalRaw V)}
    (inv : Inv M table ρ ids env k st₀) (le : ρ.Le ρ₁) {mids : HList M.Val mid}
    (ex : ExitInv M table ρ₁ e st' mids) (grows : St.Grows st₀ st') :
    Inv M table (ρ₁.setFrom st'.next (toDyns mids)) ((fresh mid.length st').1 ++ ids)
      (Env.extend mids env) (afterRegions (localFactRules V fns) exits k (fresh mid.length st').1
        mid 0) (fresh mid.length st').2 := by
  have valid : ∀ v, v ∈ toDyns mids → ValidDyn M v := lookupAll_valid ex.rets ex.coherent.valid
  have coh := Coherent.fresh ex.coherent (toDyns mids) valid
  rw [toDyns_length] at coh
  have le₂ : ρ₁.Le (ρ₁.setFrom st'.next (toDyns mids)) := setFrom_le ex.coherent.support _
  have look : lookupAll (ρ₁.setFrom st'.next (toDyns mids)) (fresh mid.length st').1 =
      some (toDyns mids) := by
    have := lookupAll_setFrom ρ₁ st'.next (toDyns mids)
    rw [toDyns_length] at this
    exact this
  refine ⟨coh, by simp [fresh, inv.length], ?_,
    agree_extend (inv.agree.le (le.trans le₂)) mids _ look, ?_⟩
  · intro i m
    rcases List.mem_append.mp m with m | m
    · have m := mem_range'_bounds m
      simp only [fresh] at m ⊢
      omega
    · simp only [fresh]
      exact Nat.lt_of_lt_of_le (inv.below i m) (Nat.le_trans grows.next (Nat.le_add_right _ _))
  · apply afterRegions_holds he ex.holds coh.valid _ _ 0 k (inv.holds.le (le.trans le₂))
    intro j m em
    have e1 := lookupAll_getElem look em
    cases hd : (toDyns mids)[j]? with
    | none => rw [hd] at e1; exact absurd e1 (lookupAll_mem look m (List.mem_of_getElem? em))
    | some d =>
        rw [hd] at e1
        refine ⟨d, e1, ?_, toDyns_typed mids j d hd⟩
        have lt : j < e.rets.length := by
          have h1 := lookupAll_length ex.rets
          have h2 := (List.getElem?_eq_some_iff.mp hd).1
          omega
        rw [Nat.zero_add, lookupAll_get ex.rets j lt, hd]

end

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}
  (distinct : (fns.map (·.key)).Nodup)
  (safe : ∀ hdr (callee : Var fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
    (table hdr callee args).Stops (· ≠ .undefined))
  (keeps : FnTable.KeepsValidity table)
  (definition : Key) (F : List (Place × Nat))

theorem ret_sound (blocks : List (Key × Nat)) {Γ outs : List V.Ty} (xs : HList (Var Γ) outs) :
    Sound (table := table) definition F blocks (.ret xs) := by
  intro path ρ ids env k st inv _ _ _ _
  simp only [Shows, walk, Term.Everywhere, Term.denote, Process.Every]
  exact ⟨trivial, ρ, Valuation.Le.refl ρ, inv.coherent, lookupAll_idsOf inv.agree xs, inv.holds⟩

include distinct in
theorem guard_sound (blocks : List (Key × Nat)) {Γ outs : List V.Ty} {t : V.Ty} (key : Key)
    (c : Var Γ t) (ok : t = .bool) (why : Reason) (rest : Term (localDialect V fns) Γ outs)
    (ih : Sound (table := table) definition F blocks rest) :
    Sound (table := table) definition F blocks (.guard key () c ok why rest) := by
  intro path ρ ids env k st inv hnone nodup apart recorded
  have lawful := localOpFacts_lawful (table := table) distinct
  simp only [Shows, walk, Term.Everywhere, Term.denote] at hnone recorded ⊢
  subst ok
  have hc := inv.agree .bool c
  simp only [asBool, cast_eq]
  cases hv : env Ty.bool c with
  | false =>
      simp only [Bool.cond_false, Process.Every, Bool.false_eq_true, false_implies, and_true]
      exact ⟨trivial, by simp⟩
  | true =>
      rw [hv] at hc
      have k' := assume_holds lawful inv.coherent.consistent inv.coherent.closed st.next inv.holds
        ⟨_, hc, rfl⟩
      have shows := ih path ρ ids env _ st ⟨inv.coherent, inv.length, inv.below, inv.agree, k'⟩
        hnone (List.nodup_cons.mp nodup).2 (apart.sub fun x m => List.mem_cons_of_mem _ m)
        (recorded.sub fun x m => List.mem_cons_of_mem _ m)
      simp only [Bool.cond_true, forall_const]
      exact ⟨⟨trivial, shows.1⟩, shows.2⟩

theorem block_sound (blocks : List (Key × Nat)) {Γ outs mid : List V.Ty} (key : Key)
    (number : Nat) (body : Term (localDialect V fns) Γ mid)
    (rest : Term (localDialect V fns) (mid ++ Γ) outs)
    (ihb : Sound (table := table) definition F (blocks ++ [(key, number)]) body)
    (ihr : Sound (table := table) definition F blocks rest) :
    Sound (table := table) definition F blocks (.block key number body rest) := by
  intro path ρ ids env k st inv hnone nodup apart recorded
  simp only [Shows, walk, Term.Everywhere, Term.denote] at hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  obtain ⟨⟨_, nb, ebb, atb⟩, gb⟩ := walk_state (localFactRules V fns) definition none
    (blocks ++ [(key, number)]) body ids k st
  generalize he : walk (localFactRules V fns) definition none (blocks ++ [(key, number)]) body ids
    k st = e at hnone recorded ebb gb ⊢
  obtain ⟨⟨⟨nr, er⟩, nbr, ebr, atr⟩, _⟩ := walk_state (localFactRules V fns) definition none
    blocks rest ((fresh mid.length e.st).1 ++ ids)
    (afterRegions (localFactRules V fns) [e] k (fresh mid.length e.st).1 mid 0)
    (fresh mid.length e.st).2
  have refs : e.st.refusals = [] := by
    rw [hnone] at er
    exact (List.append_eq_nil_iff.mp er.symm).2
  have nodupB := (List.nodup_append.mp nodup).1
  have nodupR := (List.nodup_append.mp nodup).2.1
  have recB : Recorded definition F (body.addresses (blocks ++ [(key, number)])) e.st :=
    (recorded.sub fun x m => List.mem_append_left _ m).strip (by rw [ebr]; rfl) atr
      (fun x m mr => nodup_apart nodup m mr)
  have showsB := ihb (path ++ [.iteration key number]) ρ ids env k st inv (by rw [he]; exact refs)
    nodupB (apart.sub fun x m => List.mem_append_left _ m) (by rw [he]; exact recB)
  rw [he] at showsB
  refine ⟨⟨showsB.1, ?_⟩, ?_⟩
  · refine Process.every_mono _ _ ?_ (fun _ _ => trivial) showsB.2
    intro mids h
    obtain ⟨ρ₁, le, ex⟩ := h
    have grows := (gb inv.length ⟨inv.coherent.wf, inv.below⟩).2
    have inv' := afterRegions_inv (List.mem_singleton_self e) inv le ex grows
    exact (ihr path _ _ _ _ _ inv' hnone nodupR
      (Apart.extend (apart.sub fun x m => List.mem_append_right _ m)
        (by simp only [fresh]; exact ebb) atb (fun x m mr => nodup_apart nodup m mr))
      (recorded.sub fun x m => List.mem_append_right _ m)).1
  · rw [Process.every_bind]
    refine Process.every_mono _ _ ?_ (fun _ h => h) showsB.2
    intro mids h
    obtain ⟨ρ₁, le, ex⟩ := h
    have grows := (gb inv.length ⟨inv.coherent.wf, inv.below⟩).2
    have inv' := afterRegions_inv (List.mem_singleton_self e) inv le ex grows
    have shows := ihr path _ _ _ _ _ inv' hnone nodupR
      (Apart.extend (apart.sub fun x m => List.mem_append_right _ m)
        (by simp only [fresh]; exact ebb) atb (fun x m mr => nodup_apart nodup m mr))
      (recorded.sub fun x m => List.mem_append_right _ m)
    refine Process.every_mono _ _ ?_ (fun _ h => h) shows.2
    intro vs h'
    obtain ⟨ρ'', le'', ex'⟩ := h'
    exact ⟨ρ'', le.trans ((setFrom_le ex.coherent.support _).trans le''), ex'⟩

end

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}
  (distinct : (fns.map (·.key)).Nodup)
  (definition : Key) (F : List (Place × Nat))

theorem attempt_sound (blocks : List (Key × Nat)) {Γ outs mid : List V.Ty} (key : Key) (w : Unit)
    (owns : (localDialect V fns).Attempt w)
    (body : Term (localDialect V fns) ((localDialect V fns).index w :: Γ) mid)
    (rest : Term (localDialect V fns) (mid ++ Γ) outs) :
    Sound (table := table) definition F blocks (.attempt key w owns body rest) :=
  owns.elim

/-- The state after the regions of a choice, of a valuation that agrees with the region that
ran. -/
theorem exit_grow {ρ : Valuation (Dyn M)} {e : Exit V.Ty (LocalRaw V)}
    {st st' : St V.Ty (LocalRaw V)} {outs : List V.Ty} {vs : HList M.Val outs}
    (ex : ExitInv M table ρ e st vs) (grows : St.Grows st st') (wf : Table.WF st'.next st'.table) :
    ExitInv M table ρ e st' vs :=
  ⟨ex.coherent.grow grows wf, ex.rets, ex.holds⟩

include distinct in
theorem choose_sound (blocks : List (Key × Nat)) {Γ outs mid : List V.Ty} {t : V.Ty} (key : Key)
    (c : Var Γ t) (ok : t = .bool) (gives : ∀ a, a ∈ mid → (localDialect V fns).Gives () a)
    (onTrue onFalse : Term (localDialect V fns) Γ mid)
    (rest : Term (localDialect V fns) (mid ++ Γ) outs)
    (iht : Sound (table := table) definition F blocks onTrue)
    (ihf : Sound (table := table) definition F blocks onFalse)
    (ihr : Sound (table := table) definition F blocks rest) :
    Sound (table := table) definition F blocks (.choose key () c ok gives onTrue onFalse rest) := by
  intro path ρ ids env k st inv hnone nodup apart recorded
  have lawful := localOpFacts_lawful (table := table) distinct
  simp only [Shows, walk, Term.Everywhere, Term.denote] at hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  subst ok
  simp only [asBool, cast_eq]
  have hc := inv.agree .bool c
  generalize ids.getD c.index 0 = cid at hc hnone recorded ⊢
  obtain ⟨⟨⟨ra, ea⟩, na, eba, ata⟩, ga⟩ := walk_state (localFactRules V fns) definition none
    blocks onTrue ids (assume (localFactRules V fns).ops st.table st.next k cid true) st
  generalize hfirst : walk (localFactRules V fns) definition none blocks onTrue ids
    (assume (localFactRules V fns).ops st.table st.next k cid true) st = first
    at hnone recorded ea eba ga ⊢
  obtain ⟨⟨⟨rb, eb⟩, nb, ebb, atb⟩, gb⟩ := walk_state (localFactRules V fns) definition none
    blocks onFalse ids (assume (localFactRules V fns).ops first.st.table first.st.next k cid false)
    first.st
  generalize hsecond : walk (localFactRules V fns) definition none blocks onFalse ids
    (assume (localFactRules V fns).ops first.st.table first.st.next k cid false) first.st = second
    at hnone recorded eb ebb gb ⊢
  obtain ⟨⟨⟨nr, er⟩, nbr, ebr, atr⟩, _⟩ := walk_state (localFactRules V fns) definition none
    blocks rest ((fresh mid.length second.st).1 ++ ids)
    (afterChoice (localFactRules V fns) k cid first second (fresh mid.length second.st).1 mid)
    (fresh mid.length second.st).2
  have refsB : second.st.refusals = [] := by
    rw [hnone] at er
    exact (List.append_eq_nil_iff.mp er.symm).2
  have refsA : first.st.refusals = [] := by
    rw [refsB] at eb
    exact (List.append_eq_nil_iff.mp eb.symm).2
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupAB := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  have nodupA := (List.nodup_append.mp nodupAB).1
  have nodupB := (List.nodup_append.mp nodupAB).2.1
  have fitsA := ga inv.length ⟨inv.coherent.wf, inv.below⟩
  have fitsB := gb inv.length ⟨fitsA.1.1, fun i m => Nat.lt_of_lt_of_le (inv.below i m)
    fitsA.2.next⟩
  have apartR : Apart definition (fresh mid.length second.st).2 (rest.addresses blocks) :=
    ((apart.sub fun x m => by simp [m]).extend eba ata (fun x m mr =>
      nodup_apart nodup₁ (List.mem_append_left _ m) mr)).extend ebb atb
      (fun x m mr => nodup_apart nodup₁ (List.mem_append_right _ m) mr)
  -- the rest, after either region
  have afterRest : ∀ (b0 : Bool) (ran : Exit V.Ty (LocalRaw V)), ran ∈ [first, second] →
      ran = (if b0 then first else second) → (env .bool c = b0) →
      ∀ (ρ₁ : Valuation (Dyn M)) (mids : HList M.Val mid), ρ.Le ρ₁ →
        ExitInv M table ρ₁ ran second.st mids →
        Shows (table := table) F definition blocks rest path (Env.extend mids env) (fun vs =>
          ∃ ρ', ρ.Le ρ' ∧ ExitInv M table ρ'
            (walk (localFactRules V fns) definition none blocks rest
              ((fresh mid.length second.st).1 ++ ids)
              (afterChoice (localFactRules V fns) k cid first second (fresh mid.length second.st).1
                mid) (fresh mid.length second.st).2)
            (walk (localFactRules V fns) definition none blocks rest
              ((fresh mid.length second.st).1 ++ ids)
              (afterChoice (localFactRules V fns) k cid first second (fresh mid.length second.st).1
                mid) (fresh mid.length second.st).2).st vs) := by
    intro b0 ran mem eran hb0 ρ₁ mids le ex
    have grows : St.Grows st second.st := fitsA.2.trans fitsB.2
    have inv' := afterRegions_inv mem inv le ex grows
    have le₂ : ρ₁.Le (ρ₁.setFrom second.st.next (toDyns mids)) :=
      setFrom_le ex.coherent.support _
    have choices := choiceFacts_holds (first := first) (second := second) lawful
      inv'.coherent.consistent inv'.coherent.closed (b0 := b0)
      ⟨_, (le.trans le₂) _ _ hc, by rw [hb0]; rfl⟩ (fresh mid.length second.st).1 0 (by
        intro j m em
        have look := lookupAll_setFrom ρ₁ second.st.next (toDyns mids)
        rw [toDyns_length] at look
        have e1 := lookupAll_getElem look em
        cases hd : (toDyns mids)[j]? with
        | none => rw [hd] at e1; exact absurd e1 (lookupAll_mem look m (List.mem_of_getElem? em))
        | some d =>
            rw [hd] at e1
            refine ⟨d, e1, ?_⟩
            rw [← eran, Nat.zero_add]
            have lt : j < ran.rets.length := by
              have h1 := lookupAll_length ex.rets
              have h2 := (List.getElem?_eq_some_iff.mp hd).1
              omega
            rw [le₂ _ _ (by rw [lookupAll_get ex.rets j lt, hd])])
    have inv'' : Inv M table (ρ₁.setFrom second.st.next (toDyns mids))
        ((fresh mid.length second.st).1 ++ ids) (Env.extend mids env)
        (afterChoice (localFactRules V fns) k cid first second (fresh mid.length second.st).1 mid)
        (fresh mid.length second.st).2 :=
      ⟨inv'.coherent, inv'.length, inv'.below, inv'.agree, inv'.holds.addChoices choices⟩
    have shows := ihr path _ _ _ _ _ inv'' hnone nodupR apartR
      (recorded.sub fun x m => by simp [m])
    refine ⟨shows.1, ?_⟩
    refine Process.every_mono _ _ ?_ (fun _ h => h) shows.2
    intro vs h
    obtain ⟨ρ'', le'', ex'⟩ := h
    exact ⟨ρ'', le.trans (le₂.trans le''), ex'⟩
  cases hv : env Ty.bool c with
  | true =>
      have hcv : BoolAt (localReading M) ρ cid true := ⟨_, hc, by rw [hv]; rfl⟩
      have kt : (assume (localFactRules V fns).ops st.table st.next k cid true).Holds
          (localReading M) ρ :=
        assume_holds lawful inv.coherent.consistent inv.coherent.closed st.next inv.holds hcv
      have recA : Recorded definition F (onTrue.addresses blocks) first.st :=
        ((recorded.sub fun x m => by simp [m]).strip ebr atr (fun x m mr =>
          nodup_apart nodup₁ (List.mem_append_left _ m) mr)).strip ebb atb
          (fun x m mr => nodup_apart nodupAB m mr)
      have showsT := iht path ρ ids env _ st ⟨inv.coherent, inv.length, inv.below, inv.agree, kt⟩
        (by rw [hfirst]; exact refsA) nodupA
        (apart.sub fun x m => by simp [m]) (by rw [hfirst]; exact recA)
      rw [hfirst] at showsT
      simp only [Bool.cond_true]
      refine ⟨⟨trivial, showsT.1, ?_⟩, ?_⟩
      · refine Process.every_mono _ _ ?_ (fun _ _ => trivial) showsT.2
        intro mids h
        obtain ⟨ρ₁, le, ex⟩ := h
        exact (afterRest true first (by simp) rfl hv ρ₁ mids le
          (exit_grow ex fitsB.2 fitsB.1.1)).1
      · rw [Process.every_bind]
        refine Process.every_mono _ _ ?_ (fun _ h => h) showsT.2
        intro mids h
        obtain ⟨ρ₁, le, ex⟩ := h
        exact (afterRest true first (by simp) rfl hv ρ₁ mids le
          (exit_grow ex fitsB.2 fitsB.1.1)).2
  | false =>
      have coh₁ := inv.coherent.grow fitsA.2 fitsA.1.1
      have hcv : BoolAt (localReading M) ρ cid false := ⟨_, hc, by rw [hv]; rfl⟩
      have kf : (assume (localFactRules V fns).ops first.st.table first.st.next k cid false).Holds
          (localReading M) ρ :=
        assume_holds lawful coh₁.consistent coh₁.closed first.st.next inv.holds hcv
      have recB : Recorded definition F (onFalse.addresses blocks) second.st :=
        (recorded.sub fun x m => by simp [m]).strip ebr atr (fun x m mr =>
          nodup_apart nodup₁ (List.mem_append_right _ m) mr)
      have apartB : Apart definition first.st (onFalse.addresses blocks) :=
        (apart.sub fun x m => by simp [m]).extend eba ata (fun x m mr => nodup_apart nodupAB m mr)
      have showsF := ihf path ρ ids env _ first.st
        ⟨coh₁, inv.length, fun i m => Nat.lt_of_lt_of_le (inv.below i m) fitsA.2.next,
          inv.agree, kf⟩
        (by rw [hsecond]; exact refsB) nodupB apartB (by rw [hsecond]; exact recB)
      rw [hsecond] at showsF
      simp only [Bool.cond_false]
      refine ⟨⟨trivial, showsF.1, ?_⟩, ?_⟩
      · refine Process.every_mono _ _ ?_ (fun _ _ => trivial) showsF.2
        intro mids h
        obtain ⟨ρ₁, le, ex⟩ := h
        exact (afterRest false second (by simp) rfl hv ρ₁ mids le ex).1
      · rw [Process.every_bind]
        refine Process.every_mono _ _ ?_ (fun _ h => h) showsF.2
        intro mids h
        obtain ⟨ρ₁, le, ex⟩ := h
        exact (afterRest false second (by simp) rfl hv ρ₁ mids le ex).2

end

/-! ### Case analyses -/

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}
  (definition : Key) (F : List (Place × Nat))

/-- The walk of the arms of a case analysis, from any point of a run that agrees with it, shows
the run of the arm of the alternative. -/
def ArmsSound (blocks : List (Key × Nat)) {Γ mid payloads : List V.Ty}
    (arms : Arms (localDialect V fns) Γ mid payloads) : Prop :=
  ∀ (path : List Frame) (ρ : Valuation (Dyn M)) (ids : List Nat) (env : Env M.Val Γ) (k : Known)
    (st : St V.Ty (LocalRaw V)) (p : Pick M.Val payloads), PickValid p →
    Inv M table ρ ids env k st →
    (walkArms (localFactRules V fns) definition none blocks arms ids k st).2.refusals = [] →
    (Arms.addresses blocks arms).Nodup → Apart definition st (Arms.addresses blocks arms) →
    Recorded definition F (Arms.addresses blocks arms)
      (walkArms (localFactRules V fns) definition none blocks arms ids k st).2 →
    Arms.Everywhere (localSem M fns table) (fun _ _ => True) (fun _ _ _ => True)
        (Annotation.Bounded ⟨F⟩ definition none) arms path blocks env p ∧
      (arms.denote (localSem M fns table) path env p).Every (fun _ _ => True) (fun mids =>
        ∃ ρ', ρ.Le ρ' ∧ ∃ e, e ∈ (walkArms (localFactRules V fns) definition none blocks arms ids
          k st).1 ∧ ExitInv M table ρ' e
            (walkArms (localFactRules V fns) definition none blocks arms ids k st).2 mids)
        (· ≠ .undefined)

theorem armsNil_sound (blocks : List (Key × Nat)) {Γ mid : List V.Ty} :
    ArmsSound (table := table) definition F blocks (.nil : Arms (localDialect V fns) Γ mid []) :=
  fun _ _ _ _ _ _ p => nomatch p

theorem armsCons_sound (blocks : List (Key × Nat)) {Γ mid payloads : List V.Ty} {payload : V.Ty}
    (arm : Term (localDialect V fns) (payload :: Γ) mid)
    (rest : Arms (localDialect V fns) Γ mid payloads)
    (iha : Sound (table := table) definition F blocks arm)
    (ihr : ArmsSound (table := table) definition F blocks rest) :
    ArmsSound (table := table) definition F blocks (.cons arm rest) := by
  intro path ρ ids env k st p valid inv hnone nodup apart recorded
  simp only [walkArms, localFactRules_range] at hnone recorded ⊢
  simp only [Arms.addresses] at nodup apart recorded
  obtain ⟨⟨⟨ra, ea⟩, na, eba, ata⟩, ga⟩ := walk_state (localFactRules V fns) definition none
    blocks arm ((fresh 1 st).1 ++ ids) (k.addRanges (fresh 1 st).1 [localRange payload])
    (fresh 1 st).2
  generalize he : walk (localFactRules V fns) definition none blocks arm ((fresh 1 st).1 ++ ids)
    (k.addRanges (fresh 1 st).1 [localRange payload]) (fresh 1 st).2 = e
    at hnone recorded ea eba ga ⊢
  obtain ⟨⟨⟨rr, er⟩, nr, ebr, atr⟩, gr⟩ := walkArms_state (localFactRules V fns) definition none
    blocks rest ids k e.st
  have refsE : e.st.refusals = [] := by
    rw [hnone] at er
    exact (List.append_eq_nil_iff.mp er.symm).2
  have nodupA := (List.nodup_append.mp nodup).1
  have nodupR := (List.nodup_append.mp nodup).2.1
  have fitsMade := fresh_grows 1 st inv.coherent.wf
  have fitsE := ga (by simp [fresh, inv.length])
    ⟨fitsMade.1, fun i m => by
      rcases List.mem_append.mp m with m | m
      · exact fitsMade.2.2 i m
      · exact Nat.lt_of_lt_of_le (inv.below i m) fitsMade.2.1.next⟩
  have growsE : St.Grows st e.st := fitsMade.2.1.trans fitsE.2
  have fitsR := gr inv.length ⟨fitsE.1.1, fun i m => Nat.lt_of_lt_of_le (inv.below i m)
    growsE.next⟩
  cases p with
  | here v =>
      have coh := Coherent.fresh inv.coherent [⟨payload, v⟩] (fun d m => by
        simp only [List.mem_singleton] at m
        subst m
        exact valid)
      have look : lookupAll (ρ.setFrom st.next [⟨payload, v⟩]) (fresh 1 st).1 =
          some (toDyns (HList.cons v HList.nil : HList M.Val [payload])) :=
        lookupAll_setFrom ρ st.next [⟨payload, v⟩]
      have le := setFrom_le inv.coherent.support [⟨payload, v⟩]
      have inv' : Inv M table (ρ.setFrom st.next [⟨payload, v⟩]) ((fresh 1 st).1 ++ ids)
          (Env.cons v env) (k.addRanges (fresh 1 st).1 [localRange payload]) (fresh 1 st).2 :=
        ⟨coh, by simp [fresh, inv.length], fun i m => by
          rcases List.mem_append.mp m with m | m
          · exact fitsMade.2.2 i m
          · exact Nat.lt_of_lt_of_le (inv.below i m) fitsMade.2.1.next,
          agree_extend (inv.agree.le le) (HList.cons v HList.nil) _ look,
          typeRanges_holds (inv.holds.le le) coh.valid look⟩
      have recA : Recorded definition F (arm.addresses blocks) e.st :=
        (recorded.sub fun x m => List.mem_append_left _ m).strip ebr atr
          (fun x m mr => nodup_apart nodup m mr)
      have shows := iha path _ _ _ _ _ inv' (by rw [he]; exact refsE) nodupA
        (fun q m bl key eq inA => apart q m bl key eq (List.mem_append_left _ inA))
        (by rw [he]; exact recA)
      rw [he] at shows
      refine ⟨shows.1, ?_⟩
      refine Process.every_mono _ _ ?_ (fun _ h => h) shows.2
      intro mids h
      obtain ⟨ρ₁, le₁, ex⟩ := h
      exact ⟨ρ₁, le.trans le₁, e, List.mem_cons_self, exit_grow ex fitsR.2.2 fitsR.2.1.1⟩
  | there p =>
      have apartR : Apart definition e.st (Arms.addresses blocks rest) :=
        (apart.sub fun x m => List.mem_append_right _ m).extend (by rw [eba]; rfl) ata
          (fun x m mr => nodup_apart nodup m mr)
      have shows := ihr path ρ ids env k e.st p valid
        ⟨inv.coherent.grow growsE fitsE.1.1, inv.length,
          fun i m => Nat.lt_of_lt_of_le (inv.below i m) growsE.next, inv.agree, inv.holds⟩
        hnone nodupR apartR (recorded.sub fun x m => List.mem_append_right _ m)
      refine ⟨shows.1, ?_⟩
      refine Process.every_mono _ _ ?_ (fun _ h => h) shows.2
      intro mids h
      obtain ⟨ρ₁, le₁, e', m, ex⟩ := h
      exact ⟨ρ₁, le₁, e', List.mem_cons_of_mem _ m, ex⟩

theorem cases_sound (blocks : List (Key × Nat)) {Γ outs mid payloads : List V.Ty} {t : V.Ty}
    (key : Key) (x : Var Γ t) (ok : (localDialect V fns).Alternatives () t payloads)
    (gives : ∀ a, a ∈ mid → (localDialect V fns).Gives () a)
    (arms : Arms (localDialect V fns) Γ mid payloads)
    (rest : Term (localDialect V fns) (mid ++ Γ) outs)
    (iha : ArmsSound (table := table) definition F blocks arms)
    (ihr : Sound (table := table) definition F blocks rest) :
    Sound (table := table) definition F blocks (.cases key () x ok gives arms rest) := by
  intro path ρ ids env k st inv hnone nodup apart recorded
  simp only [Shows, walk, Term.Everywhere, Term.denote] at hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  obtain ⟨⟨⟨ra, ea⟩, na, eba, ata⟩, ga⟩ := walkArms_state (localFactRules V fns) definition none
    blocks arms ids k st
  generalize hregions : walkArms (localFactRules V fns) definition none blocks arms ids k st =
    regions at hnone recorded ea eba ga ⊢
  obtain ⟨⟨⟨rr, er⟩, nr, ebr, atr⟩, _⟩ := walk_state (localFactRules V fns) definition none
    blocks rest ((fresh mid.length regions.2).1 ++ ids)
    (afterRegions (localFactRules V fns) regions.1 k (fresh mid.length regions.2).1 mid 0)
    (fresh mid.length regions.2).2
  have refsR : regions.2.refusals = [] := by
    rw [hnone] at er
    exact (List.append_eq_nil_iff.mp er.symm).2
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupA := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  have fits := ga inv.length ⟨inv.coherent.wf, inv.below⟩
  have valid := agree_valid inv.agree inv.coherent.valid
  have recA : Recorded definition F (Arms.addresses blocks arms) regions.2 :=
    (recorded.sub fun x m => by simp [m]).strip ebr atr
      (fun x m mr => nodup_apart nodup₁ m mr)
  have shows := iha path ρ ids env k st _ (localPick_valid ok (env t x) (valid t x)) inv
    (by rw [hregions]; exact refsR) nodupA (apart.sub fun x m => by simp [m])
    (by rw [hregions]; exact recA)
  rw [hregions] at shows
  have apartR : Apart definition (fresh mid.length regions.2).2 (rest.addresses blocks) :=
    (apart.sub fun x m => by simp [m]).extend eba ata (fun x m mr => nodup_apart nodup₁ m mr)
  have afterRest : ∀ (mids : HList M.Val mid), (∃ ρ', ρ.Le ρ' ∧ ∃ e, e ∈ regions.1 ∧
      ExitInv M table ρ' e regions.2 mids) →
      Shows (table := table) F definition blocks rest path (Env.extend mids env) (fun vs =>
        ∃ ρ', ρ.Le ρ' ∧ ExitInv M table ρ'
          (walk (localFactRules V fns) definition none blocks rest
            ((fresh mid.length regions.2).1 ++ ids)
            (afterRegions (localFactRules V fns) regions.1 k (fresh mid.length regions.2).1 mid 0)
            (fresh mid.length regions.2).2)
          (walk (localFactRules V fns) definition none blocks rest
            ((fresh mid.length regions.2).1 ++ ids)
            (afterRegions (localFactRules V fns) regions.1 k (fresh mid.length regions.2).1 mid 0)
            (fresh mid.length regions.2).2).st vs) := by
    intro mids h
    obtain ⟨ρ₁, le, e, he, ex⟩ := h
    have inv' := afterRegions_inv he inv le ex fits.2.2
    have shows' := ihr path _ _ _ _ _ inv' hnone nodupR apartR
      (recorded.sub fun x m => by simp [m])
    refine ⟨shows'.1, ?_⟩
    refine Process.every_mono _ _ ?_ (fun _ h => h) shows'.2
    intro vs h'
    obtain ⟨ρ'', le'', ex'⟩ := h'
    exact ⟨ρ'', le.trans ((setFrom_le ex.coherent.support _).trans le''), ex'⟩
  refine ⟨⟨trivial, shows.1, ?_⟩, ?_⟩
  · exact Process.every_mono _ _ (fun mids h => (afterRest mids h).1) (fun _ _ => trivial) shows.2
  · rw [Process.every_bind]
    exact Process.every_mono _ _ (fun mids h => (afterRest mids h).2) (fun _ h => h) shows.2

end

/-! ### Loops -/

namespace Range

theorem afterSums_zero {r₀ rt : Range} {n : Nat} (h : r₀.Has n) :
    (Range.afterSums r₀ rt 0 (some 0)).Has n := by
  obtain ⟨lo, hi⟩ := h
  refine ⟨by simp [Range.afterSums]; omega, fun h e => ?_⟩
  simp only [Range.afterSums] at e
  rcases r₀ with ⟨l₀, _ | h₀⟩ <;> rcases rt with ⟨lt, _ | ht⟩ <;> simp at e
  have := hi h₀ rfl
  omega

theorem afterSums_step {r₀ rt : Range} {i n t : Nat}
    (h : (Range.afterSums r₀ rt i (some i)).Has n) (ht : rt.Has t) :
    (Range.afterSums r₀ rt (i + 1) (some (i + 1))).Has (n + t) := by
  obtain ⟨lo, hi⟩ := h
  obtain ⟨tlo, thi⟩ := ht
  simp only [Range.afterSums] at lo hi ⊢
  refine ⟨?_, fun h e => ?_⟩
  · show r₀.lo + (i + 1) * rt.lo ≤ n + t
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rcases r₀ with ⟨l₀, _ | h₀⟩ <;> rcases rt with ⟨lt, _ | ht'⟩ <;> simp at e hi thi
  subst e
  have := hi
  have := thi
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem afterSums_widen {r₀ rt : Range} {N n low : Nat} {high : Option Nat}
    (h : (Range.afterSums r₀ rt N (some N)).Has n) (hlow : low ≤ N)
    (hhigh : ∀ m, high = some m → N ≤ m) : (Range.afterSums r₀ rt low high).Has n := by
  obtain ⟨lo, hi⟩ := h
  simp only [Range.afterSums] at lo hi ⊢
  refine ⟨Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hlow) _) lo, fun h e => ?_⟩
  rcases r₀ with ⟨l₀, _ | h₀⟩ <;> rcases high with _ | m <;> rcases rt with ⟨lt, _ | ht⟩ <;>
    simp at e hi
  subst e
  have := hhigh m rfl
  exact Nat.le_trans hi (Nat.add_le_add_left (Nat.mul_le_mul_right _ this) _)

end Range

section
variable {V : Vocabulary} {M : Model V}

theorem toDyns_append : ∀ {as bs : List V.Ty} (xs : HList M.Val as) (ys : HList M.Val bs),
    toDyns (xs.append ys) = toDyns xs ++ toDyns ys
  | [], _, .nil, _ => rfl
  | _ :: _, _, .cons x xs, ys => by simp [HList.append, toDyns, toDyns_append xs ys]

theorem all_append : ∀ {as bs : List V.Ty} (xs : HList M.Val as) (ys : HList M.Val bs),
    (xs.append ys).All M.Valid ↔ xs.All M.Valid ∧ ys.All M.Valid
  | [], _, .nil, _ => by simp [HList.append, HList.All]
  | _ :: _, _, .cons x xs, ys => by
      simp only [HList.append, HList.all_cons, all_append xs ys, and_assoc]

theorem split_append : ∀ (as : List V.Ty) {bs : List V.Ty} (xs : HList M.Val (as ++ bs)),
    (HList.split as xs).1.append (HList.split as xs).2 = xs
  | [], _, _ => rfl
  | _ :: as, _, .cons x rest => by
      simp only [HList.split, HList.append, split_append as rest]

/-- Values collected so far: as many of each type as iterations, each valid. -/
def CollectedOK : {each : List V.Ty} → HList (fun a => List (M.Val a)) each → Nat → Prop
  | [], .nil, _ => True
  | a :: _, .cons vs rest, i => vs.length = i ∧ (∀ v, v ∈ vs → M.Valid a v) ∧ CollectedOK rest i

theorem collectedOK_empties : ∀ (each : List V.Ty),
    CollectedOK (HList.empties (V := M.Val) each) 0
  | [] => trivial
  | _ :: rest => ⟨rfl, fun _ m => (nomatch m), collectedOK_empties rest⟩

theorem collectedOK_push : ∀ {each : List V.Ty} {acc : HList (fun a => List (M.Val a)) each}
    {i : Nat} {vs : HList M.Val each}, CollectedOK acc i → vs.All M.Valid →
    CollectedOK (acc.push vs) (i + 1)
  | [], .nil, _, .nil, _, _ => trivial
  | _ :: _, .cons xs rest, _, .cons v more, h, all => by
      obtain ⟨len, valid, others⟩ := h
      refine ⟨by simp [len], fun w m => ?_, collectedOK_push others (HList.all_cons.mp all).2⟩
      rcases List.mem_append.mp m with m | m
      · exact valid w m
      · simp only [List.mem_singleton] at m
        subst m
        exact (HList.all_cons.mp all).1

theorem collected_valid {fns : List (FnHeader V)} {table : FnTable M fns} (size : Option Nat)
    {n : Nat} (fits : ∀ m, size = some m → n = m) :
    ∀ {each : List V.Ty} {acc : HList (fun a => List (M.Val a)) each}, CollectedOK acc n →
      ((localSem M fns table).collected size acc).All M.Valid
  | [], .nil, _ => trivial
  | _ :: _, .cons vs rest, h => by
      obtain ⟨len, valid, others⟩ := h
      exact HList.all_cons.mpr ⟨⟨valid, fun m e => by rw [len]; exact fits m e⟩,
        collected_valid size fits others⟩

end

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}

theorem Consistent.sub {ρ : Valuation (Dyn M)} {tbl tbl' : Table (LocalRaw V)}
    (h : Consistent (LocalRun M table) ρ tbl') (sub : ∀ x, x ∈ tbl → x ∈ tbl') :
    Consistent (LocalRun M table) ρ tbl := fun x m => h x (sub x m)

theorem Closed.sub {ρ : Valuation (Dyn M)} {tbl tbl' : Table (LocalRaw V)}
    (h : Closed ρ tbl') (sub : ∀ x, x ∈ tbl → x ∈ tbl') : Closed ρ tbl := fun x m => h x (sub x m)

/-- What the types of values at identifiers say holds of them. -/
theorem addTypeRanges_holds {k : Known} {ρ : Valuation (Dyn M)}
    (hk : k.Holds (localReading M) ρ) (valid : ∀ i v, ρ i = some v → ValidDyn M v)
    {ms : List Nat} {τs : List V.Ty}
    (h : ∀ (j m : Nat), ms[j]? = some m → ∃ d, ρ m = some d ∧ τs[j]? = some d.1) :
    (k.addRanges ms (τs.map localRange)).Holds (localReading M) ρ := by
  refine hk.addRanges fun j id r e1 e2 => ?_
  obtain ⟨d, hd, hτ⟩ := h j id e1
  rw [List.getElem?_map, hτ] at e2
  simp only [Option.map_some, Option.some.injEq] at e2
  obtain ⟨n, hn, has⟩ := localRange_has e2 d.2 (valid id d hd)
  exact ⟨n, ⟨d, hd, hn⟩, has⟩

/-- The value of the count of a loop as often as a count, and what is known of its identifier. -/
theorem count_at {Γ : List V.Ty} {ρ : Valuation (Dyn M)} {ids : List Nat}
    {env : Env M.Val Γ} (agree : Agree M ρ ids env) {t : V.Ty} (count : Var Γ t)
    (ok : (localDialect V fns).Count () t) :
    NatAt (localReading M) ρ (ids.getD count.index 0)
      ((localSem M fns table).times (Times.value count ok) env) := by
  have := agree t count
  simp only [Semantics.times]
  subst ok
  exact ⟨_, this, rfl⟩

/-- How often a loop runs is between the bounds that the walk computes. -/
theorem timesBounds_ok {Γ : List V.Ty} {ρ : Valuation (Dyn M)} {ids : List Nat}
    {env : Env M.Val Γ} {k : Known} (hk : k.Holds (localReading M) ρ) (agree : Agree M ρ ids env)
    (times : Times (localDialect V fns) () Γ) :
    (timesBounds k ids times).1 ≤ (localSem M fns table).times times env ∧
      ∀ m, (timesBounds k ids times).2 = some m → (localSem M fns table).times times env ≤ m := by
  cases times with
  | fixed n => exact ⟨Nat.le_refl _, fun m e => by
      simp [timesBounds] at e; subst e; exact Nat.le_refl _⟩
  | value count ok =>
      refine ⟨Nat.zero_le _, fun m e => ?_⟩
      simp only [timesBounds] at e
      cases hr : k.rangeOf (ids.getD count.index 0) with
      | none => rw [hr] at e; cases e
      | some r =>
          rw [hr] at e
          simp only [Option.bind_some] at e
          exact (hk.rangeOf_at (count_at agree count ok) hr).2 m e

/-- What is known in the body of a loop holds at an iteration below its count. -/
theorem bodyKnown_holds {Γ carried : List V.Ty} {ρ : Valuation (Dyn M)} {ids : List Nat}
    {env : Env M.Val Γ} {k : Known} (hk : k.Holds (localReading M) ρ) (agree : Agree M ρ ids env)
    (valid : ∀ i v, ρ i = some v → ValidDyn M v) (times : Times (localDialect V fns) () Γ)
    {i index : Nat} (lt : i < (localSem M fns table).times times env)
    (hi : ρ index = some ⟨.nat, i⟩) {carriedIds : List Nat} {vs : HList M.Val carried}
    (look : lookupAll ρ carriedIds = some (toDyns vs)) :
    (bodyKnown (localFactRules V fns) k ids times index carriedIds carried).Holds
      (localReading M) ρ := by
  have hindex : NatAt (localReading M) ρ index i := ⟨_, hi, rfl⟩
  have k₁ : ((k.addRange index (indexRange k ids times)).addRange? index
      (localRange (V := V) Ty.nat)).Holds (localReading M) ρ := by
    refine (hk.addRange hindex ?_).addRange? fun r e => ⟨i, hindex, ?_⟩
    · cases times with
      | fixed n =>
          exact (Range.has_point.mpr rfl : (Range.point n).Has n).below lt
      | value count ok =>
          simp only [indexRange]
          cases hr : k.rangeOf (ids.getD count.index 0) with
          | none => exact ⟨Nat.zero_le _, fun _ e => nomatch e⟩
          | some r => exact (hk.rangeOf_at (count_at agree count ok) hr).below lt
    · simp only [localRange, Option.some.injEq] at e
      subst e
      exact ⟨Nat.zero_le _, fun _ e => nomatch e⟩
  have carriedOK : ∀ (j m : Nat), carriedIds[j]? = some m →
      ∃ d, ρ m = some d ∧ carried[j]? = some d.1 := by
    intro j m e
    have e1 := lookupAll_getElem look e
    cases hd : (toDyns vs)[j]? with
    | none => rw [hd] at e1; exact absurd e1 (lookupAll_mem look m (List.mem_of_getElem? e))
    | some d =>
        rw [hd] at e1
        exact ⟨d, e1, toDyns_typed vs j d hd⟩
  cases times with
  | fixed n =>
      simp only [bodyKnown, localFactRules_range]
      exact addTypeRanges_holds k₁ valid carriedOK
  | value count ok =>
      simp only [bodyKnown, localFactRules_range]
      exact addTypeRanges_holds (k₁.addOrder hindex (count_at agree count ok) (by simpa using lt))
        valid carriedOK

/-- The bound that a loop records is its count's upper end. -/
theorem recordBound_mem {Γ : List V.Ty} {place : Place} {k : Known} {ids : List Nat}
    {st : St V.Ty (LocalRaw V)} {times : Times (localDialect V fns) () Γ} {q : Place × Nat}
    (m : q ∈ (recordBound place k ids st times).bounds) :
    q ∈ st.bounds ∨ ∃ t, ∃ count : Var Γ t, ∃ ok, times = .value count ok ∧ q.1 = place ∧
      (k.rangeOf (ids.getD count.index 0)).bind (·.hi) = some q.2 := by
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

theorem toDyns_split {carried each : List V.Ty} (out : HList M.Val (carried ++ each)) :
    toDyns out = toDyns (HList.split carried out).1 ++ toDyns (HList.split carried out).2 := by
  conv => lhs; rw [← split_append carried out]
  exact toDyns_append _ _

end

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}

/-- The base of what is known after a loop: what the types of the collected values say. -/
theorem afterLoop_holds {e : Exit V.Ty (LocalRaw V)} {iters : Nat × Option Nat}
    {ρ : Valuation (Dyn M)} (valid : ∀ i v, ρ i = some v → ValidDyn M v) :
    ∀ (ms : List Nat) (initials : List (Option Range)) (carriedIds returns : List Nat)
      (τs : List V.Ty) (k : Known), k.Holds (localReading M) ρ →
      (∀ (j m : Nat), ms[j]? = some m → ∃ d, ρ m = some d ∧ τs[j]? = some d.1 ∧
        ∀ initial cid ret, initials[j]? = some initial → carriedIds[j]? = some cid →
          returns[j]? = some ret → ∀ r,
            carriedRange (localFactRules V fns).ops e initial cid ret iters = some r →
            ∃ n, (localReading M).nat d = some n ∧ r.Has n) →
      (afterLoop (localFactRules V fns) e k iters ms initials carriedIds returns τs).Holds
        (localReading M) ρ := by
  intro ms
  induction ms with
  | nil =>
      intro initials carriedIds returns τs k hk _
      simp only [afterLoop]
      exact hk
  | cons m ms ih =>
      intro initials carriedIds returns τs k hk h
      have base : (k.addRanges (m :: ms) (τs.map (localFactRules V fns).range)).Holds
          (localReading M) ρ := by
        rw [localFactRules_range]
        exact addTypeRanges_holds hk valid fun j m' e => by
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
                        · rw [localFactRules_range] at e2
                          obtain ⟨n, hn, has⟩ := localRange_has e2 d.2 (valid m d hd)
                          exact ⟨n, ⟨d, hd, hn⟩, has⟩
                      · intro j m' e'
                        obtain ⟨d', h1, h2, h3⟩ := h (j + 1) m' (by simpa using e')
                        exact ⟨d', h1, by simpa using h2, fun a b c ea eb ec =>
                          h3 a b c (by simpa using ea) (by simpa using eb) (by simpa using ec)⟩

/-- What the walk knows of a carried natural after a loop holds of its last value. -/
theorem carriedRange_has {e : Exit V.Ty (LocalRaw V)} {iters : Nat × Option Nat}
    {initial : Option Range} {cid ret N : Nat} {v : Dyn M}
    (lowOK : iters.1 ≤ N) (highOK : ∀ m, iters.2 = some m → N ≤ m)
    (alive : 0 < N → e.known.dead = false)
    (initialOK : N = 0 → ∀ r, initial = some r → ∃ n, (localReading M).nat v = some n ∧ r.Has n)
    (sumOK : ∀ r₀ t rt, initial = some r₀ →
      carriedTerm (localFactRules V fns).ops e cid ret = some t → e.known.rangeOf t = some rt →
      ∃ n, (localReading M).nat v = some n ∧ (Range.afterSums r₀ rt N (some N)).Has n) :
    ∀ r, carriedRange (localFactRules V fns).ops e initial cid ret iters = some r →
      ∃ n, (localReading M).nat v = some n ∧ r.Has n := by
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
  · cases ht : carriedTerm (localFactRules V fns).ops e cid ret with
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
                exact ⟨n, hn, Range.afterSums_widen has lowOK highOK⟩

/-- What holds at an iteration of a loop, of a valuation below the first identifier of its body:
it agrees with the table after the body's walk, the values are valid, as many collected values
as iterations, the body's end was reached when an iteration was, the carried values are the
initial ones before any iteration, and each carried natural that the body returns as itself
plus a term has the range of the sum so far. -/
structure LoopAt (ρ ρi : Valuation (Dyn M)) (n0 : Nat) (e : Exit V.Ty (LocalRaw V))
    (initials : List (Option Range)) (carriedIds : List Nat) {carried each : List V.Ty}
    (init0 : HList M.Val carried) (i : Nat)
    (state : HList M.Val carried × HList (fun a => List (M.Val a)) each) : Prop where
  le : ρ.Le ρi
  support : Support n0 ρi
  consistent : Consistent (LocalRun M table) ρi e.st.table
  closed : Closed ρi e.st.table
  valid : ∀ j v, ρi j = some v → ValidDyn M v
  carriedValid : state.1.All M.Valid
  collected : CollectedOK state.2 i
  alive : 0 < i → e.known.dead = false
  initial : i = 0 → state.1 = init0
  sums : ∀ (j : Nat) (r₀ : Range) (t : Nat) (rt : Range), initials[j]? = some (some r₀) →
    carriedTerm (localFactRules V fns).ops e (carriedIds.getD j 0) (e.rets.getD j 0) = some t →
    e.known.rangeOf t = some rt → ∃ d n, (toDyns state.1)[j]? = some d ∧
      (localReading M).nat d = some n ∧ (Range.afterSums r₀ rt i (some i)).Has n

end

theorem carriedTerm_spec {V : Vocabulary} {fns : List (FnHeader V)} {e : Exit V.Ty (LocalRaw V)}
    {cid ret t : Nat} (h : carriedTerm (localFactRules V fns).ops e cid ret = some t) :
    ∃ x y, e.st.table.formOf (localFactRules V fns).ops ret = some (.sum, [x, y]) ∧
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

theorem range'_getD {s n j : Nat} (h : j < n) : (List.range' s n).getD j 0 = s + j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_range' h]
  simp

theorem lookupAll_tail {Val : Type} {ρ : Valuation Val} {i : Nat} {is : List Nat} {v : Val}
    {vs : List Val} (h : lookupAll ρ (i :: is) = some (v :: vs)) : lookupAll ρ is = some vs := by
  simp only [lookupAll] at h
  split at h
  · next w ws _ e2 =>
      simp only [Option.some.injEq, List.cons.injEq] at h
      rw [e2, h.2]
  · cases h

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}
  (distinct : (fns.map (·.key)).Nodup)
  (definition : Key) (F : List (Place × Nat))

include distinct in
/-- A loop: each iteration starts from the valuation below the first identifier of its body, and
keeps what holds at an iteration; after the last, the carried naturals have the range of their
sums, and the loop has run at most as often as the bound recorded for it. -/
theorem loop_sound (blocks : List (Key × Nat)) {Γ outs carried each : List V.Ty} (key : Key)
    (times : Times (localDialect V fns) () Γ)
    (gives : ∀ a, a ∈ carried ++ each → (localDialect V fns).Gives () a)
    (init : HList (Var Γ) carried)
    (body : Term (localDialect V fns) ((localDialect V fns).index () :: (carried ++ Γ))
      (carried ++ each))
    (rest : Term (localDialect V fns)
      ((carried ++ each.map ((localDialect V fns).collected times.size)) ++ Γ) outs)
    (ihb : Sound (table := table) definition F blocks body)
    (ihr : Sound (table := table) definition F blocks rest) :
    Sound (table := table) definition F blocks (.loop key () times gives init body rest) := by
  intro path ρ ids env k st inv hnone nodup apart recorded
  have lawful := localOpFacts_lawful (table := table) distinct
  simp only [Shows, walk, Term.Everywhere, Term.denote] at hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  have notHere := (List.nodup_cons.mp nodup).1
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupB := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  have fitsIn := fresh_grows (carried.length + 1) st inv.coherent.wf
  generalize hin : fresh (carried.length + 1) st = inBody at hnone recorded fitsIn ⊢
  have in1 : inBody.1 = List.range' st.next (carried.length + 1) := by rw [← hin]; rfl
  have in2next : inBody.2.next = st.next + (carried.length + 1) := by rw [← hin]; rfl
  have in2table : inBody.2.table = st.table := by rw [← hin]; rfl
  have in2bounds : inBody.2.bounds = st.bounds := by rw [← hin]; rfl
  have headIn : inBody.1.headD 0 = st.next := by rw [in1, List.range'_succ]; rfl
  have tailIn : inBody.1.tail = List.range' (st.next + 1) carried.length := by
    rw [in1, List.range'_succ]; rfl
  obtain ⟨⟨⟨rb, eb⟩, nb, ebb, atb⟩, gb⟩ := walk_state (localFactRules V fns) definition none
    blocks body (inBody.1 ++ ids)
    (bodyKnown (localFactRules V fns) k ids times (inBody.1.headD 0) inBody.1.tail carried)
    inBody.2
  generalize he : walk (localFactRules V fns) definition none blocks body (inBody.1 ++ ids)
    (bodyKnown (localFactRules V fns) k ids times (inBody.1.headD 0) inBody.1.tail carried)
    inBody.2 = e at hnone recorded eb ebb gb ⊢
  have rbs := recordBound_state (D := localDialect V fns) ⟨definition, blocks, some key, none⟩ k
    ids e.st times
  generalize hst₁ : recordBound ⟨definition, blocks, some key, none⟩ k ids e.st times = st₁
    at hnone recorded rbs ⊢
  obtain ⟨rbt, rbn, rbr, nbd, ebd, atd⟩ := rbs
  generalize hmade : fresh (carried.length + each.length) st₁ = made at hnone recorded ⊢
  obtain ⟨⟨⟨rr, er⟩, nbr, ebr, atr⟩, _⟩ := walk_state (localFactRules V fns) definition none
    blocks rest (made.1 ++ ids)
    (afterLoop (localFactRules V fns) e k (timesBounds k ids times) made.1
      (List.map k.rangeOf (idsOf ids init)) inBody.1.tail e.rets
      (carried ++ List.map (fun t => Ty.seq t times.size) each)) made.2
  have m2r : made.2.refusals = st₁.refusals := by rw [← hmade]; rfl
  have m2b : made.2.bounds = st₁.bounds := by rw [← hmade]; rfl
  have m2t : made.2.table = st₁.table := by rw [← hmade]; rfl
  have m2n : made.2.next = st₁.next + (carried.length + each.length) := by rw [← hmade]; rfl
  have m1 : made.1 = List.range' st₁.next (carried.length + each.length) := by
    rw [← hmade]; rfl
  have refsE : e.st.refusals = [] := by
    rw [hnone, m2r, rbr] at er
    exact (List.append_eq_nil_iff.mp er.symm).2
  have fitsE := gb (by simp [in1, inv.length]; omega) ⟨fitsIn.1, fun i m => by
    rcases List.mem_append.mp m with m | m
    · exact fitsIn.2.2 i m
    · exact Nat.lt_of_lt_of_le (inv.below i m) fitsIn.2.1.next⟩
  have splitE : ∀ x, x ∈ e.st.table → x.lo + x.count ≤ st.next ∨ st.next ≤ x.lo := by
    obtain ⟨new, enew, low⟩ := fitsE.2.table
    intro x m
    rw [enew, in2table] at m
    rcases List.mem_append.mp m with m | m
    · right
      have := low x m
      rw [in2next] at this
      omega
    · left
      exact (inv.coherent.wf.mem m).2
  have argsE : ∀ x, x ∈ e.st.table → ∀ a, a ∈ x.args → a < x.lo :=
    fun x m => (fitsE.1.1.mem m).1
  have subTable : ∀ x, x ∈ st.table → x ∈ e.st.table := by
    obtain ⟨new, enew, _⟩ := fitsE.2.table
    intro x m
    rw [enew, in2table]
    exact List.mem_append_right _ m
  have apartB : Apart definition inBody.2 (body.addresses blocks) := fun q m bl key' eq inB =>
    apart q (by rw [in2bounds] at m; exact m) bl key' eq
      (List.mem_cons_of_mem _ (List.mem_append_left _ inB))
  have recB : Recorded definition F (body.addresses blocks) e.st :=
    ((recorded.sub fun x m => List.mem_cons_of_mem _ (List.mem_append_left _ m)).strip ebr atr
      (fun x m mr => nodup_apart nodup₁ m mr)).strip (by rw [m2b, ebd])
      (Bnew := [(blocks, key)]) (fun q m => ⟨blocks, key, atd q m, List.mem_singleton_self _⟩)
      (fun x m mr => by
        simp only [List.mem_singleton] at mr
        subst mr
        exact notHere (List.mem_append_left _ m))
  -- the body at an iteration
  have bodyInv : ∀ (i : Nat) (state : HList M.Val carried × HList (fun a => List (M.Val a)) each)
      (ρi : Valuation (Dyn M)), i < (localSem M fns table).times times env →
      LoopAt (table := table) ρ ρi st.next e (List.map k.rangeOf (idsOf ids init)) inBody.1.tail
        (env.all init) i state →
      Inv M table (ρi.setFrom st.next (toDyns (HList.cons (a := Ty.nat) i state.1)))
        (inBody.1 ++ ids) (Env.cons (a := Ty.nat) i (Env.extend state.1 env))
        (bodyKnown (localFactRules V fns) k ids times (inBody.1.headD 0) inBody.1.tail carried)
        inBody.2 := by
    intro i state ρi lt la
    have validL : ∀ v, v ∈ toDyns (HList.cons (a := Ty.nat) i state.1) → ValidDyn M v :=
      toDyns_valid (HList.all_cons.mpr ⟨trivial, la.carriedValid⟩)
    have lenL : (toDyns (HList.cons (a := Ty.nat) i state.1)).length = carried.length + 1 := by
      rw [toDyns_length]; rfl
    have le₁ := setFrom_le la.support (toDyns (HList.cons (a := Ty.nat) i state.1))
    have look : lookupAll (ρi.setFrom st.next (toDyns (HList.cons (a := Ty.nat) i state.1)))
        inBody.1 = some (toDyns (HList.cons (a := Ty.nat) i state.1)) := by
      rw [in1, ← lenL]
      exact lookupAll_setFrom _ _ _
    obtain ⟨cons, clo⟩ := consistent_setFrom inv.coherent.wf (la.consistent.sub subTable)
      (la.closed.sub subTable) (toDyns (HList.cons (a := Ty.nat) i state.1))
    have validS := setFrom_valid (lo := st.next) la.valid validL
    refine ⟨⟨?_, ?_, ?_, ?_, validS⟩, ?_, ?_, ?_, ?_⟩
    · rw [in2next, ← lenL]
      exact setFrom_support la.support _
    · rw [in2next, in2table]
      exact inv.coherent.wf.mono (by omega)
    · rw [in2table]; exact cons
    · rw [in2table]; exact clo
    · simp [in1, inv.length]; omega
    · intro j m
      rcases List.mem_append.mp m with m | m
      · exact fitsIn.2.2 j m
      · exact Nat.lt_of_lt_of_le (inv.below j m) fitsIn.2.1.next
    · exact agree_extend (inv.agree.le (la.le.trans le₁)) (HList.cons (a := Ty.nat) i state.1)
        inBody.1 look
    · have hi : (ρi.setFrom st.next (toDyns (HList.cons (a := Ty.nat) i state.1)))
          (inBody.1.headD 0) = some ⟨.nat, i⟩ := by
        rw [headIn]
        have := setFrom_at ρi st.next (toDyns (HList.cons (a := Ty.nat) i state.1)) 0
          (by rw [lenL]; omega)
        rw [Nat.add_zero] at this
        rw [this]
        rfl
      have lookC : lookupAll (ρi.setFrom st.next (toDyns (HList.cons (a := Ty.nat) i state.1)))
          inBody.1.tail = some (toDyns state.1) := by
        have shape : inBody.1 = st.next :: inBody.1.tail := by
          rw [tailIn, in1, List.range'_succ]
        rw [shape] at look
        exact lookupAll_tail look
      exact bodyKnown_holds (inv.holds.le (la.le.trans le₁)) (inv.agree.le (la.le.trans le₁))
        validS times lt hi lookC
  have bodyShows : ∀ (i : Nat)
      (state : HList M.Val carried × HList (fun a => List (M.Val a)) each)
      (ρi : Valuation (Dyn M)), i < (localSem M fns table).times times env →
      LoopAt (table := table) ρ ρi st.next e (List.map k.rangeOf (idsOf ids init)) inBody.1.tail
        (env.all init) i state →
      Shows (table := table) F definition blocks body (path ++ [.iteration key i])
        (Env.cons (a := Ty.nat) i (Env.extend state.1 env)) (fun out => ∃ ρ',
          (ρi.setFrom st.next (toDyns (HList.cons (a := Ty.nat) i state.1))).Le ρ' ∧
          ExitInv M table ρ' e e.st out) := by
    intro i state ρi lt la
    have shows := ihb (path ++ [.iteration key i]) _ _ _ _ _ (bodyInv i state ρi lt la)
      (by rw [he]; exact refsE) nodupB apartB (by rw [he]; exact recB)
    rw [he] at shows
    exact shows
  -- one iteration keeps what holds
  have keeps : ∀ (i : Nat) (state : (localSem M fns table).LoopState carried each),
      i < (localSem M fns table).times times env →
      (∃ ρi, LoopAt (table := table) ρ ρi st.next e (List.map k.rangeOf (idsOf ids init))
        inBody.1.tail (env.all init) i state) →
      ((localSem M fns table).loopStep () (fun path' env' =>
          Term.denote (localSem M fns table) body path' env') key path env i state).Every
        (fun _ _ => True) (fun state' => ∃ ρi, LoopAt (table := table) ρ ρi st.next e
          (List.map k.rangeOf (idsOf ids init)) inBody.1.tail (env.all init) (i + 1) state')
        (· ≠ .undefined) := by
    intro i state lt h
    obtain ⟨ρi, la⟩ := h
    have shows := bodyShows i state ρi lt la
    simp only [Semantics.loopStep]
    rw [Process.every_bind]
    refine Process.every_mono _ _ ?_ (fun _ h => h) shows.2
    intro out h
    obtain ⟨ρ', le', ex⟩ := h
    simp only [Process.Every]
    have lenL : (toDyns (HList.cons (a := Ty.nat) i state.1)).length = carried.length + 1 := by
      rw [toDyns_length]; rfl
    have le₁ := setFrom_le la.support (toDyns (HList.cons (a := Ty.nat) i state.1))
    have outValid : out.All M.Valid :=
      valid_of_toDyns (lookupAll_valid ex.rets ex.coherent.valid)
    have parts := (all_append _ _).mp
      (by rw [split_append]; exact outValid :
        ((HList.split carried out).1.append (HList.split carried out).2).All M.Valid)
    obtain ⟨cons, clo⟩ := consistent_below splitE argsE ex.coherent.consistent ex.coherent.closed
    refine ⟨ρ'.below st.next, below_le inv.coherent.support (la.le.trans (le₁.trans le')),
      below_support _ _, cons, clo,
      fun j v h => ex.coherent.valid j v (below_self_le ρ' st.next j v h), parts.1,
      collectedOK_push la.collected parts.2, fun _ => ex.holds.alive,
      fun h => absurd h (Nat.succ_ne_zero i), ?_⟩
    intro j r₀ t rt hinit hterm hrt
    have jlt : j < carried.length := by
      have := (List.getElem?_eq_some_iff.mp hinit).1
      simp only [List.length_map, idsOf_length] at this
      exact this
    obtain ⟨d₀, n₀, hd₀, hn₀, has₀⟩ := la.sums j r₀ t rt hinit hterm hrt
    have retLt : j < e.rets.length := by
      have h1 := lookupAll_length ex.rets
      rw [toDyns_length] at h1
      have h2 := List.length_append (as := carried) (bs := each)
      omega
    have hret : ρ' (e.rets.getD j 0) = (toDyns out)[j]? := lookupAll_get ex.rets j retLt
    have outSplit : (toDyns out)[j]? = (toDyns (HList.split carried out).1)[j]? := by
      rw [toDyns_split out, List.getElem?_append_left (by rw [toDyns_length]; exact jlt)]
    have hcid : ρ' (inBody.1.tail.getD j 0) = some d₀ := by
      rw [tailIn, range'_getD jlt]
      have := setFrom_at ρi st.next (toDyns (HList.cons (a := Ty.nat) i state.1)) (j + 1)
        (by rw [lenL]; omega)
      rw [show st.next + (j + 1) = st.next + 1 + j by omega] at this
      apply le'
      rw [this]
      exact hd₀
    cases hv : (toDyns (HList.split carried out).1)[j]? with
    | none =>
        have := (List.getElem?_eq_none_iff.mp hv)
        rw [toDyns_length] at this
        exfalso
        omega
    | some dv =>
        rw [outSplit, hv] at hret
        obtain ⟨x, y, hform, which⟩ := carriedTerm_spec hterm
        obtain ⟨vals, hvals, a, b, xa, yb, eqv, ha, hb, hsum⟩ :=
          formOf_values lawful ex.coherent.consistent ex.coherent.closed hform hret
        obtain ⟨va, vb, rfl, hxa, hyb⟩ := lookupAll_pair hvals
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
  have I0 : ∃ ρi, LoopAt (table := table) ρ ρi st.next e (List.map k.rangeOf (idsOf ids init))
      inBody.1.tail (env.all init) 0 (env.all init, HList.empties each) := by
    obtain ⟨new, enew, low⟩ := fitsE.2.table
    have ext := consistent_extend inv.coherent.support inv.coherent.consistent inv.coherent.closed
      (new := new) (fun x m => by have := low x m; rw [in2next] at this; omega)
    rw [← in2table, ← enew] at ext
    refine ⟨ρ, Valuation.Le.refl ρ, inv.coherent.support, ext.1, ext.2, inv.coherent.valid,
      env_all_valid (agree_valid inv.agree inv.coherent.valid) init, collectedOK_empties each,
      fun h => absurd h (Nat.lt_irrefl 0), fun _ => rfl, ?_⟩
    intro j r₀ t rt hinit _ _
    rw [List.getElem?_map] at hinit
    cases hid : (idsOf ids init)[j]? with
    | none => rw [hid] at hinit; cases hinit
    | some id =>
        rw [hid] at hinit
        simp only [Option.map_some, Option.some.injEq] at hinit
        obtain ⟨n, ⟨d, hd, hn⟩, has⟩ := inv.holds.rangeOf hinit
        have := lookupAll_getElem (lookupAll_idsOf inv.agree init) hid
        rw [hd] at this
        exact ⟨d, n, this.symm, hn, Range.afterSums_zero has⟩
  -- after the last iteration
  have apartR : Apart definition made.2 (rest.addresses blocks) := by
    intro q m bl key' eq inR
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
      · rw [in2bounds] at m
        exact apart q m bl key' eq (List.mem_cons_of_mem _ (List.mem_append_right _ inR))
  have afterRest : ∀ (state : (localSem M fns table).LoopState carried each),
      (∃ ρi, LoopAt (table := table) ρ ρi st.next e (List.map k.rangeOf (idsOf ids init))
        inBody.1.tail (env.all init) ((localSem M fns table).times times env) state) →
      Shows (table := table) F definition blocks rest path
        (Env.extend (state.1.append ((localSem M fns table).collected times.size state.2)) env)
        (fun vs => ∃ ρ', ρ.Le ρ' ∧ ExitInv M table ρ'
          (walk (localFactRules V fns) definition none blocks rest (made.1 ++ ids)
            (afterLoop (localFactRules V fns) e k (timesBounds k ids times) made.1
              (List.map k.rangeOf (idsOf ids init)) inBody.1.tail e.rets
              (carried ++ List.map (fun t => Ty.seq t times.size) each)) made.2)
          (walk (localFactRules V fns) definition none blocks rest (made.1 ++ ids)
            (afterLoop (localFactRules V fns) e k (timesBounds k ids times) made.1
              (List.map k.rangeOf (idsOf ids init)) inBody.1.tail e.rets
              (carried ++ List.map (fun t => Ty.seq t times.size) each)) made.2).st vs) := by
    intro state h
    obtain ⟨ρN, la⟩ := h
    have fits : ∀ m, times.size = some m → (localSem M fns table).times times env = m := by
      intro m e'
      cases times with
      | fixed n => simp only [Times.size, Option.some.injEq] at e'; subst e'; rfl
      | value => cases e'
    have validR : (state.1.append ((localSem M fns table).collected times.size state.2)).All
        M.Valid :=
      (all_append _ _).mpr ⟨la.carriedValid, collected_valid times.size fits la.collected⟩
    have lenR : (toDyns (state.1.append
        ((localSem M fns table).collected times.size state.2))).length =
        carried.length + each.length := by
      rw [toDyns_length]
      simp
    have nextLe : st.next ≤ e.st.next := Nat.le_trans fitsIn.2.1.next fitsE.2.next
    have cohN : Coherent (LocalRun M table) (ValidDyn M) ρN st₁ :=
      ⟨by rw [rbn]; exact la.support.mono nextLe, by rw [rbt, rbn]; exact fitsE.1.1,
        by rw [rbt]; exact la.consistent, by rw [rbt]; exact la.closed, la.valid⟩
    have coh₂ := Coherent.fresh cohN _ (toDyns_valid validR)
    rw [lenR, hmade] at coh₂
    have le₂ := setFrom_le cohN.support (toDyns (state.1.append
      ((localSem M fns table).collected times.size state.2)))
    have look : lookupAll (ρN.setFrom st₁.next (toDyns (state.1.append
        ((localSem M fns table).collected times.size state.2)))) made.1 =
        some (toDyns (state.1.append ((localSem M fns table).collected times.size state.2))) := by
      rw [m1, ← lenR]
      exact lookupAll_setFrom _ _ _
    have le := la.le.trans le₂
    have bounds := timesBounds_ok (table := table) inv.holds inv.agree times
    have inv' : Inv M table (ρN.setFrom st₁.next (toDyns (state.1.append
        ((localSem M fns table).collected times.size state.2)))) (made.1 ++ ids)
        (Env.extend (state.1.append ((localSem M fns table).collected times.size state.2)) env)
        (afterLoop (localFactRules V fns) e k (timesBounds k ids times) made.1
          (List.map k.rangeOf (idsOf ids init)) inBody.1.tail e.rets
          (carried ++ List.map (fun t => Ty.seq t times.size) each)) made.2 := by
      refine ⟨coh₂, ?_, ?_, agree_extend (inv.agree.le le) _ made.1 look, ?_⟩
      · rw [m1]; simp [inv.length, Nat.add_assoc]
      · intro i m
        rcases List.mem_append.mp m with m | m
        · rw [m1] at m
          have m := mem_range'_bounds m
          rw [m2n]
          omega
        · rw [m2n, rbn]
          exact Nat.lt_of_lt_of_le (inv.below i m) (Nat.le_trans nextLe (Nat.le_add_right _ _))
      · apply afterLoop_holds coh₂.valid _ _ _ _ _ k (inv.holds.le le)
        intro j m em
        have e1 := lookupAll_getElem look em
        cases hd : (toDyns (state.1.append
            ((localSem M fns table).collected times.size state.2)))[j]? with
        | none => rw [hd] at e1; exact absurd e1 (lookupAll_mem look m (List.mem_of_getElem? em))
        | some d =>
            rw [hd] at e1
            refine ⟨d, e1, toDyns_typed _ j d hd, fun initial cid ret hinit hcid hret => ?_⟩
            have jlt : j < carried.length := by
              have := (List.getElem?_eq_some_iff.mp hinit).1
              simp only [List.length_map, idsOf_length] at this
              exact this
            have hdj : (toDyns state.1)[j]? = some d := by
              rw [toDyns_append, List.getElem?_append_left (by rw [toDyns_length]; exact jlt)] at hd
              exact hd
            refine carriedRange_has bounds.1 bounds.2 la.alive ?_ ?_
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
                  have := lookupAll_getElem (lookupAll_idsOf inv.agree init) hid
                  rw [hd', hdj] at this
                  cases this
                  exact ⟨n, hn, has⟩
            · intro r₀ t rt hr₀ ht hrt
              have hcidD : inBody.1.tail.getD j 0 = cid := by
                rw [List.getD_eq_getElem?_getD, hcid]; rfl
              have hretD : e.rets.getD j 0 = ret := by
                rw [List.getD_eq_getElem?_getD, hret]; rfl
              rw [← hcidD, ← hretD] at ht
              obtain ⟨d', n, hd', hn, has⟩ := la.sums j r₀ t rt (by rw [hinit, hr₀]) ht hrt
              rw [hdj] at hd'
              cases hd'
              exact ⟨n, hn, has⟩
    have shows := ihr path _ _ _ _ _ inv' hnone nodupR apartR
      (recorded.sub fun x m => List.mem_cons_of_mem _ (List.mem_append_right _ m))
    refine ⟨shows.1, ?_⟩
    refine Process.every_mono _ _ ?_ (fun _ h => h) shows.2
    intro vs h'
    obtain ⟨ρ'', le'', ex'⟩ := h'
    exact ⟨ρ'', le.trans le'', ex'⟩
  have all := Process.every_iterate_below (fun _ _ => True) (· ≠ .undefined)
    ((localSem M fns table).loopStep () (fun path' env' =>
      Term.denote (localSem M fns table) body path' env') key path env)
    (fun i state => ∃ ρi, LoopAt (table := table) ρ ρi st.next e
      (List.map k.rangeOf (idsOf ids init)) inBody.1.tail (env.all init) i state)
    ((localSem M fns table).times times env) keeps
  refine ⟨⟨trivial, ?_, ?_, ?_⟩, ?_⟩
  · intro bound hb
    simp only [Annotation.boundAt, Option.map_eq_some_iff] at hb
    obtain ⟨q, hq, rfl⟩ := hb
    have mq := List.mem_of_find?_eq_some hq
    have pq : q.1 = ⟨definition, blocks, some key, none⟩ := by
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
    · rw [m2b, ← hst₁] at m
      rcases recordBound_mem m with m | ⟨t, count, ok, htimes, _, hb'⟩
      · rw [ebb] at m
        rcases List.mem_append.mp m with m | m
        · obtain ⟨bl, key', eq, mem⟩ := atb _ m
          rw [pq] at eq
          simp only [Place.mk.injEq, Option.some.injEq, true_and, and_true] at eq
          obtain ⟨rfl, rfl⟩ := eq
          exact (notHere (List.mem_append_left _ mem)).elim
        · rw [in2bounds] at m
          exact (apart _ m blocks key pq List.mem_cons_self).elim
      · subst htimes
        cases hr : k.rangeOf (ids.getD count.index 0) with
        | none => rw [hr] at hb'; cases hb'
        | some r =>
            rw [hr] at hb'
            simp only [Option.bind_some] at hb'
            exact (inv.holds.rangeOf_at (count_at inv.agree count ok) hr).2 _ hb'
  · intro i lt
    refine Process.every_mono _ _ ?_ (fun _ _ => trivial)
      (all i 0 (env.all init, HList.empties each) (by omega) I0)
    intro state h
    rw [Nat.zero_add] at h
    obtain ⟨ρi, la⟩ := h
    exact (bodyShows i state ρi lt la).1
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

/-! ## The theorem for a function -/

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}
  (definition : Key) (F : List (Place × Nat))

mutual
  /-- The walk of every term is sound. -/
  theorem walk_sound (distinct : (fns.map (·.key)).Nodup)
      (safe : ∀ hdr (callee : Var fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
        (table hdr callee args).Stops (· ≠ .undefined))
      (keeps : FnTable.KeepsValidity table) :
      ∀ (blocks : List (Key × Nat)) {Γ outs : List V.Ty}
      (t : Term (localDialect V fns) Γ outs), Sound (table := table) definition F blocks t
    | _, _, _, .ret xs => ret_sound definition F _ xs
    | blocks, _, _, .op key o args rest =>
        op_sound distinct safe keeps definition F blocks key o args rest
          (walk_sound distinct safe keeps blocks rest)
    | blocks, _, _, .guard key () c ok why rest =>
        guard_sound distinct definition F blocks key c ok why rest
          (walk_sound distinct safe keeps blocks rest)
    | blocks, _, _, .choose key () c ok gives onTrue onFalse rest =>
        choose_sound distinct definition F blocks key c ok gives onTrue onFalse rest
          (walk_sound distinct safe keeps blocks onTrue)
          (walk_sound distinct safe keeps blocks onFalse)
          (walk_sound distinct safe keeps blocks rest)
    | blocks, _, _, .cases key () x ok gives arms rest =>
        cases_sound definition F blocks key x ok gives arms rest
          (walkArms_sound distinct safe keeps blocks arms)
          (walk_sound distinct safe keeps blocks rest)
    | blocks, _, _, .loop key () times gives init body rest =>
        loop_sound distinct definition F blocks key times gives init body rest
          (walk_sound distinct safe keeps blocks body) (walk_sound distinct safe keeps blocks rest)
    | blocks, _, _, .block key number body rest =>
        block_sound definition F blocks key number body rest
          (walk_sound distinct safe keeps (blocks ++ [(key, number)]) body)
          (walk_sound distinct safe keeps blocks rest)
    | blocks, _, _, .attempt key w owns body rest =>
        attempt_sound definition F blocks key w owns body rest
  /-- The walk of the arms of every case analysis is sound. -/
  theorem walkArms_sound (distinct : (fns.map (·.key)).Nodup)
      (safe : ∀ hdr (callee : Var fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
        (table hdr callee args).Stops (· ≠ .undefined))
      (keeps : FnTable.KeepsValidity table) :
      ∀ (blocks : List (Key × Nat)) {Γ mid payloads : List V.Ty}
      (arms : Arms (localDialect V fns) Γ mid payloads),
      ArmsSound (table := table) definition F blocks arms
    | blocks, _, _, _, .nil => armsNil_sound definition F blocks
    | blocks, _, _, _, .cons arm rest =>
        armsCons_sound definition F blocks arm rest (walk_sound distinct safe keeps blocks arm)
          (walkArms_sound distinct safe keeps blocks rest)
end

end

section
variable {V : Vocabulary} {M : Model V} {fns : List (FnHeader V)} {table : FnTable M fns}

theorem toDyns_ofList : ∀ {Γ : List V.Ty} (ins : HList M.Val Γ) {τ : V.Ty} (x : Var Γ τ),
    (toDyns ins)[x.index]? = some ⟨τ, Env.ofList ins τ x⟩
  | _ :: _, .cons _ _, _, .head => rfl
  | _ :: _, .cons _ rest, _, .tail x => by
      simp only [toDyns, Var.index, List.getElem?_cons_succ]
      exact toDyns_ofList rest x

/-- At the start of a body: the inputs have the first identifiers, and the table is empty. -/
theorem start_inv {Γ : List V.Ty} (ins : HList M.Val Γ) (valid : ins.All M.Valid) :
    Inv M table (Valuation.setFrom (fun _ => none : Valuation (Dyn M)) 0 (toDyns ins))
      (List.range Γ.length) (Env.ofList ins)
      (Known.empty.addRanges (List.range Γ.length) (List.map (localFactRules V fns).range Γ))
      ⟨[], Γ.length, [], []⟩ := by
  have support : Support Γ.length
      (Valuation.setFrom (fun _ => none : Valuation (Dyn M)) 0 (toDyns ins)) := by
    have := setFrom_support (ρ := (fun _ => none : Valuation (Dyn M))) (lo := 0)
      (fun _ _ => rfl) (toDyns ins)
    rw [Nat.zero_add, toDyns_length] at this
    exact this
  have validS := setFrom_valid (Valid := ValidDyn M) (ρ := (fun _ => none : Valuation (Dyn M)))
    (lo := 0) (fun _ _ e => by cases e) (toDyns_valid valid)
  have at_ : ∀ j, j < Γ.length →
      (Valuation.setFrom (fun _ => none : Valuation (Dyn M)) 0 (toDyns ins)) j =
        (toDyns ins)[j]? := by
    intro j lt
    have := setFrom_at (fun _ => none : Valuation (Dyn M)) 0 (toDyns ins) j
      (by rw [toDyns_length]; exact lt)
    rw [Nat.zero_add] at this
    exact this
  refine ⟨⟨support, trivial, fun _ m => (nomatch m), fun _ m => (nomatch m), validS⟩, by simp,
    fun i m => List.mem_range.mp m, fun τ x => ?_, ?_⟩
  · have lt := Var.index_lt x
    rw [List.getD_eq_getElem?_getD, List.getElem?_range lt, Option.getD_some, at_ _ lt]
    exact toDyns_ofList ins x
  · rw [localFactRules_range]
    have empty : Known.empty.Holds (localReading M)
        (Valuation.setFrom (fun _ => none : Valuation (Dyn M)) 0 (toDyns ins)) :=
      ⟨rfl, fun _ _ m => by simp [Known.empty] at m, fun _ _ _ m => by simp [Known.empty] at m,
        fun _ _ m => by simp [Known.empty] at m, fun _ m => by simp [Known.empty] at m⟩
    refine addTypeRanges_holds empty validS fun j m e => ?_
    have lt := (List.getElem?_eq_some_iff.mp e).1
    rw [List.length_range] at lt
    rw [List.getElem?_range lt, Option.some.injEq] at e
    subst e
    rw [at_ _ lt]
    cases hd : (toDyns ins)[j]? with
    | none =>
        have := List.getElem?_eq_none_iff.mp hd
        rw [toDyns_length] at this
        omega
    | some d => exact ⟨d, rfl, toDyns_typed ins j d hd⟩

/-- **The check of facts is sound for a function.** For a body with distinct addresses that the
check of facts accepts with some bounds, against callees with distinct keys that never stop
`undefined` on valid inputs and keep validity, on valid inputs: the process never stops
`undefined`, what it returns is valid, and every loop as often as a count runs at most the bound
that an annotation gives its place, for every annotation whose entries at the definition's places
are among those bounds. -/
theorem checkFacts_sound (distinct : (fns.map (·.key)).Nodup)
    (safe : ∀ hdr (callee : Var fns hdr) (args : HList M.Val hdr.ins), args.All M.Valid →
      (table hdr callee args).Stops (· ≠ .undefined))
    (keeps : FnTable.KeepsValidity table) (definition : Key) {Γ outs : List V.Ty}
    (body : Term (localDialect V fns) Γ outs) (hdistinct : Term.Distinct body)
    {bounds : List (Place × Nat)}
    (accepted : checkFacts (localFactRules V fns) definition none body = .ok bounds)
    (F : List (Place × Nat))
    (hF : ∀ p b, (p, b) ∈ F → p.definition = definition → p.role = none → (p, b) ∈ bounds)
    (ins : HList M.Val Γ) (valid : ins.All M.Valid) :
    body.Everywhere (localSem M fns table) (fun _ _ => True) (fun _ _ _ => True)
        (Annotation.Bounded ⟨F⟩ definition none) [] [] (Env.ofList ins) ∧
      (body.denote (localSem M fns table) [] (Env.ofList ins)).Every (fun _ _ => True)
        (fun outs => outs.All M.Valid) (· ≠ .undefined) := by
  have inv := start_inv (table := table) ins valid
  simp only [checkFacts] at accepted
  generalize he : walk (localFactRules V fns) definition none [] body (List.range Γ.length)
    (Known.empty.addRanges (List.range Γ.length) (List.map (localFactRules V fns).range Γ))
    ⟨[], Γ.length, [], []⟩ = e at accepted
  split at accepted
  · next hr =>
      simp only [Except.ok.injEq] at accepted
      have nodup : (body.addresses []).Nodup := by
        simp only [Term.Distinct, Bool.and_eq_true, decide_eq_true_eq] at hdistinct
        exact hdistinct.1
      have shows := walk_sound definition F distinct safe keeps [] body [] _ _ _ _ _ inv
        (by rw [he]; exact hr) nodup (fun _ m => nomatch m) (by
          rw [he]
          intro p b bl key m eq _
          have := hF p b m (by rw [eq]) (by rw [eq])
          rw [← accepted, List.mem_reverse] at this
          exact this)
      refine ⟨shows.1, Process.every_mono _ _ (fun outs h => ?_) (fun _ h => h) shows.2⟩
      obtain ⟨ρ', _, ex⟩ := h
      exact valid_of_toDyns (lookupAll_valid ex.rets ex.coherent.valid)
  · cases accepted

/-- The bounds that the check of facts gives a body are at the definition's places. -/
theorem checkFacts_places (definition : Key) {Γ outs : List V.Ty}
    (body : Term (localDialect V fns) Γ outs) {bounds : List (Place × Nat)}
    (accepted : checkFacts (localFactRules V fns) definition none body = .ok bounds) :
    ∀ q, q ∈ bounds → q.1.definition = definition ∧ q.1.role = none := by
  simp only [checkFacts] at accepted
  obtain ⟨_, new, enew, at_⟩ := (walk_state (localFactRules V fns) definition none [] body
    (List.range Γ.length)
    (Known.empty.addRanges (List.range Γ.length) (List.map (localFactRules V fns).range Γ))
    ⟨[], Γ.length, [], []⟩).1
  split at accepted
  · simp only [Except.ok.injEq] at accepted
    intro q m
    rw [← accepted, List.mem_reverse, enew, List.append_nil] at m
    obtain ⟨bl, key, eq, _⟩ := at_ q m
    rw [eq]
    exact ⟨rfl, rfl⟩
  · cases accepted

end

end

end FactCheck

end Zkc.Core

#print axioms Zkc.Core.FactCheck.checkFacts_sound
