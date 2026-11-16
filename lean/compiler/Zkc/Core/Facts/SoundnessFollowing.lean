module

public import Zkc.Core.Facts.Soundness

@[expose] public section

/-!
The walk of the analysis is sound while it follows a skeleton, for any dialect and any semantics
that satisfy the laws of `FactRules.Lawful` (`Facts/Laws.lean`).

A walk that follows a skeleton and adds no place that differs finds, at each instruction that it
keeps in order, the skeleton's entry (`found_of_differs`, `Facts/Growth.lean`): it takes the
entry's leaves and follows the entry's regions. The leaves are made in order (`Skel.Ordered`), below the next identifier and
apart from the table; along a run, every identifier from the first leaf not yet reached on that
has a value is a result of an entry of the table (`Quiet`). So setting a leaf never changes a
value (`leaves_at`): the leaf has none, the entries whose results it is are none, and an entry
that reads it has no result with a value while it has none (`Coherent.setAt`). What the walk
values on its way is entry results (`Fills`: `share_fills`, `checkRequirements_fills`) and leaves
that it passed, which keeps `Quiet`.
-/

namespace Zkc.Core.Analysis.Facts

open FactCheck


/-! ## Values at the leaves of a followed entry -/

section
variable {D : Dialect} {Raw : Type} {σ : Setting D Raw}

/-- Values set at leaves of a followed entry, which have no value and are no results of entries,
keep the state and the valuation in agreement; the leaves have them, and every identifier above
them that has a value is still a result of an entry. -/
theorem leaves_at {ρ : Valuation σ.sem.Dyn} {st : St D.Ty Raw}
    (coh : Coherent σ.Runs σ.Valid ρ st) {lo base : Nat} (vs : List σ.sem.Dyn)
    (valid : ∀ v, v ∈ vs → σ.Valid v) (inside : base + vs.length ≤ st.next)
    (apart : LeavesApart st.table base vs.length) (quiet : Quiet lo ρ st.table) (low : lo ≤ base) :
    Coherent σ.Runs σ.Valid (ρ.setFrom base vs) st ∧ ρ.Le (ρ.setFrom base vs) ∧
      valuesOf (ρ.setFrom base vs) (List.range' base vs.length) = some vs ∧
      Quiet (base + vs.length) (ρ.setFrom base vs) st.table := by
  obtain ⟨coh', le⟩ := Coherent.setAt coh vs valid inside apart (quiet.unvalued apart low)
  exact ⟨coh', le, valuesOf_setFrom ρ base vs, quiet.setFrom low vs⟩

end

/-! ## Each construct, while a skeleton is followed -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] {σ : Setting D Raw} (laws : σ.Lawful)

theorem ret_follow (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs : List D.Ty}
    (xs : HList (Var Γ) outs) (skel : Skel D outs) : Sound σ blocks (.ret xs) (some skel) := by
  intro path ρ ids env k s lo hi inv following differs _ _ _ _
  simp only [walk, Option.isSome_some, Option.map_some, Option.getD_some] at differs ⊢
  have found := found_of_differs ⟨[], rfl⟩ differs
  simp only [found, miss_found]
  obtain ⟨ordered, _, _, quiet⟩ := following
  rw [Option.some.inj (retEntry_hit (followed := some skel) found)] at ordered
  simp only [Shows, Term.EveryLoop, Term.denote, Process.Every]
  exact ⟨trivial, ρ, Valuation.Le.refl ρ, ⟨inv.coherent, valuesOf_idsOf inv.agree xs, inv.holds⟩,
    quiet.low ordered⟩

include laws in
/-- An operation, while a skeleton is followed: its requirements are as when none is followed; a
shared operation is as when none is followed, and leaves the skeleton where it is; an operation
kept in order finds its entry, whose leaves get its results. -/
theorem op_follow (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs ins res : List D.Ty}
    (key : Key) (o : D.Op ins res) (args : HList (Var Γ) ins) (results : Names res)
    (rest : Term D (Γ.extend results) outs) (ih : ∀ skel, Sound σ blocks rest (some skel))
    (skel : Skel D outs) : Sound σ blocks (.op key o args results rest) (some skel) := by
  intro path ρ ids env k s lo hi inv following differs hnone nodup apart recorded
  have nodup' := (List.nodup_cons.mp nodup).2
  have recorded' := fun (st : St D.Ty Raw) (h : Recorded σ (Term.addresses blocks
    (.op key o args results rest)) st) =>
      Recorded.sub (σ := σ) h fun _ m => List.mem_cons_of_mem _ m
  obtain ⟨ordered, below, apartSkel, quiet⟩ := following
  obtain ⟨-, b₁⟩ := checkRequirements_state σ.rules.ops k ⟨σ.definition, blocks, some key, σ.role⟩
    (σ.rules.written o) (idsOf ids args) (σ.rules.ops.requires (σ.rules.written o)) s.st
  obtain ⟨-, g₁⟩ := checkRequirements_grows σ.rules.ops k ⟨σ.definition, blocks, some key, σ.role⟩
    (σ.rules.written o) (idsOf ids args) (σ.rules.ops.requires (σ.rules.written o)) s.st
    inv.coherent.wf (idsOf_lt inv.scoped.2 args)
  have apartSkel₁ := Skel.Ordered.apart ordered below apartSkel g₁
  cases hs : σ.rules.shared o with
  | true =>
      simp only [walk, hs] at differs hnone recorded ⊢
      generalize hst₁ : checkRequirements σ.rules.ops k ⟨σ.definition, blocks, some key, σ.role⟩
        (σ.rules.written o) (idsOf ids args) (σ.rules.ops.requires (σ.rules.written o)) s.st = st₁
        at b₁ g₁ apartSkel₁ differs hnone recorded ⊢
      obtain ⟨r₂, b₂⟩ := valueStep_state σ.rules (σ.rules.written o) res (idsOf ids args) k st₁
      have refs₁ : st₁.refusals = [] := by
        rw [← r₂]
        exact refusals_before (walk_adds σ.rules σ.checks σ.definition σ.role blocks rest
          (some skel) _ _ { s with st := (valueStep σ.rules (σ.rules.written o) res
            (idsOf ids args) k st₁).2.2 }).1 hnone
      obtain ⟨ρ₁, le₁, inv₁, required, fills₁⟩ := requirements_sound laws
        ⟨σ.definition, blocks, some key, σ.role⟩ o args inv (by rw [hst₁]; exact refs₁)
      rw [hst₁] at inv₁ fills₁
      obtain ⟨values, ρ₂, ran, le, inv', fills₂⟩ := value_sound laws key o hs args results path ρ₁
        ids env k st₁ inv₁ required
      obtain ⟨-, grows₂, -, -⟩ := valueStep_grows σ.rules (σ.rules.written o) res
        (idsOf ids args) k st₁ inv₁.coherent.wf (idsOf_lt inv₁.scoped.2 args)
      have shows := ih skel path ρ₂ _ _ _ _ lo hi inv'
        ⟨ordered, Nat.le_trans below (g₁.trans grows₂).next,
          Skel.Ordered.apart ordered (Nat.le_trans below g₁.next) apartSkel₁ grows₂,
          (quiet.fills fills₁ g₁.sub).fills fills₂ grows₂.sub⟩ differs hnone nodup'
        (fun q m bl key' eq inR => apart q (by rw [← b₁, ← b₂]; exact m) bl key' eq
          (List.mem_cons_of_mem _ inR)) (recorded' _ recorded)
      simp only [Shows, Term.EveryLoop, Term.denote, ran, Process.bind, Process.Every]
      exact ⟨shows.1, Process.every_mono _ _ (fun vs h => by
        obtain ⟨ρ', le', ex, f⟩ := h
        exact ⟨ρ', le₁.trans (le.trans le'), ex, f⟩) (fun _ h => h) shows.2⟩
  | false =>
      simp only [walk, hs, Option.isSome_some, Exit.region_skel] at differs hnone recorded ⊢
      generalize hst₁ : checkRequirements σ.rules.ops k ⟨σ.definition, blocks, some key, σ.role⟩
        (σ.rules.written o) (idsOf ids args) (σ.rules.ops.requires (σ.rules.written o)) s.st = st₁
        at b₁ g₁ apartSkel₁ differs hnone recorded ⊢
      generalize hhit : effectEntry σ.checks key o (idsOf ids args) (some skel) = hit
        at differs hnone recorded ⊢
      have found := found_of_differs (adds_after_leaves (walk_adds σ.rules σ.checks σ.definition
        σ.role blocks rest _ _ _ _).2.2) differs
      obtain ⟨⟨r, rest'⟩, rfl⟩ : ∃ h, hit = some h := by
        cases hit with
        | none => cases found
        | some h => exact ⟨h, rfl⟩
      obtain ⟨_, _, e⟩ := effectEntry_hit σ.checks hhit
      obtain rfl := Option.some.inj e
      simp only [Option.isSome_some, miss_found, Option.map_some, leaves]
        at differs hnone recorded ⊢
      have refs₁ : st₁.refusals = [] :=
        refusals_before (walk_adds σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
          _ _ { s with st := st₁ }).1 hnone
      obtain ⟨ρ₁, le₁, inv₁, required, fills₁⟩ := requirements_sound laws
        ⟨σ.definition, blocks, some key, σ.role⟩ o args inv (by rw [hst₁]; exact refs₁)
      rw [hst₁] at inv₁ fills₁
      have quiet₁ := quiet.fills fills₁ g₁.sub
      have apart₁ : BoundsApart σ st₁ (Term.addresses blocks (.op key o args results rest)) :=
        fun q m => apart q (by rw [← b₁]; exact m)
      obtain ⟨low, orderedRest⟩ := ordered
      obtain ⟨apartHere, apartRest⟩ := apartSkel₁
      have inside : r + res.length ≤ st₁.next :=
        Nat.le_trans (Skel.Ordered.le (skel := rest') orderedRest) (Nat.le_trans below g₁.next)
      have va : σ.AllValid (env.all args) :=
        env_all_valid (agree_valid inv.agree inv.coherent.valid) args
      have restShows : ∀ values : HList σ.sem.Val res, σ.AllValid values →
          Shows σ blocks rest path (env.extend results values) (fun vs => ∃ ρ', ρ.Le ρ' ∧
            ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
              (bindIds ids results (List.range' r res.length))
              ((k.addRanges (List.range' r res.length) (res.map σ.rules.range)).enter
                σ.rules res) { s with st := st₁ }).region
              (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
                (bindIds ids results (List.range' r res.length))
                ((k.addRanges (List.range' r res.length) (res.map σ.rules.range)).enter
                  σ.rules res) { s with st := st₁ }).state.st vs ∧
            Followed (some rest') hi ρ'
              (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
                (bindIds ids results (List.range' r res.length))
                ((k.addRanges (List.range' r res.length) (res.map σ.rules.range)).enter
                  σ.rules res) { s with st := st₁ }).state.st) := by
        intro values valid
        obtain ⟨coh, le, look, quiet'⟩ := leaves_at inv₁.coherent (σ.sem.dyns values) valid
          (by rw [σ.sem.dyns_length]; exact inside) (by rw [σ.sem.dyns_length]; exact apartHere)
          quiet₁ low
        rw [σ.sem.dyns_length] at look quiet'
        have inv' : Inv σ (ρ₁.setFrom r (σ.sem.dyns values))
            (bindIds ids results (List.range' r res.length)) (env.extend results values)
            ((k.addRanges (List.range' r res.length) (res.map σ.rules.range)).enter
              σ.rules res) st₁ := by
          refine ⟨coh, agree_extend results values _ (inv₁.agree.le le) look, ?_⟩
          rw [enter_of_valid laws valid]
          exact addTypeRanges_holds laws (inv₁.holds.le le) coh.valid (valuesOf_typed look)
        have shows := ih rest' path _ _ _ _ { s with st := st₁ } (r + res.length) hi inv'
          ⟨orderedRest, Nat.le_trans below g₁.next, apartRest, quiet'⟩ differs hnone nodup'
          (BoundsApart.sub apart₁ fun _ m => List.mem_cons_of_mem _ m) (recorded' _ recorded)
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
/-- A guard, while a skeleton is followed: it finds its entry, and is as when none is followed. -/
theorem guard_follow (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs : List D.Ty} {t : D.Ty}
    (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t) (why : Reason)
    (rest : Term D Γ outs) (ih : ∀ skel, Sound σ blocks rest (some skel)) (skel : Skel D outs) :
    Sound σ blocks (.guard key w c ok why rest) (some skel) := by
  intro path ρ ids env k s lo hi inv following differs hnone nodup apart recorded
  have lawful : OpFacts.Lawful σ.rules.ops σ.R σ.Runs := laws.ops
  simp only [walk, Option.isSome_some, Exit.region_skel] at differs hnone recorded ⊢
  generalize hhit : guardEntry σ.checks (t := t) key w (idOf ids c.name) why (some skel) = hit
    at differs hnone recorded ⊢
  have found := found_of_differs (walk_adds σ.rules σ.checks σ.definition σ.role blocks rest
    _ _ _ _).2.2 differs
  obtain ⟨rest', rfl⟩ : ∃ h, hit = some h := by
    cases hit with
    | none => cases found
    | some h => exact ⟨h, rfl⟩
  obtain ⟨_, e⟩ := guardEntry_hit σ.checks hhit
  obtain rfl := Option.some.inj e
  simp only [Option.isSome_some, miss_found] at differs hnone recorded ⊢
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
      have shows := ih rest' path ρ ids env _ s lo hi ⟨inv.coherent, inv.agree, k'⟩ following
        differs hnone (List.nodup_cons.mp nodup).2
        (BoundsApart.sub apart fun x m => List.mem_cons_of_mem _ m)
        (Recorded.sub recorded fun x m => List.mem_cons_of_mem _ m)
      simp only [Bool.cond_true, forall_const]
      exact ⟨shows.1, shows.2⟩

include laws in
/-- A block, while a skeleton is followed: it finds its entry; its body follows the entry's body,
and the values that it returns are at the entry's leaves. -/
theorem block_follow (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs mid : List D.Ty}
    (key : Key) (number : Nat) (body : Term D Γ mid) (results : Names mid)
    (rest : Term D (Γ.extend results) outs)
    (ihb : ∀ skel, Sound σ (blocks ++ [(key, number)]) body (some skel))
    (ihr : ∀ skel, Sound σ blocks rest (some skel)) (skel : Skel D outs) :
    Sound σ blocks (.block key number body results rest) (some skel) := by
  intro path ρ ids env k s lo hi inv following differs hnone nodup apart recorded
  simp only [walk, Option.isSome_some, Exit.region_skel] at differs hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  generalize hhit : blockEntry σ.checks (mid := mid) key number (some skel) = hit
    at differs hnone recorded ⊢
  have found := found_of_differs (AddsPlaces.trans (walk_adds σ.rules σ.checks σ.definition
    σ.role (blocks ++ [(key, number)]) body _ _ _ _).2.2 (adds_after_leaves (walk_adds σ.rules
    σ.checks σ.definition σ.role blocks rest _ _ _ _).2.2)) differs
  obtain ⟨⟨body', r, rest'⟩, rfl⟩ : ∃ h, hit = some h := by
    cases hit with
    | none => cases found
    | some h => exact ⟨h, rfl⟩
  obtain rfl := Option.some.inj (blockEntry_hit σ.checks hhit)
  simp only [Option.isSome_some, miss_found, Option.map_some, leaves]
    at differs hnone recorded ⊢
  obtain ⟨⟨orderedB, orderedR⟩, below, ⟨apartB, apartHere, apartRest⟩, quiet⟩ := following
  have highR := Skel.Ordered.le (skel := rest') orderedR
  obtain ⟨⟨rb, eb⟩, ⟨nb, ebb, atb⟩, db⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    (blocks ++ [(key, number)]) body (some body') ids k s
  have gb := walk_grows σ.rules σ.checks σ.definition σ.role (blocks ++ [(key, number)]) body
    (some body') ids k s inv.scoped ((Skel.Ordered.below orderedB).mono (by omega))
  generalize he : walk σ.rules σ.checks σ.definition σ.role (blocks ++ [(key, number)]) body
    (some body') ids k s = e at differs hnone recorded eb ebb db gb ⊢
  obtain ⟨⟨nr, er⟩, ⟨nbr, ebr, atr⟩, dr⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks rest (some rest') (bindIds ids results (List.range' r mid.length))
    ((afterRegions σ.rules [e.region] k (List.range' r mid.length) mid 0).enter
      σ.rules mid) e.state
  obtain ⟨differsB, differsR⟩ := differs_both db dr differs
  have refs : e.state.st.refusals = [] := refusals_before ⟨nr, er⟩ hnone
  have nodupB := (List.nodup_append.mp nodup).1
  have nodupR := (List.nodup_append.mp nodup).2.1
  have recB : Recorded σ (body.addresses (blocks ++ [(key, number)])) e.state.st :=
    (Recorded.sub recorded fun x m => List.mem_append_left _ m).strip ebr atr
      (fun x m mr => nodup_apart nodup m mr)
  have showsB := ihb body' (path ++ [.iteration key number]) ρ ids env k s lo r inv
    ⟨orderedB, by omega, apartB, quiet⟩
    (by rw [he]; exact differsB) (by rw [he]; exact refs) nodupB
    (BoundsApart.sub apart fun x m => List.mem_append_left _ m) (by rw [he]; exact recB)
  rw [he] at showsB
  have afterRest : ∀ mids : HList σ.sem.Val mid, (∃ ρ₁, ρ.Le ρ₁ ∧
      ExitInv σ ρ₁ e.region e.state.st mids ∧ Followed (some body') r ρ₁ e.state.st) →
      Shows σ blocks rest path (env.extend results mids) (fun vs => ∃ ρ', ρ.Le ρ' ∧
        ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
          (bindIds ids results (List.range' r mid.length))
          ((afterRegions σ.rules [e.region] k (List.range' r mid.length) mid 0).enter
            σ.rules mid) e.state).region
          (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
            (bindIds ids results (List.range' r mid.length))
            ((afterRegions σ.rules [e.region] k (List.range' r mid.length) mid 0).enter
              σ.rules mid) e.state).state.st vs ∧
        Followed (some rest') hi ρ'
          (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
            (bindIds ids results (List.range' r mid.length))
            ((afterRegions σ.rules [e.region] k (List.range' r mid.length) mid 0).enter
              σ.rules mid) e.state).state.st) := by
    intro mids h
    obtain ⟨ρ₁, le, ex, quiet₁⟩ := h
    have valid : σ.AllValid mids := allValid_of_valuesOf ex.rets ex.coherent.valid
    obtain ⟨coh, le₂, look, quiet₂⟩ := leaves_at ex.coherent (σ.sem.dyns mids) valid
      (by rw [σ.sem.dyns_length]; exact Nat.le_trans (Nat.le_trans highR below) gb.2.next)
      (by rw [σ.sem.dyns_length]; exact apartHere.grows (by omega) gb.2) quiet₁ (Nat.le_refl r)
    rw [σ.sem.dyns_length] at look quiet₂
    have inv' := afterRegions_inv laws (List.mem_singleton_self e.region) inv le ex results coh
      le₂ look
    have shows := ihr rest' path _ _ _ _ e.state (r + mid.length) hi inv'
      ⟨orderedR, Nat.le_trans below gb.2.next, Skel.Ordered.apart orderedR below apartRest gb.2,
        quiet₂⟩ differsR hnone nodupR
      (BoundsApart.extend (BoundsApart.sub apart fun x m => List.mem_append_right _ m)
        ebb atb (fun x m mr => nodup_apart nodup m mr))
      (Recorded.sub recorded fun x m => List.mem_append_right _ m)
    exact ⟨shows.1, Process.every_mono _ _ (fun vs h' => by
      obtain ⟨ρ'', le'', ex', f⟩ := h'
      exact ⟨ρ'', le.trans (le₂.trans le''), ex', f⟩) (fun _ h => h) shows.2⟩
  simp only [Shows, Term.EveryLoop, Term.denote]
  refine ⟨⟨showsB.1, Process.every_mono _ _ (fun mids h => (afterRest mids h).1)
    (fun _ _ => trivial) showsB.2⟩, ?_⟩
  rw [Process.every_bind]
  exact Process.every_mono _ _ (fun mids h => (afterRest mids h).2) (fun _ h => h) showsB.2

include laws in
/-- An attempt, while a skeleton is followed: it finds its entry; its number is at the entry's
leaf, its body follows the entry's body, and the values that it returns are at the entry's
leaves. -/
theorem attempt_follow (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs mid : List D.Ty}
    (key : Key) (w : D.Who) (owns : D.Attempt w) (inputs : Names [D.index w])
    (body : Term D (Γ.extend inputs) mid) (results : Names mid)
    (rest : Term D (Γ.extend results) outs)
    (ihb : ∀ skel, Sound σ blocks body (some skel)) (ihr : ∀ skel, Sound σ blocks rest (some skel))
    (skel : Skel D outs) : Sound σ blocks (.attempt key w owns inputs body results rest) (some skel) := by
  intro path ρ ids env k s lo hi inv following differs hnone nodup apart recorded
  simp only [walk, Option.isSome_some, Exit.region_skel] at differs hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  generalize hhit : attemptEntry σ.checks (mid := mid) key w (some skel) = hit
    at differs hnone recorded ⊢
  have found := found_of_differs (adds_after_leaves (AddsPlaces.trans (walk_adds σ.rules σ.checks
    σ.definition σ.role blocks body _ _ _ _).2.2 (adds_after_leaves (walk_adds σ.rules σ.checks
    σ.definition σ.role blocks rest _ _ _ _).2.2))) differs
  obtain ⟨⟨input, body', r, rest'⟩, rfl⟩ : ∃ h, hit = some h := by
    cases hit with
    | none => cases found
    | some h => exact ⟨h, rfl⟩
  obtain rfl := Option.some.inj (attemptEntry_hit σ.checks hhit)
  simp only [Option.isSome_some, miss_found, Option.map_some, leaves]
    at differs hnone recorded ⊢
  obtain ⟨⟨lowInput, orderedB, orderedR⟩, below, ⟨apartInput, apartB, apartHere, apartRest⟩,
    quiet⟩ := following
  have highB := Skel.Ordered.le (skel := body') orderedB
  have highR := Skel.Ordered.le (skel := rest') orderedR
  have notHere := (List.nodup_cons.mp nodup).1
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupB := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  obtain ⟨⟨rb, eb⟩, ⟨nb, ebb, atb⟩, db⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks body (some body') (bindIds ids inputs (List.range' input 1))
    ((k.addRanges (List.range' input 1) [σ.rules.range (D.index w)]).enter σ.rules
      [D.index w]) s
  have gb := walk_grows σ.rules σ.checks σ.definition σ.role blocks body (some body')
    (bindIds ids inputs (List.range' input 1))
    ((k.addRanges (List.range' input 1) [σ.rules.range (D.index w)]).enter σ.rules
      [D.index w]) s
    ⟨inv.coherent.wf, inv.scoped.2.bind inputs _ (by simp) fun i m => by
      have := mem_range'_bounds m
      omega⟩ ((Skel.Ordered.below orderedB).mono (by omega))
  generalize he : walk σ.rules σ.checks σ.definition σ.role blocks body (some body')
    (bindIds ids inputs (List.range' input 1))
    ((k.addRanges (List.range' input 1) [σ.rules.range (D.index w)]).enter σ.rules
      [D.index w]) s = e at differs hnone recorded eb ebb db gb ⊢
  obtain ⟨⟨nr, er⟩, ⟨nbr, ebr, atr⟩, dr⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks rest (some rest') (bindIds ids results (List.range' r mid.length))
    ((afterRegions σ.rules [e.region] k (List.range' r mid.length) mid 0).enter
      σ.rules mid) e.state
  obtain ⟨differsB, differsR⟩ := differs_both db dr differs
  have refs : e.state.st.refusals = [] := refusals_before ⟨nr, er⟩ hnone
  have recB : Recorded σ (body.addresses blocks) e.state.st :=
    (Recorded.sub recorded fun x m => List.mem_cons_of_mem _ (List.mem_append_left _ m)).strip
      ebr atr (fun x m mr => nodup_apart nodup₁ m mr)
  have apartR : BoundsApart σ e.state.st (rest.addresses blocks) :=
    BoundsApart.extend (BoundsApart.sub apart fun x m =>
        List.mem_cons_of_mem _ (List.mem_append_right _ m))
      ebb atb (fun x m mr => nodup_apart nodup₁ m mr)
  have bodyShows : ∀ n : σ.sem.Val (D.index w), σ.Valid ⟨D.index w, n⟩ →
      Shows σ blocks body path (env.extend inputs (.cons n .nil)) (fun mids => ∃ ρ', ρ.Le ρ' ∧
        ExitInv σ ρ' e.region e.state.st mids ∧ Followed (some body') r ρ' e.state.st) := by
    intro n valid
    have validN : σ.AllValid (HList.cons n HList.nil : HList σ.sem.Val [D.index w]) :=
      allValid_cons.mpr ⟨valid, fun _ m => nomatch m⟩
    obtain ⟨coh, le, look, quiet'⟩ := leaves_at inv.coherent [⟨D.index w, n⟩]
      (fun d m => by simp only [List.mem_singleton] at m; subst m; exact valid)
      (by simp only [List.length_singleton]; omega) apartInput quiet lowInput
    simp only [List.length_singleton] at look quiet'
    have inv' : Inv σ (ρ.setFrom input [⟨D.index w, n⟩]) (bindIds ids inputs (List.range' input 1))
        (env.extend inputs (.cons n .nil))
        ((k.addRanges (List.range' input 1) [σ.rules.range (D.index w)]).enter σ.rules
          [D.index w]) s.st := by
      refine ⟨coh, agree_extend inputs (HList.cons n HList.nil) _ (inv.agree.le le) look, ?_⟩
      rw [enter_of_valid laws validN]
      exact addTypeRanges_holds laws (τs := [D.index w]) (inv.holds.le le) coh.valid
        (valuesOf_typed (vs := HList.cons n HList.nil) look)
    have shows := ihb body' path _ _ _ _ s (input + 1) r inv'
      ⟨orderedB, by omega, apartB, quiet'⟩ (by rw [he]; exact differsB) (by rw [he]; exact refs)
      nodupB (BoundsApart.sub apart fun x m => List.mem_cons_of_mem _ (List.mem_append_left _ m))
      (by rw [he]; exact recB)
    rw [he] at shows
    exact ⟨shows.1, Process.every_mono _ _ (fun vs h' => by
      obtain ⟨ρ'', le'', ex', f⟩ := h'
      exact ⟨ρ'', le.trans le'', ex', f⟩) (fun _ h => h) shows.2⟩
  have afterRest : ∀ mids : HList σ.sem.Val mid, (∃ ρ₁, ρ.Le ρ₁ ∧
      ExitInv σ ρ₁ e.region e.state.st mids ∧ Followed (some body') r ρ₁ e.state.st) →
      Shows σ blocks rest path (env.extend results mids) (fun vs => ∃ ρ', ρ.Le ρ' ∧
        ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
          (bindIds ids results (List.range' r mid.length))
          ((afterRegions σ.rules [e.region] k (List.range' r mid.length) mid 0).enter
            σ.rules mid) e.state).region
          (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
            (bindIds ids results (List.range' r mid.length))
            ((afterRegions σ.rules [e.region] k (List.range' r mid.length) mid 0).enter
              σ.rules mid) e.state).state.st vs ∧
        Followed (some rest') hi ρ'
          (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
            (bindIds ids results (List.range' r mid.length))
            ((afterRegions σ.rules [e.region] k (List.range' r mid.length) mid 0).enter
              σ.rules mid) e.state).state.st) := by
    intro mids h
    obtain ⟨ρ₁, le, ex, quiet₁⟩ := h
    have valid : σ.AllValid mids := allValid_of_valuesOf ex.rets ex.coherent.valid
    obtain ⟨coh, le₂, look, quiet₂⟩ := leaves_at ex.coherent (σ.sem.dyns mids) valid
      (by rw [σ.sem.dyns_length]; exact Nat.le_trans (Nat.le_trans highR below) gb.2.next)
      (by rw [σ.sem.dyns_length]; exact apartHere.grows (by omega) gb.2) quiet₁ (Nat.le_refl r)
    rw [σ.sem.dyns_length] at look quiet₂
    have inv' := afterRegions_inv laws (List.mem_singleton_self e.region) inv le ex results coh
      le₂ look
    have shows := ihr rest' path _ _ _ _ e.state (r + mid.length) hi inv'
      ⟨orderedR, Nat.le_trans below gb.2.next, Skel.Ordered.apart orderedR below apartRest gb.2,
        quiet₂⟩ differsR hnone nodupR apartR
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
/-- A choice, while a skeleton is followed: it finds its entry; its regions follow the entry's
regions, and the values that the region that ran returns are at the entry's leaves. -/
theorem choose_follow (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs mid : List D.Ty} {t : D.Ty}
    (key : Key) (w : D.Who) (c : Var Γ t) (ok : D.Condition w t)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (onTrue onFalse : Term D Γ mid) (results : Names mid)
    (rest : Term D (Γ.extend results) outs)
    (iht : ∀ skel, Sound σ blocks onTrue (some skel))
    (ihf : ∀ skel, Sound σ blocks onFalse (some skel))
    (ihr : ∀ skel, Sound σ blocks rest (some skel)) (skel : Skel D outs) :
    Sound σ blocks (.choose key w c ok gives onTrue onFalse results rest) (some skel) := by
  intro path ρ ids env k s lo hi inv following differs hnone nodup apart recorded
  have lawful : OpFacts.Lawful σ.rules.ops σ.R σ.Runs := laws.ops
  simp only [walk, Option.isSome_some, Exit.region_skel] at differs hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  have hc := inv.agree.idOf c
  have read := laws.condition ok (env.get c) (inv.coherent.valid _ _ hc)
  generalize idOf ids c.name = cid at hc differs hnone recorded ⊢
  generalize hhit : chooseEntry σ.checks (mid := mid) (t := t) key w cid (some skel) = hit
    at differs hnone recorded ⊢
  have found := found_of_differs (AddsPlaces.trans (walk_adds σ.rules σ.checks σ.definition
    σ.role blocks onTrue _ _ _ _).2.2 (AddsPlaces.trans (walk_adds σ.rules σ.checks σ.definition
    σ.role blocks onFalse _ _ _ _).2.2 (adds_after_leaves (walk_adds σ.rules σ.checks
    σ.definition σ.role blocks rest _ _ _ _).2.2))) differs
  obtain ⟨⟨onTrue', onFalse', r, rest'⟩, rfl⟩ : ∃ h, hit = some h := by
    cases hit with
    | none => cases found
    | some h => exact ⟨h, rfl⟩
  obtain ⟨_, e⟩ := chooseEntry_hit σ.checks hhit
  obtain rfl := Option.some.inj e
  simp only [Option.isSome_some, miss_found, Option.map_some, leaves]
    at differs hnone recorded ⊢
  obtain ⟨⟨orderedT, orderedF, orderedR⟩, below, ⟨apartT, apartF, apartHere, apartRest⟩, quiet⟩ :=
    following
  have highR := Skel.Ordered.le (skel := rest') orderedR
  have rBelow : r ≤ s.st.next := by omega
  obtain ⟨⟨ra, ea⟩, ⟨na, eba, ata⟩, da⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks onTrue (some onTrue') ids (assume σ.rules.ops s.st.table s.st.next k cid true) s
  have ga := walk_grows σ.rules σ.checks σ.definition σ.role blocks onTrue (some onTrue') ids
    (assume σ.rules.ops s.st.table s.st.next k cid true) s inv.scoped
    ((Skel.Ordered.below orderedT).mono rBelow)
  generalize hfirst : walk σ.rules σ.checks σ.definition σ.role blocks onTrue (some onTrue') ids
    (assume σ.rules.ops s.st.table s.st.next k cid true) s = first
    at differs hnone recorded ea eba da ga ⊢
  have fitsB : Scoped Γ ids first.state.st := ⟨ga.1.1, inv.scoped.2.mono ga.2.next⟩
  obtain ⟨⟨rb, eb⟩, ⟨nb, ebb, atb⟩, db⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks onFalse (some onFalse') ids
    (assume σ.rules.ops first.state.st.table first.state.st.next k cid false) first.state
  have gb := walk_grows σ.rules σ.checks σ.definition σ.role blocks onFalse (some onFalse') ids
    (assume σ.rules.ops first.state.st.table first.state.st.next k cid false) first.state
    fitsB ((Skel.Ordered.below orderedF).mono (Nat.le_trans rBelow ga.2.next))
  generalize hsecond : walk σ.rules σ.checks σ.definition σ.role blocks onFalse (some onFalse') ids
    (assume σ.rules.ops first.state.st.table first.state.st.next k cid false) first.state = second
    at differs hnone recorded eb ebb db gb ⊢
  have growsAB : St.Grows s.st second.state.st := ga.2.trans gb.2
  obtain ⟨⟨nr, er⟩, ⟨nbr, ebr, atr⟩, dr⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks rest (some rest') (bindIds ids results (List.range' r mid.length))
    ((afterChoice σ.rules k cid first.region second.region
      (List.range' r mid.length) mid).enter σ.rules mid) second.state
  obtain ⟨differsA, differsB, differsR⟩ := differs_three da db dr differs
  have refsB : second.state.st.refusals = [] := refusals_before ⟨nr, er⟩ hnone
  have refsA : first.state.st.refusals = [] := refusals_before ⟨rb, eb⟩ refsB
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupAB := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  have nodupA := (List.nodup_append.mp nodupAB).1
  have nodupB := (List.nodup_append.mp nodupAB).2.1
  have apartR : BoundsApart σ second.state.st (rest.addresses blocks) :=
    ((BoundsApart.sub apart fun x m => by simp [m]).extend eba ata (fun x m mr =>
      nodup_apart nodup₁ (List.mem_append_left _ m) mr)).extend ebb atb
      (fun x m mr => nodup_apart nodup₁ (List.mem_append_right _ m) mr)
  -- the rest, after either region
  have afterRest : ∀ (b0 : Bool) (ran : FactCheck.Exit D.Ty Raw),
      ran ∈ [first.region, second.region] →
      ran = (if b0 then first.region else second.region) → σ.sem.holds ok (env.get c) = b0 →
      ∀ (ρ₁ : Valuation σ.sem.Dyn) (mids : HList σ.sem.Val mid), ρ.Le ρ₁ →
        ExitInv σ ρ₁ ran second.state.st mids → Quiet r ρ₁ second.state.st.table →
        Shows σ blocks rest path (env.extend results mids) (fun vs => ∃ ρ', ρ.Le ρ' ∧
          ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
            (bindIds ids results (List.range' r mid.length))
            ((afterChoice σ.rules k cid first.region second.region
              (List.range' r mid.length) mid).enter σ.rules mid) second.state).region
            (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
              (bindIds ids results (List.range' r mid.length))
              ((afterChoice σ.rules k cid first.region second.region
                (List.range' r mid.length) mid).enter σ.rules mid) second.state).state.st vs ∧
          Followed (some rest') hi ρ'
            (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
              (bindIds ids results (List.range' r mid.length))
              ((afterChoice σ.rules k cid first.region second.region
                (List.range' r mid.length) mid).enter σ.rules mid) second.state).state.st) := by
    intro b0 ran mem eran hb0 ρ₁ mids le ex quiet₁
    have valid : σ.AllValid mids := allValid_of_valuesOf ex.rets ex.coherent.valid
    obtain ⟨coh, le₂, look, quiet₂⟩ := leaves_at ex.coherent (σ.sem.dyns mids) valid
      (by rw [σ.sem.dyns_length]; exact Nat.le_trans (Nat.le_trans highR below) growsAB.next)
      (by rw [σ.sem.dyns_length]; exact apartHere.grows (by omega) growsAB) quiet₁
      (Nat.le_refl r)
    rw [σ.sem.dyns_length] at look quiet₂
    have inv' := afterRegions_inv laws mem inv le ex results coh le₂ look
    have choices := choiceFacts_holds (first := first.region) (second := second.region) lawful
      inv'.coherent.consistent inv'.coherent.closed (b0 := b0)
      ⟨_, (le.trans le₂) _ _ hc, by rw [read, hb0]⟩ (List.range' r mid.length) 0 (by
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
    have inv'' : Inv σ (ρ₁.setFrom r (σ.sem.dyns mids))
        (bindIds ids results (List.range' r mid.length)) (env.extend results mids)
        ((afterChoice σ.rules k cid first.region second.region
          (List.range' r mid.length) mid).enter σ.rules mid) second.state.st := by
      refine ⟨inv'.coherent, inv'.agree, ?_⟩
      have holds := inv'.holds
      rw [enter_of_valid laws valid] at holds ⊢
      exact Known.Holds.addChoices holds choices
    have shows := ihr rest' path _ _ _ _ second.state (r + mid.length) hi inv''
      ⟨orderedR, Nat.le_trans below growsAB.next,
        Skel.Ordered.apart orderedR below apartRest growsAB, quiet₂⟩ differsR hnone nodupR apartR
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
      have showsT := iht onTrue' path ρ ids env _ s lo r ⟨inv.coherent, inv.agree, kt⟩
        ⟨orderedT, rBelow, apartT, quiet⟩
        (by rw [hfirst]; exact differsA) (by rw [hfirst]; exact refsA) nodupA
        (BoundsApart.sub apart fun x m => by simp [m]) (by rw [hfirst]; exact recA)
      rw [hfirst] at showsT
      simp only [Bool.cond_true]
      refine ⟨⟨showsT.1, ?_⟩, ?_⟩
      · refine Process.every_mono _ _ ?_ (fun _ _ => trivial) showsT.2
        intro mids h
        obtain ⟨ρ₁, le, ex, quiet₁⟩ := h
        exact (afterRest true first.region (by simp) rfl hv ρ₁ mids le
          (exit_grow ex gb.2 gb.1.1) (Quiet.grow quiet₁ gb.2.sub)).1
      · rw [Process.every_bind]
        refine Process.every_mono _ _ ?_ (fun _ h => h) showsT.2
        intro mids h
        obtain ⟨ρ₁, le, ex, quiet₁⟩ := h
        exact (afterRest true first.region (by simp) rfl hv ρ₁ mids le
          (exit_grow ex gb.2 gb.1.1) (Quiet.grow quiet₁ gb.2.sub)).2
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
      have showsF := ihf onFalse' path ρ ids env _ first.state lo r ⟨coh₁, inv.agree, kf⟩
        ⟨orderedF, Nat.le_trans rBelow ga.2.next,
          Skel.Ordered.apart orderedF rBelow apartF ga.2, quiet.grow ga.2.sub⟩
        (by rw [hsecond]; exact differsB) (by rw [hsecond]; exact refsB) nodupB apartB
        (by rw [hsecond]; exact recB)
      rw [hsecond] at showsF
      simp only [Bool.cond_false]
      refine ⟨⟨showsF.1, ?_⟩, ?_⟩
      · refine Process.every_mono _ _ ?_ (fun _ _ => trivial) showsF.2
        intro mids h
        obtain ⟨ρ₁, le, ex, quiet₁⟩ := h
        exact (afterRest false second.region (by simp) rfl hv ρ₁ mids le ex quiet₁).1
      · rw [Process.every_bind]
        refine Process.every_mono _ _ ?_ (fun _ h => h) showsF.2
        intro mids h
        obtain ⟨ρ₁, le, ex, quiet₁⟩ := h
        exact (afterRest false second.region (by simp) rfl hv ρ₁ mids le ex quiet₁).2

theorem armsNil_follow (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {mid : List D.Ty}
    (arms : SkelArms D mid []) : ArmsSound σ blocks (.nil : Arms D Γ mid []) (some arms) :=
  fun _ _ _ _ _ _ _ _ p => nomatch p

include laws in
/-- The arms of a case analysis, while their skeletons are followed: the arm of the alternative
runs, with its payload at the leaf of its arm of the skeleton. -/
theorem armsCons_follow (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
    {payload : D.Ty} (inputs : Names [payload]) (arm : Term D (Γ.extend inputs) mid)
    (rest : Arms D Γ mid payloads) (iha : ∀ skel, Sound σ blocks arm (some skel))
    (ihr : ∀ arms, ArmsSound σ blocks rest (some arms))
    (arms : SkelArms D mid (payload :: payloads)) :
    ArmsSound σ blocks (.cons inputs arm rest) (some arms) := by
  intro path ρ ids env k s lo hi p valid inv following differs hnone nodup apart recorded
  cases arms with
  | cons input arm' rest'' =>
  simp only [walkArms, armEntry, Option.map_some, leaves, Option.getD_some]
    at differs hnone recorded ⊢
  simp only [Arms.addresses] at nodup apart recorded
  obtain ⟨⟨lowInput, orderedA, orderedR⟩, below, ⟨apartInput, apartA, apartR⟩, quiet⟩ := following
  have highA := Skel.Ordered.le (skel := arm') orderedA
  obtain ⟨⟨ra, ea⟩, ⟨na, eba, ata⟩, da⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks arm (some arm') (bindIds ids inputs (List.range' input 1))
    ((k.addRanges (List.range' input 1) [σ.rules.range payload]).enter σ.rules [payload]) s
  have ga := walk_grows σ.rules σ.checks σ.definition σ.role blocks arm (some arm')
    (bindIds ids inputs (List.range' input 1))
    ((k.addRanges (List.range' input 1) [σ.rules.range payload]).enter σ.rules [payload]) s
    ⟨inv.coherent.wf, inv.scoped.2.bind inputs _ (by simp) fun i m => by
      have := mem_range'_bounds m
      omega⟩ ((Skel.Ordered.below orderedA).mono below)
  generalize he : walk σ.rules σ.checks σ.definition σ.role blocks arm (some arm')
    (bindIds ids inputs (List.range' input 1))
    ((k.addRanges (List.range' input 1) [σ.rules.range payload]).enter σ.rules [payload]) s
    = e at differs hnone recorded ea eba da ga ⊢
  obtain ⟨⟨rr, er⟩, ⟨nr, ebr, atr⟩, dr⟩ := walkArms_adds σ.rules σ.checks σ.definition σ.role
    blocks rest (some rest'') ids k e.state
  have gr := walkArms_grows σ.rules σ.checks σ.definition σ.role blocks rest (some rest'') ids k
    e.state ⟨ga.1.1, inv.scoped.2.mono ga.2.next⟩
    ((SkelArms.Ordered.below orderedR).mono (Nat.le_trans below ga.2.next))
  obtain ⟨differsA, differsR⟩ := differs_both da dr differs
  have refsE : e.state.st.refusals = [] := refusals_before ⟨rr, er⟩ hnone
  have nodupA := (List.nodup_append.mp nodup).1
  have nodupR := (List.nodup_append.mp nodup).2.1
  cases p with
  | here v =>
      have validV : σ.AllValid (HList.cons v HList.nil : HList σ.sem.Val [payload]) :=
        allValid_cons.mpr ⟨valid, fun _ m => nomatch m⟩
      obtain ⟨coh, le, look, quiet'⟩ := leaves_at inv.coherent [⟨payload, v⟩]
        (fun d m => by simp only [List.mem_singleton] at m; subst m; exact valid)
        (by simp only [List.length_singleton]; omega) apartInput quiet lowInput
      simp only [List.length_singleton] at look quiet'
      have inv' : Inv σ (ρ.setFrom input [⟨payload, v⟩]) (bindIds ids inputs (List.range' input 1))
          (env.extend inputs (.cons v .nil))
          ((k.addRanges (List.range' input 1) [σ.rules.range payload]).enter σ.rules
            [payload]) s.st := by
        refine ⟨coh, agree_extend inputs (HList.cons v HList.nil) _ (inv.agree.le le) look, ?_⟩
        rw [enter_of_valid laws validV]
        exact addTypeRanges_holds laws (τs := [payload]) (inv.holds.le le) coh.valid
          (valuesOf_typed (vs := HList.cons v HList.nil) look)
      have recA : Recorded σ (arm.addresses blocks) e.state.st :=
        (Recorded.sub recorded fun x m => List.mem_append_left _ m).strip ebr atr
          (fun x m mr => nodup_apart nodup m mr)
      have shows := iha arm' path _ _ _ _ s (input + 1) hi inv' ⟨orderedA, below, apartA, quiet'⟩
        (by rw [he]; exact differsA) (by rw [he]; exact refsE) nodupA
        (BoundsApart.sub apart fun x m => List.mem_append_left _ m) (by rw [he]; exact recA)
      rw [he] at shows
      refine ⟨shows.1, Process.every_mono _ _ ?_ (fun _ h => h) shows.2⟩
      intro mids h
      obtain ⟨ρ₁, le₁, ex, quiet₁⟩ := h
      exact ⟨ρ₁, le.trans le₁, e.region, List.mem_cons_self, exit_grow ex gr.2.2 gr.2.1.1,
        Quiet.grow quiet₁ gr.2.2.sub⟩
  | there p =>
      have apartRest : BoundsApart σ e.state.st (Arms.addresses blocks rest) :=
        (BoundsApart.sub apart fun x m => List.mem_append_right _ m).extend
          eba ata (fun x m mr => nodup_apart nodup m mr)
      have shows := ihr rest'' path ρ ids env k e.state lo hi p valid
        ⟨Coherent.grow inv.coherent ga.2 ga.1.1, inv.agree, inv.holds⟩
        ⟨orderedR, Nat.le_trans below ga.2.next, SkelArms.Ordered.apart orderedR below apartR ga.2,
          quiet.grow ga.2.sub⟩
        differsR hnone nodupR apartRest (Recorded.sub recorded fun x m => List.mem_append_right _ m)
      refine ⟨shows.1, Process.every_mono _ _ ?_ (fun _ h => h) shows.2⟩
      intro mids h
      obtain ⟨ρ₁, le₁, e', m, ex, quiet₁⟩ := h
      exact ⟨ρ₁, le₁, e', List.mem_cons_of_mem _ m, ex, quiet₁⟩

include laws in
/-- A case analysis, while a skeleton is followed: it finds its entry; its arms follow the entry's
arms, and the values that the arm that ran returns are at the entry's leaves. -/
theorem cases_follow (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs mid payloads : List D.Ty}
    {t : D.Ty} (key : Key) (w : D.Who) (x : Var Γ t) (ok : D.Alternatives w t payloads)
    (gives : ∀ a, a ∈ mid → D.Gives w a) (arms : Arms D Γ mid payloads) (results : Names mid)
    (rest : Term D (Γ.extend results) outs) (iha : ∀ skel, ArmsSound σ blocks arms (some skel))
    (ihr : ∀ skel, Sound σ blocks rest (some skel)) (skel : Skel D outs) :
    Sound σ blocks (.cases key w x ok gives arms results rest) (some skel) := by
  intro path ρ ids env k s lo hi inv following differs hnone nodup apart recorded
  simp only [walk, Option.isSome_some, Exit.region_skel] at differs hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  generalize hhit : casesEntry σ.checks (mid := mid) (t := t) (payloads := payloads) key w
    (idOf ids x.name) (some skel) = hit at differs hnone recorded ⊢
  have found := found_of_differs (AddsPlaces.trans (walkArms_adds σ.rules σ.checks σ.definition
    σ.role blocks arms _ _ _ _).2.2 (adds_after_leaves (walk_adds σ.rules σ.checks σ.definition
    σ.role blocks rest _ _ _ _).2.2)) differs
  obtain ⟨⟨arms', r, rest'⟩, rfl⟩ : ∃ h, hit = some h := by
    cases hit with
    | none => cases found
    | some h => exact ⟨h, rfl⟩
  obtain ⟨_, e⟩ := casesEntry_hit σ.checks hhit
  obtain rfl := Option.some.inj e
  simp only [Option.isSome_some, miss_found, Option.map_some, leaves]
    at differs hnone recorded ⊢
  obtain ⟨⟨orderedA, orderedR⟩, below, ⟨apartA, apartHere, apartRest⟩, quiet⟩ := following
  have highR := Skel.Ordered.le (skel := rest') orderedR
  obtain ⟨⟨ra, ea⟩, ⟨na, eba, ata⟩, da⟩ := walkArms_adds σ.rules σ.checks σ.definition σ.role
    blocks arms (some arms') ids k s
  have ga := walkArms_grows σ.rules σ.checks σ.definition σ.role blocks arms (some arms') ids k s
    inv.scoped ((SkelArms.Ordered.below orderedA).mono (by omega))
  generalize hregions : walkArms σ.rules σ.checks σ.definition σ.role blocks arms (some arms') ids
    k s = regions at differs hnone recorded ea eba da ga ⊢
  obtain ⟨⟨rr, er⟩, ⟨nr, ebr, atr⟩, dr⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks rest (some rest') (bindIds ids results (List.range' r mid.length))
    ((afterRegions σ.rules regions.exits k (List.range' r mid.length) mid 0).enter
      σ.rules mid) regions.state
  obtain ⟨differsA, differsR⟩ := differs_both da dr differs
  have refsR : regions.state.st.refusals = [] := refusals_before ⟨rr, er⟩ hnone
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupA := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  have valid := agree_valid inv.agree inv.coherent.valid
  have recA : Recorded σ (Arms.addresses blocks arms) regions.state.st :=
    (Recorded.sub recorded fun x m => by simp [m]).strip ebr atr
      (fun x m mr => nodup_apart nodup₁ m mr)
  have shows := iha arms' path ρ ids env k s lo r _ (laws.pick ok (env.get x) (valid t x)) inv
    ⟨orderedA, by omega, apartA, quiet⟩
    (by rw [hregions]; exact differsA) (by rw [hregions]; exact refsR) nodupA
    (BoundsApart.sub apart fun x m => by simp [m]) (by rw [hregions]; exact recA)
  rw [hregions] at shows
  have apartR : BoundsApart σ regions.state.st (rest.addresses blocks) :=
    (BoundsApart.sub apart fun x m => by simp [m]).extend eba ata
      (fun x m mr => nodup_apart nodup₁ m mr)
  have afterRest : ∀ (mids : HList σ.sem.Val mid), (∃ ρ', ρ.Le ρ' ∧ ∃ e, e ∈ regions.exits ∧
      ExitInv σ ρ' e regions.state.st mids ∧ ArmsFollowed (some arms') r ρ' regions.state.st) →
      Shows σ blocks rest path (env.extend results mids) (fun vs => ∃ ρ', ρ.Le ρ' ∧
        ExitInv σ ρ' (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
          (bindIds ids results (List.range' r mid.length))
          ((afterRegions σ.rules regions.exits k (List.range' r mid.length) mid 0).enter
            σ.rules mid) regions.state).region
          (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
            (bindIds ids results (List.range' r mid.length))
            ((afterRegions σ.rules regions.exits k (List.range' r mid.length) mid 0).enter
              σ.rules mid) regions.state).state.st vs ∧
        Followed (some rest') hi ρ'
          (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
            (bindIds ids results (List.range' r mid.length))
            ((afterRegions σ.rules regions.exits k (List.range' r mid.length) mid 0).enter
              σ.rules mid) regions.state).state.st) := by
    intro mids h
    obtain ⟨ρ₁, le, e, he, ex, quiet₁⟩ := h
    have validM : σ.AllValid mids := allValid_of_valuesOf ex.rets ex.coherent.valid
    obtain ⟨coh, le₂, look, quiet₂⟩ := leaves_at ex.coherent (σ.sem.dyns mids) validM
      (by rw [σ.sem.dyns_length]; exact Nat.le_trans (Nat.le_trans highR below) ga.2.2.next)
      (by rw [σ.sem.dyns_length]; exact apartHere.grows (by omega) ga.2.2) quiet₁ (Nat.le_refl r)
    rw [σ.sem.dyns_length] at look quiet₂
    have inv' := afterRegions_inv laws he inv le ex results coh le₂ look
    have shows' := ihr rest' path _ _ _ _ regions.state (r + mid.length) hi inv'
      ⟨orderedR, Nat.le_trans below ga.2.2.next,
        Skel.Ordered.apart orderedR below apartRest ga.2.2, quiet₂⟩
      differsR hnone nodupR apartR (Recorded.sub recorded fun x m => by simp [m])
    exact ⟨shows'.1, Process.every_mono _ _ (fun vs h' => by
      obtain ⟨ρ'', le'', ex', f⟩ := h'
      exact ⟨ρ'', le.trans (le₂.trans le''), ex', f⟩) (fun _ h => h) shows'.2⟩
  simp only [Shows, Term.EveryLoop, Term.denote]
  refine ⟨⟨shows.1, ?_⟩, ?_⟩
  · exact Process.every_mono _ _ (fun mids h => (afterRest mids h).1) (fun _ _ => trivial) shows.2
  · rw [Process.every_bind]
    exact Process.every_mono _ _ (fun mids h => (afterRest mids h).2) (fun _ h => h) shows.2

include laws in
/-- A loop, while a skeleton is followed: it finds its entry; each iteration starts from the
valuation before the loop, with its number and the carried values at the leaves of the entry's
body, and its body follows the entry's body; after the last, the values that it gives are at the
entry's leaves. -/
theorem loop_follow (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs carried each : List D.Ty}
    (key : Key) (w : D.Who) (times : Times D w Γ)
    (gives : ∀ a, a ∈ carried ++ each → D.Gives w a) (init : HList (Var Γ) carried)
    (inputs : Names (D.index w :: carried)) (body : Term D (Γ.extend inputs) (carried ++ each))
    (results : Names (carried ++ each.map (D.collected times.size)))
    (rest : Term D (Γ.extend results) outs)
    (ihb : ∀ skel, Sound σ blocks body (some skel)) (ihr : ∀ skel, Sound σ blocks rest (some skel))
    (skel : Skel D outs) :
    Sound σ blocks (.loop key w times gives init inputs body results rest) (some skel) := by
  intro path ρ ids env k s lo hi inv following differs hnone nodup apart recorded
  have lawful : OpFacts.Lawful σ.rules.ops σ.R σ.Runs := laws.ops
  simp only [walk, Option.isSome_some, Exit.region_skel] at differs hnone recorded ⊢
  simp only [Term.addresses] at nodup apart recorded
  generalize hhit : loopEntry σ.checks (carried := carried) (each := each) key w
    (fun count => times.follows σ.checks ids count) (idsOf ids init) (some skel) = hit
    at differs hnone recorded ⊢
  have found := found_of_differs (adds_after_leaves (AddsPlaces.trans (walk_adds σ.rules σ.checks
    σ.definition σ.role blocks body _ _ _ _).2.2 (AddsPlaces.trans (AddsPlaces.with_st _ _)
    (adds_after_leaves (walk_adds σ.rules σ.checks σ.definition σ.role blocks rest _ _ _ _).2.2))))
    differs
  obtain ⟨⟨inp, body', r, rest'⟩, rfl⟩ : ∃ h, hit = some h := by
    cases hit with
    | none => cases found
    | some h => exact ⟨h, rfl⟩
  obtain ⟨_, _, e⟩ := loopEntry_hit σ.checks hhit
  obtain rfl := Option.some.inj e
  simp only [Option.isSome_some, miss_found, Option.map_some, leaves]
    at differs hnone recorded ⊢
  obtain ⟨⟨lowInputs, orderedB, orderedR⟩, below,
    ⟨apartInputs, apartB, apartHere, apartRest⟩, quiet⟩ := following
  have highB := Skel.Ordered.le (skel := body') orderedB
  have highR := Skel.Ordered.le (skel := rest') orderedR
  have notHere := (List.nodup_cons.mp nodup).1
  have nodup₁ := (List.nodup_cons.mp nodup).2
  have nodupB := (List.nodup_append.mp nodup₁).1
  have nodupR := (List.nodup_append.mp nodup₁).2.1
  have headIn : (List.range' inp (carried.length + 1)).headD 0 = inp := by
    rw [List.range'_succ]; rfl
  have tailIn : (List.range' inp (carried.length + 1)).tail = List.range' (inp + 1) carried.length := by
    rw [List.range'_succ]; rfl
  have scopeB : Scoped (Γ.extend inputs) (bindIds ids inputs (List.range' inp (carried.length + 1)))
      s.st :=
    ⟨inv.coherent.wf, inv.scoped.2.bind inputs _ (by simp) fun i m => by
      have := mem_range'_bounds m
      omega⟩
  obtain ⟨⟨rb, eb⟩, ⟨nb, ebb, atb⟩, db⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks body (some body') (bindIds ids inputs (List.range' inp (carried.length + 1)))
    (bodyKnown σ.rules k ids times ((List.range' inp (carried.length + 1)).headD 0)
      (List.range' inp (carried.length + 1)).tail carried) s
  have gb := walk_grows σ.rules σ.checks σ.definition σ.role blocks body (some body')
    (bindIds ids inputs (List.range' inp (carried.length + 1)))
    (bodyKnown σ.rules k ids times ((List.range' inp (carried.length + 1)).headD 0)
      (List.range' inp (carried.length + 1)).tail carried) s scopeB
    ((Skel.Ordered.below orderedB).mono (by omega))
  generalize he : walk σ.rules σ.checks σ.definition σ.role blocks body (some body')
    (bindIds ids inputs (List.range' inp (carried.length + 1)))
    (bodyKnown σ.rules k ids times ((List.range' inp (carried.length + 1)).headD 0)
      (List.range' inp (carried.length + 1)).tail carried) s = e
    at differs hnone recorded eb ebb db gb ⊢
  have rbs := recordBound_state (D := D) ⟨σ.definition, blocks, some key, σ.role⟩ k ids
    e.state.st times
  generalize hst₁ : recordBound ⟨σ.definition, blocks, some key, σ.role⟩ k ids e.state.st times =
    st₁ at differs hnone recorded rbs ⊢
  obtain ⟨rbt, rbn, rbr, nbd, ebd, atd⟩ := rbs
  obtain ⟨⟨rr, er⟩, ⟨nbr, ebr, atr⟩, dr⟩ := walk_adds σ.rules σ.checks σ.definition σ.role
    blocks rest (some rest') (bindIds ids results (List.range' r (carried.length + each.length)))
    ((afterLoop σ.rules e.region k (timesBound k ids times)
      (List.range' r (carried.length + each.length)) ((idsOf ids init).map k.rangeOf)
      (List.range' inp (carried.length + 1)).tail e.rets
      (carried ++ each.map (D.collected times.size))).enter σ.rules
      (carried ++ each.map (D.collected times.size))) { e.state with st := st₁ }
  obtain ⟨differsB, differsR⟩ := differs_both db dr differs
  have refsE : e.state.st.refusals = [] := by
    have := refusals_before ⟨rr, er⟩ hnone
    simp only at this
    rw [rbr] at this
    exact this
  have recB : Recorded σ (body.addresses blocks) e.state.st :=
    ((Recorded.sub recorded fun x m => List.mem_cons_of_mem _ (List.mem_append_left _ m)).strip
      ebr atr (fun x m mr => nodup_apart nodup₁ m mr)).strip (by simp only; rw [ebd])
      (Bnew := [(blocks, key)]) (fun q m => ⟨blocks, key, atd q m, List.mem_singleton_self _⟩)
      (fun x m mr => by
        simp only [List.mem_singleton] at mr
        subst mr
        exact notHere (List.mem_append_left _ m))
  have apartBounds : BoundsApart σ s.st (body.addresses blocks) :=
    fun q m bl key' eq inB => apart q m bl key' eq
      (List.mem_cons_of_mem _ (List.mem_append_left _ inB))
  -- the body at an iteration
  have bodyInv : ∀ (i : Nat) (state : σ.sem.LoopState carried each),
      i < σ.sem.times times env →
      LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf)
        (List.range' inp (carried.length + 1)).tail (env.all init) i state →
      Inv σ (ρ.setFrom inp (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)))
        (bindIds ids inputs (List.range' inp (carried.length + 1)))
        (env.extend inputs (.cons (σ.sem.index w i) state.1))
        (bodyKnown σ.rules k ids times ((List.range' inp (carried.length + 1)).headD 0)
          (List.range' inp (carried.length + 1)).tail carried) s.st ∧
      Following (some body') (inp + (carried.length + 1)) r
        (ρ.setFrom inp (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1))) s.st := by
    intro i state lt la
    have validL : σ.AllValid (HList.cons (σ.sem.index w i) state.1) :=
      allValid_cons.mpr ⟨(laws.index w i).1, la.carriedValid⟩
    have lenL : (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)).length =
        carried.length + 1 := by rw [σ.sem.dyns_length]; rfl
    obtain ⟨coh, le₁, look, quiet'⟩ := leaves_at inv.coherent
      (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)) validL (by rw [lenL]; omega)
      (by rw [lenL]; exact apartInputs) quiet lowInputs
    rw [lenL] at look quiet'
    refine ⟨⟨coh, agree_extend inputs (HList.cons (σ.sem.index w i) state.1) _
      (inv.agree.le le₁) look, ?_⟩, orderedB, by omega, apartB, quiet'⟩
    have hi : (ρ.setFrom inp (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)))
        ((List.range' inp (carried.length + 1)).headD 0) = some ⟨D.index w, σ.sem.index w i⟩ := by
      rw [headIn]
      have := setFrom_at ρ inp (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)) 0
        (by rw [lenL]; omega)
      rw [Nat.add_zero] at this
      rw [this]
      rfl
    have lookC : valuesOf (ρ.setFrom inp (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)))
        (List.range' inp (carried.length + 1)).tail = some (σ.sem.dyns state.1) := by
      rw [List.range'_succ] at look
      exact valuesOf_tail look
    exact bodyKnown_holds laws (inv.holds.le le₁) (inv.agree.le le₁) coh.valid times lt hi lookC
  have bodyShows : ∀ (i : Nat) (state : σ.sem.LoopState carried each),
      i < σ.sem.times times env →
      LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf)
        (List.range' inp (carried.length + 1)).tail (env.all init) i state →
      Shows σ blocks body (path ++ [.iteration key i])
        (env.extend inputs (.cons (σ.sem.index w i) state.1)) (fun out => ∃ ρ',
          (ρ.setFrom inp (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1))).Le ρ' ∧
          ExitInv σ ρ' e.region e.state.st out ∧ Followed (some body') r ρ' e.state.st) := by
    intro i state lt la
    obtain ⟨invB, followingB⟩ := bodyInv i state lt la
    have shows := ihb body' (path ++ [.iteration key i]) _ _ _ _ s _ _ invB followingB
      (by rw [he]; exact differsB) (by rw [he]; exact refsE) nodupB apartBounds
      (by rw [he]; exact recB)
    rw [he] at shows
    exact shows
  -- one iteration keeps what holds
  have keeps : ∀ (i : Nat) (state : σ.sem.LoopState carried each),
      i < σ.sem.times times env →
      LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf)
        (List.range' inp (carried.length + 1)).tail (env.all init) i state →
      (σ.sem.loopStep w inputs (fun path' env' => Term.denote σ.sem body path' env') key path env i
        state).Every σ.permitted (fun state' => LoopAt (σ := σ) e.region
          ((idsOf ids init).map k.rangeOf) (List.range' inp (carried.length + 1)).tail
          (env.all init) (i + 1) state')
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
    have hcid : ρ' ((List.range' inp (carried.length + 1)).tail.getD j 0) = some d₀ := by
      rw [tailIn, range'_getD jlt]
      have := setFrom_at ρ inp (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)) (j + 1)
        (by rw [lenL]; omega)
      rw [show inp + (j + 1) = inp + 1 + j by omega] at this
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
  have I0 : LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf)
      (List.range' inp (carried.length + 1)).tail (env.all init) 0
      (env.all init, HList.empties each) := by
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
  have apartR : BoundsApart σ { e.state with st := st₁ }.st (rest.addresses blocks) := by
    intro q m bl key' eq inR
    simp only at m
    rw [ebd] at m
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
      · exact apart q m bl key' eq (List.mem_cons_of_mem _ (List.mem_append_right _ inR))
  have growsE : St.Grows s.st e.state.st := gb.2
  have growsT : St.Grows s.st st₁ :=
    ⟨by rw [rbn]; exact growsE.next, by rw [rbt]; exact growsE.table⟩
  have afterRest : ∀ (state : σ.sem.LoopState carried each),
      LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf)
        (List.range' inp (carried.length + 1)).tail (env.all init) (σ.sem.times times env) state →
      Shows σ blocks rest path
        (env.extend results (state.1.append (σ.sem.collected times.size state.2)))
        (fun vs => ∃ ρ', ρ.Le ρ' ∧ ExitInv σ ρ'
          (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
            (bindIds ids results (List.range' r (carried.length + each.length)))
            ((afterLoop σ.rules e.region k (timesBound k ids times)
              (List.range' r (carried.length + each.length)) ((idsOf ids init).map k.rangeOf)
              (List.range' inp (carried.length + 1)).tail e.rets
              (carried ++ each.map (D.collected times.size))).enter σ.rules
              (carried ++ each.map (D.collected times.size))) { e.state with st := st₁ }).region
          (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
            (bindIds ids results (List.range' r (carried.length + each.length)))
            ((afterLoop σ.rules e.region k (timesBound k ids times)
              (List.range' r (carried.length + each.length)) ((idsOf ids init).map k.rangeOf)
              (List.range' inp (carried.length + 1)).tail e.rets
              (carried ++ each.map (D.collected times.size))).enter σ.rules
              (carried ++ each.map (D.collected times.size))) { e.state with st := st₁ }).state.st
          vs ∧
          Followed (some rest') hi ρ'
            (walk σ.rules σ.checks σ.definition σ.role blocks rest (some rest')
              (bindIds ids results (List.range' r (carried.length + each.length)))
              ((afterLoop σ.rules e.region k (timesBound k ids times)
                (List.range' r (carried.length + each.length)) ((idsOf ids init).map k.rangeOf)
                (List.range' inp (carried.length + 1)).tail e.rets
                (carried ++ each.map (D.collected times.size))).enter σ.rules
                (carried ++ each.map (D.collected times.size))) { e.state with st := st₁ }).state.st)
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
    obtain ⟨coh₂, le₂, look, quiet₂⟩ := leaves_at cohE
      (σ.sem.dyns (state.1.append (σ.sem.collected times.size state.2))) validR
      (by rw [lenR]; exact Nat.le_trans (Nat.le_trans highR below) growsT.next)
      (by rw [lenR]; exact apartHere.grows (by omega) growsT) (quiet.grow growsT.sub)
      (by omega)
    rw [lenR] at look quiet₂
    have bounds := timesBound_ok laws inv.holds inv.agree inv.coherent.valid times
    have inv' : Inv σ (ρ.setFrom r (σ.sem.dyns (state.1.append
        (σ.sem.collected times.size state.2))))
        (bindIds ids results (List.range' r (carried.length + each.length)))
        (env.extend results (state.1.append (σ.sem.collected times.size state.2)))
        ((afterLoop σ.rules e.region k (timesBound k ids times)
          (List.range' r (carried.length + each.length)) ((idsOf ids init).map k.rangeOf)
          (List.range' inp (carried.length + 1)).tail e.rets
          (carried ++ each.map (D.collected times.size))).enter σ.rules
          (carried ++ each.map (D.collected times.size))) st₁ := by
      refine ⟨coh₂, agree_extend results _ _ (inv.agree.le le₂) look, ?_⟩
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
          · intro zero r' hr
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
            have hcidD : (List.range' inp (carried.length + 1)).tail.getD j 0 = cid := by
              rw [List.getD_eq_getElem?_getD, hcid]; rfl
            have hretD : e.region.rets.getD j 0 = ret := by
              show e.rets.getD j 0 = ret
              rw [List.getD_eq_getElem?_getD, hret]; rfl
            rw [← hcidD, ← hretD] at ht
            obtain ⟨d', n, hd', hn, has⟩ := la.sums j r₀ t rt (by rw [hinit, hr₀]) ht hrt
            rw [hdj] at hd'
            cases hd'
            exact ⟨n, hn, has⟩
    have shows := ihr rest' path _ _ _ _ { e.state with st := st₁ } _ hi inv'
      ⟨orderedR, Nat.le_trans below growsT.next,
        Skel.Ordered.apart orderedR below apartRest growsT, quiet₂⟩ differsR hnone nodupR apartR
      (Recorded.sub recorded fun x m => List.mem_cons_of_mem _ (List.mem_append_right _ m))
    exact ⟨shows.1, Process.every_mono _ _ (fun vs h' => by
      obtain ⟨ρ'', le'', ex', f⟩ := h'
      exact ⟨ρ'', le₂.trans le'', ex', f⟩) (fun _ h => h) shows.2⟩
  have all := Process.every_iterate_below σ.permitted (fun stop => ¬ σ.undefined stop)
    (σ.sem.loopStep w inputs (fun path' env' => Term.denote σ.sem body path' env') key path env)
    (fun i state => LoopAt (σ := σ) e.region ((idsOf ids init).map k.rangeOf)
      (List.range' inp (carried.length + 1)).tail (env.all init) i state)
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
      rw [← hst₁] at m
      rcases recordBound_mem m with m | ⟨t, count, ok, htimes, _, hb'⟩
      · rw [ebb] at m
        rcases List.mem_append.mp m with m | m
        · obtain ⟨bl, key', eq, mem⟩ := atb _ m
          rw [pq] at eq
          simp only [Place.mk.injEq, Option.some.injEq, true_and, and_true] at eq
          obtain ⟨rfl, rfl⟩ := eq
          exact (notHere (List.mem_append_left _ mem)).elim
        · exact (apart _ m blocks key pq List.mem_cons_self).elim
      · subst htimes
        cases hr : k.rangeOf (idOf ids count.name) with
        | none => rw [hr] at hb'; cases hb'
        | some r' =>
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

/-! ## Every term, while a skeleton is followed -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] {σ : Setting D Raw}

mutual
  /-- **The walk is sound while a skeleton is followed.** -/
  theorem walk_sound_follow (laws : σ.Lawful) :
      ∀ (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs)
        (skel : Skel D outs), Sound σ blocks t (some skel)
    | _, _, _, .ret xs, skel => ret_follow _ xs skel
    | blocks, _, _, .op key o args results rest, skel =>
        op_follow laws blocks key o args results rest (walk_sound_follow laws blocks rest) skel
    | blocks, _, _, .guard key w c ok why rest, skel =>
        guard_follow laws blocks key w c ok why rest (walk_sound_follow laws blocks rest) skel
    | blocks, _, _, .choose key w c ok gives onTrue onFalse results rest, skel =>
        choose_follow laws blocks key w c ok gives onTrue onFalse results rest
          (walk_sound_follow laws blocks onTrue) (walk_sound_follow laws blocks onFalse)
          (walk_sound_follow laws blocks rest) skel
    | blocks, _, _, .cases key w x ok gives arms results rest, skel =>
        cases_follow laws blocks key w x ok gives arms results rest
          (walkArms_sound_follow laws blocks arms) (walk_sound_follow laws blocks rest) skel
    | blocks, _, _, .loop key w times gives init inputs body results rest, skel =>
        loop_follow laws blocks key w times gives init inputs body results rest
          (walk_sound_follow laws blocks body) (walk_sound_follow laws blocks rest) skel
    | blocks, _, _, .block key number body results rest, skel =>
        block_follow laws blocks key number body results rest
          (walk_sound_follow laws (blocks ++ [(key, number)]) body)
          (walk_sound_follow laws blocks rest) skel
    | blocks, _, _, .attempt key w owns inputs body results rest, skel =>
        attempt_follow laws blocks key w owns inputs body results rest
          (walk_sound_follow laws blocks body) (walk_sound_follow laws blocks rest) skel
  /-- The walk of arms is sound while the arms of a skeleton are followed. -/
  theorem walkArms_sound_follow (laws : σ.Lawful) :
      ∀ (blocks : List (Key × Nat)) {Γ : Ctx D.Ty} {mid payloads : List D.Ty}
        (arms : Arms D Γ mid payloads) (skel : SkelArms D mid payloads),
        ArmsSound σ blocks arms (some skel)
    | blocks, _, _, _, .nil, skel => armsNil_follow blocks skel
    | blocks, _, _, _, .cons inputs arm rest, skel =>
        armsCons_follow laws blocks inputs arm rest (walk_sound_follow laws blocks arm)
          (walkArms_sound_follow laws blocks rest) skel
end

end

end Zkc.Core.Analysis.Facts
