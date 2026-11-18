module

public import Zkc.Core.Facts.Body.OperationSound

@[expose] public section

/-!
The three properties of a choice from those of its regions: `ChooseGrowsStatement`,
`ChooseRunsStatement`, `ChooseSoundStatement`.
-/

namespace Zkc.Core.BodyAnalysis

/-! ## What a walk returns, how the state grows -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw) (notes : Annotations Raw)

/-- **A walk returns as many identifiers as the term's types**: those of its exit. -/
theorem walk_returned_length (cursor : StaticCursor) :
    ∀ {Γ : Ctx D.Ty} {outs : List D.Ty} (t : Term D Γ outs) (ids : Ctx Ident)
      (s : State Raw) (k : cfg.domain.State),
      (walk cfg notes cursor t ids s k).returned.length = outs.length
  | _, _, .ret exit, ids, _, _ => idsOf_length ids exit
  | _, _, .step _ _ _ rest, _, _, _ => walk_returned_length cursor.next rest _ _ _


end

/-! ## Growth combined -/

section
variable {D : Dialect} {Raw : Type} {cfg : Config D Raw}

/-- Growth, then growth: by both counts, with the bounds of both. -/
theorem Grew.trans {addresses : List (List (Key × Nat) × Key)} {s t u : State Raw} {n m : Nat}
    (first : Grew cfg addresses s t n) (second : Grew cfg addresses t u m) :
    Grew cfg addresses s u (n + m) := by
  obtain ⟨table, wf, next, leaves, ⟨new, refusals⟩, bnew, bounds, added⟩ := first
  obtain ⟨table', wf', next', leaves', ⟨new', refusals'⟩, bnew', bounds', added'⟩ := second
  refine ⟨table.trans table', wf', Nat.le_trans next next', ?_, ⟨new' ++ new, ?_⟩, bnew' ++ bnew,
    ?_, fun q m => ?_⟩
  · rw [leaves', leaves, Nat.add_assoc]
  · rw [refusals', refusals, List.append_assoc]
  · rw [bounds', bounds, List.append_assoc]
  · rcases List.mem_append.mp m with m | m
    · exact added' q m
    · exact added q m

/-- Growth adding bounds at some addresses adds them at more addresses. -/
theorem Grew.widen {addresses addresses' : List (List (Key × Nat) × Key)} {s t : State Raw} {n : Nat}
    (grew : Grew cfg addresses s t n) (sub : ∀ a, a ∈ addresses → a ∈ addresses') :
    Grew cfg addresses' s t n := by
  obtain ⟨table, wf, next, leaves, refusals, bnew, bounds, added⟩ := grew
  refine ⟨table, wf, next, leaves, refusals, bnew, bounds, fun q m => ?_⟩
  obtain ⟨bl, key, place, at_⟩ := added q m
  exact ⟨bl, key, place, sub _ at_⟩

/-- Growth by a count is growth by an equal count. -/
theorem Grew.count {addresses : List (List (Key × Nat) × Key)} {s t : State Raw} {n m : Nat}
    (grew : Grew cfg addresses s t n) (same : n = m) : Grew cfg addresses s t m := by
  subst same
  exact grew

/-- Dropping a region's refusals keeps its values. -/
theorem discount_values (entry : cfg.domain.State) (before after : State Raw) :
    (discount cfg entry before after).values = after.values := by
  unfold discount
  split <;> rfl

/-- Dropping a region's refusals keeps its leaf counter. -/
theorem discount_leaves (entry : cfg.domain.State) (before after : State Raw) :
    (discount cfg entry before after).leaves = after.leaves := by
  unfold discount
  split <;> rfl

/-- Dropping a region's refusals keeps its bounds. -/
theorem discount_bounds (entry : cfg.domain.State) (before after : State Raw) :
    (discount cfg entry before after).bounds = after.bounds := by
  unfold discount
  split <;> rfl

/-- A region whose entry state is not dead counts. -/
theorem discount_alive {entry : cfg.domain.State} (alive : cfg.domain.dead entry = false)
    (before after : State Raw) : discount cfg entry before after = after := by
  simp only [discount, alive, Bool.false_eq_true, ↓reduceIte]

/-- Dropping the refusals of a region keeps its growth. -/
theorem Grew.discount {addresses : List (List (Key × Nat) × Key)} (entry : cfg.domain.State)
    {before after : State Raw} {n : Nat} (grew : Grew cfg addresses before after n) :
    Grew cfg addresses before (discount cfg entry before after) n := by
  unfold Zkc.Core.BodyAnalysis.discount
  split
  · obtain ⟨table, wf, next, leaves, _, bounds⟩ := grew
    exact ⟨table, wf, next, leaves, ⟨[], rfl⟩, bounds⟩
  · exact grew

/-- New values grow the state by no leaf. -/
theorem Grew.values {addresses : List (List (Key × Nat) × Key)} {s : State Raw} {v : Values Raw}
    (grew : Values.Grew s.values v) : Grew cfg addresses s { s with values := v } 0 :=
  ⟨grew.1, grew.2.1, grew.2.2, rfl, ⟨[], rfl⟩, [], rfl, fun _ m => nomatch m⟩

end

/-! ## The two regions of a choice -/

section
variable {D : Dialect} {Raw : Type} (cfg : Config D Raw)

/-- The two regions of a choice, with the state and the domain's state at the second's entry
named: the first's exit state, its refusals dropped when `trueKnown` is dead, and the domain's
state at the choice's entry with the condition assumed false there. -/
theorem chooseRegions_eq {mid : List D.Ty} (condition : Ident) (entry : State Raw)
    (known trueKnown : cfg.domain.State) (first : Exit D Raw cfg.domain.State mid)
    (second : State Raw → cfg.domain.State → Exit D Raw cfg.domain.State mid) :
    ∃ afterFirst falseKnown, afterFirst = discount cfg trueKnown entry first.state ∧
      falseKnown = cfg.domain.assume Asks.nobody afterFirst.values.table known condition false ∧
      chooseRegions cfg condition entry known trueKnown first second =
        ⟨first, second afterFirst falseKnown,
          discount cfg falseKnown afterFirst (second afterFirst falseKnown).state⟩ :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- **The two regions of a choice grow the state when each does**, by the leaves of both, adding
bounds at the addresses of both. -/
theorem chooseRegions_grew {mid : List D.Ty} {A B : List (List (Key × Nat) × Key)} {m n : Nat}
    (condition : Ident) {entry : State Raw} (known trueKnown : cfg.domain.State)
    {first : Exit D Raw cfg.domain.State mid}
    {second : State Raw → cfg.domain.State → Exit D Raw cfg.domain.State mid}
    (firstGrew : Grew cfg A entry first.state m)
    (secondGrew : ∀ s k, s.values.WF → Grew cfg B s (second s k).state n) :
    Grew cfg (A ++ B) entry (chooseRegions cfg condition entry known trueKnown first second).state
      (m + n) :=
  have one := Grew.discount trueKnown firstGrew
  (one.widen fun _ m => List.mem_append_left _ m).trans
    ((Grew.discount _ (secondGrew _ _ one.2.1)).widen fun _ m => List.mem_append_right _ m)

end

/-! ## A choice grows the state -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw) (notes : Annotations Raw)

/-- After its regions, a choice adds selections to the values. -/
theorem chooseExit_grew {mid : List D.Ty} {t : D.Ty} (w : D.Who) (condition : Ident)
    (ok : D.Condition w t) (before : cfg.domain.State) (first second : Exit D Raw cfg.domain.State mid)
    (addresses : List (List (Key × Nat) × Key)) {s : State Raw} (wf : s.values.WF) :
    Grew cfg addresses s (chooseExit cfg w condition ok before first second s).state 0 :=
  Grew.values (Values.selectAll_grew condition first.returned second.returned wf)

/-- **A choice grows the state when its regions do**, by their leaves. -/
theorem chooseGrows : ChooseGrowsStatement cfg notes := by
  intro cursor key Γ mid t w c ok gives onTrue onFalse growsTrue growsFalse ids s k wf
  have entry := atEntry_entered cfg notes (.instruction cursor key) ids s k wf
  simp only [walkInstr, Instr.leafCount]
  generalize atEntry cfg notes (.instruction cursor key) ids s k = e at entry
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry ⊢
  generalize cfg.domain.assume Asks.nobody E.values.table Ek (idOf ids c.name) true = trueKnown
  have regions := chooseRegions_grew cfg (idOf ids c.name) Ek trueKnown
    (growsTrue ids E trueKnown entry.wf) (growsFalse ids)
  exact (((Grew.of_entered cfg _ entry).trans
    (regions.widen fun _ m => List.mem_cons_of_mem _ m)).trans
    (chooseExit_grew cfg w (idOf ids c.name) ok Ek _ _ _ regions.2.1)).count
    (by rw [Nat.zero_add, Nat.add_zero])


end

/-! ## A choice runs its entry -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

/-- **A choice runs its entry of the skeleton when its regions run theirs**: the region that the
condition chooses runs, followed by the choice's rest, which runs from the leaves at that region's
exit, where the selections read what the region returned. -/
theorem chooseRuns : ChooseRunsStatement σ := by
  intro laws cursor key Γ mid t w c ok gives onTrue onFalse growsTrue growsFalse runsTrue runsFalse
  intro path ρ ids env s k table mid₀ outs rest after cont
  dsimp only
  intro scope sub notUndefined next
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k scope.wf
  have condition := scope.idOf_reads c
  rw [Instr.denote_choose] at notUndefined ⊢
  simp only [walkInstr] at sub next ⊢
  revert sub next
  generalize atEntry σ.cfg σ.notes (.instruction cursor key) ids s k = e at entry
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry ⊢
  have scopeE := scope.grow entry.1 (Nat.le_of_eq entry.2.1.symm)
  generalize σ.cfg.domain.assume Asks.nobody E.values.table Ek (idOf ids c.name) true = trueKnown
  have firstRaw := growsTrue ids E trueKnown entry.wf
  have runsOne := runsTrue path ρ ids env E trueKnown table (.cons path rest after) cont
  have lengthOne := walk_returned_length σ.cfg σ.notes (cursor.region key) onTrue ids E trueKnown
  generalize walk σ.cfg σ.notes (cursor.region key) onTrue ids E trueKnown = one at firstRaw runsOne lengthOne ⊢
  obtain ⟨afterFirst, falseKnown, hA, -, regions⟩ := chooseRegions_eq σ.cfg (idOf ids c.name) E Ek
    trueKnown one (walk σ.cfg σ.notes (cursor.otherwise key) onFalse ids)
  rw [regions]
  dsimp only
  have first := Grew.discount trueKnown firstRaw
  have valuesOne := discount_values trueKnown E one.state
  have leavesOne := discount_leaves trueKnown E one.state
  rw [← hA] at first valuesOne leavesOne
  have secondRaw := growsFalse ids afterFirst falseKnown first.2.1
  have second := Grew.discount falseKnown secondRaw
  have runsTwo := runsFalse path ρ ids env afterFirst falseKnown table (.cons path rest after) cont
  have lengthTwo := walk_returned_length σ.cfg σ.notes (cursor.otherwise key) onFalse ids afterFirst falseKnown
  generalize walk σ.cfg σ.notes (cursor.otherwise key) onFalse ids afterFirst falseKnown = two
    at secondRaw second runsTwo lengthTwo ⊢
  have valuesTwo := discount_values falseKnown afterFirst two.state
  have leavesTwo := discount_leaves falseKnown afterFirst two.state
  generalize discount σ.cfg falseKnown afterFirst two.state = final at second valuesTwo leavesTwo ⊢
  intro sub next
  have finalLe : final.values.table.Le table :=
    (Values.selectAll_table_le (idOf ids c.name) one.returned two.returned final.values).trans sub
  have twoFinal : two.state.values.table.Le final.values.table := by
    rw [valuesTwo]
    exact Table.Le.refl _
  have oneFinal : one.state.values.table.Le final.values.table := by
    rw [← valuesOne]
    exact second.1
  have conditionFinal := Reads.mono (entry.1.1.trans (first.1.trans second.1)) (fun _ _ h => h)
    condition
  have lengths : one.returned.length = two.returned.length := lengthOne.trans lengthTwo.symm
  have oneLeaves : one.state.leaves ≤ final.leaves := by
    rw [leavesTwo, secondRaw.2.2.2.1, leavesOne]
    exact Nat.le_add_right _ _
  have twoLeaves : two.state.leaves ≤ final.leaves := Nat.le_of_eq leavesTwo.symm
  have truth := laws.2 ok (env.get c)
  cases holds : σ.sem.holds ok (env.get c) with
  | true =>
      rw [holds] at truth
      simp only [holds, Bool.cond_true] at notUndefined ⊢
      refine Skel.Runs.chooseTrue (env.get c) (Reads.mono finalLe (fun _ _ h => h) conditionFinal)
        holds ?_
      refine runsOne scopeE (oneFinal.trans finalLe) notUndefined
        fun ρ' values le fresh reads undefined => .resume (next ρ' values le ?_ ?_ undefined)
      · exact fun n above => fresh n (Nat.le_trans oneLeaves above)
      · exact Values.selectAll_reads one.returned two.returned lengths
          (Reads.mono (Table.Le.refl _) le conditionFinal) truth
          (ReadsAll.mono oneFinal (fun _ _ h => h) reads)
  | false =>
      rw [holds] at truth
      simp only [holds, Bool.cond_false] at notUndefined ⊢
      refine Skel.Runs.chooseFalse (env.get c) (Reads.mono finalLe (fun _ _ h => h) conditionFinal)
        holds ?_
      have scopeA := scope.grow ⟨entry.1.1.trans first.1, first.2.1,
        Nat.le_trans entry.1.2.2 first.2.2.1⟩
        (by rw [first.2.2.2.1, entry.2.1]; exact Nat.le_add_right _ _)
      refine runsTwo scopeA (twoFinal.trans finalLe) notUndefined
        fun ρ' values le fresh reads undefined => .resume (next ρ' values le ?_ ?_ undefined)
      · exact fun n above => fresh n (Nat.le_trans twoLeaves above)
      · exact Values.selectAll_reads one.returned two.returned lengths
          (Reads.mono (Table.Le.refl _) le conditionFinal) truth
          (ReadsAll.mono twoFinal (fun _ _ h => h) reads)


end

/-! ## Addresses and bounds -/

section
variable {D : Dialect} {Raw : Type}

/-- Distinct addresses of two parts: each part's are distinct, and no address is in both. -/
theorem nodup_append_parts {α : Type} {A B : List α} (distinct : (A ++ B).Nodup) :
    A.Nodup ∧ B.Nodup ∧ ∀ a, a ∈ A → a ∉ B := by
  have parts := List.pairwise_append.mp distinct
  exact ⟨parts.1, parts.2.1, fun a inA inB => parts.2.2 a inA a inB rfl⟩

/-- The bounds of the setting at some addresses, recorded after a walk that added bounds only at
other addresses, were recorded before it. -/
theorem Recorded.before {σ : Setting D Raw} {A B C : List (List (Key × Nat) × Key)} {t u : State Raw}
    (recorded : Recorded σ C u) (sub : ∀ a, a ∈ A → a ∈ C) (apart : ∀ a, a ∈ A → a ∉ B)
    (adds : ∃ new, u.bounds = new ++ t.bounds ∧
      ∀ q, q ∈ new → ∃ bl key, q.1 = σ.cfg.place bl key ∧ (bl, key) ∈ B) :
    Recorded σ A t := by
  intro p b bl key inF place at_
  obtain ⟨new, bounds, added⟩ := adds
  have inU := recorded p b bl key inF place (sub _ at_)
  rw [bounds] at inU
  rcases List.mem_append.mp inU with m | m
  · obtain ⟨bl', key', place', at'⟩ := added _ m
    rw [place] at place'
    simp only [Config.place, Place.mk.injEq, Option.some.injEq, true_and, and_true] at place'
    obtain ⟨rfl, rfl⟩ := place'
    exact absurd at' (apart _ at_)
  · exact m

/-- No bound recorded is at some addresses, after a walk that added bounds only at other
addresses, when none was before. -/
theorem BoundsApart.after {σ : Setting D Raw} {A B C : List (List (Key × Nat) × Key)}
    {s t : State Raw} (before : BoundsApart σ s C) (sub : ∀ a, a ∈ A → a ∈ C)
    (apart : ∀ a, a ∈ A → a ∉ B)
    (adds : ∃ new, t.bounds = new ++ s.bounds ∧
      ∀ q, q ∈ new → ∃ bl key, q.1 = σ.cfg.place bl key ∧ (bl, key) ∈ B) :
    BoundsApart σ t A := by
  intro q m bl key place
  obtain ⟨new, bounds, added⟩ := adds
  rw [bounds] at m
  rcases List.mem_append.mp m with m | m
  · obtain ⟨bl', key', place', at'⟩ := added q m
    rw [place] at place'
    simp only [Config.place, Place.mk.injEq, Option.some.injEq, true_and, and_true] at place'
    obtain ⟨rfl, rfl⟩ := place'
    exact fun at_ => apart _ at_ at'
  · exact fun at_ => before q m bl key place (sub _ at_)

end

/-! ## A choice is sound -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

omit [DecidableEq Raw] in
/-- Refusals added, then refusals added, are refusals added. -/
theorem refusals_trans {s t u : State Raw} (first : ∃ new, t.refusals = new ++ s.refusals)
    (second : ∃ new, u.refusals = new ++ t.refusals) : ∃ new, u.refusals = new ++ s.refusals := by
  obtain ⟨new₁, r₁⟩ := first
  obtain ⟨new₂, r₂⟩ := second
  exact ⟨new₂ ++ new₁, by rw [r₂, r₁, List.append_assoc]⟩

omit [DecidableEq Raw] in
/-- A region whose exit state is not dead is told to `after`. -/
theorem mem_live {known : σ.cfg.domain.State} (alive : σ.cfg.domain.dead known = false)
    (returned : List Ident) : (Asks.nobody, known, returned) ∈ live σ.cfg known returned := by
  simp only [live, alive, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_cons_self

/-- **What a choice returns is what `Returned` says**, from what the region that ran returns: the
selections read what that region returned (its condition reads the truth that chose it), the
domain's `after` is told of that region's exit, and `leaves` of the selections' types. -/
theorem chooseExit_returned {Γ : Ctx D.Ty} {mid : List D.Ty} {t : D.Ty} (w : D.Who)
    (condition : Ident) (ok : D.Condition w t) {before : σ.cfg.domain.State}
    (first second : Exit D Raw σ.cfg.domain.State mid) {s' : State Raw} {ρ : Leaves σ.sem.Dyn}
    {ids : Ctx Ident} {env : Env σ.sem.Val Γ} {beforeTable : Table Raw}
    (beforeMeans : σ.domain.Means before beforeTable ρ) (beforeLe : beforeTable.Le s'.values.table)
    (wf : s'.values.WF) (lengths : first.returned.length = second.returned.length) {which : Bool}
    {v : σ.sem.Dyn} (decided : Reads σ.Runs σ.R.bool s'.values.table ρ condition v)
    (holds : σ.R.bool v = some which) (r : Exit D Raw σ.cfg.domain.State mid)
    (member : σ.cfg.domain.dead r.known = false → (Asks.nobody, r.known, r.returned) ∈
      live σ.cfg first.known first.returned ++ live σ.cfg second.known second.returned)
    (picked : r.returned = if which then first.returned else second.returned)
    (regionLe : r.state.values.table.Le s'.values.table) (regionLeaves : r.state.leaves ≤ s'.leaves)
    {values : HList σ.sem.Val mid} (region : Returned σ ρ ids env r.known r.state r.returned values) :
    Returned σ ρ ids env (chooseExit σ.cfg w condition ok before first second s').known
      (chooseExit σ.cfg w condition ok before first second s').state
      (chooseExit σ.cfg w condition ok before first second s').returned values := by
  obtain ⟨ρ₁, le, inv₁, reads₁⟩ := region
  have grew := Values.selectAll_grew condition first.returned second.returned wf
  have readsAt : ReadsAll σ.Runs σ.R.bool s'.values.table ρ₁
      (if which then first.returned else second.returned) (σ.sem.dyns values) := by
    rw [← picked]
    exact ReadsAll.mono regionLe (fun _ _ h => h) reads₁
  have chosen := Values.selectAll_reads first.returned second.returned lengths
    (Reads.mono (Table.Le.refl _) le decided) holds readsAt
  have valid := ReadsAll.valid inv₁.valid chosen
  have afterMeans := σ.domain.after grew.2.1.slots (σ.domain.mono (beforeLe.trans grew.1) le beforeMeans)
    (member (σ.alive inv₁.means)) (σ.domain.mono (regionLe.trans grew.1) (fun _ _ h => h) inv₁.means)
    (Asks.nobody_sound _ _ _ _)
    ⟨σ.sem.dyns values, ReadsAll.mono (regionLe.trans grew.1) (fun _ _ h => h) reads₁, chosen⟩
  have leavesMeans := σ.domain.leaves grew.2.1.slots afterMeans (ReadsAll.zip_typed values chosen valid)
  refine ⟨ρ₁, le, ⟨⟨fun n above => inv₁.fresh n (Nat.le_trans regionLeaves above), fun τ x => ?_,
    inv₁.bound, grew.2.1⟩, inv₁.valid, leavesMeans⟩, chosen⟩
  obtain ⟨id, found, read⟩ := inv₁.agree τ x
  exact ⟨id, found, Reads.mono (regionLe.trans grew.1) (fun _ _ h => h) read⟩

/-- **A choice is sound when its regions are.** The region that the condition chooses starts from
a state that means the condition's truth, so it is not dead and its refusals count; the other
region's refusals count only where its entry state is not dead. -/
theorem chooseSound : ChooseSoundStatement σ := by
  intro laws cursor key Γ mid t w c ok gives onTrue onFalse growsTrue growsFalse soundTrue soundFalse
  intro path ρ ids env s k
  dsimp only
  intro inv steps defined facts everyFact unchanged
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k inv.wf
  have entryInv := fun unchanged => atEntry_inv σ laws cursor key
    (.choose w c ok gives onTrue onFalse) (path := path) inv steps facts unchanged
  have condition := inv.toScope.idOf_reads c
  have truth := laws.rules.condition ok (env.get c) (Reads.valid inv.valid condition)
  rw [Instr.denote_choose]
  simp only [walkInstr] at unchanged ⊢
  revert unchanged
  simp only [Instr.site] at entryInv
  generalize atEntry σ.cfg σ.notes (.instruction cursor key) ids s k = e at entry entryInv
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry entryInv ⊢
  generalize hT : σ.cfg.domain.assume Asks.nobody E.values.table Ek (idOf ids c.name) true
    = trueKnown
  have firstRaw := growsTrue ids E trueKnown entry.wf
  have soundOne := soundTrue path ρ ids env E trueKnown
  have lengthOne := walk_returned_length σ.cfg σ.notes (cursor.region key) onTrue ids E trueKnown
  generalize walk σ.cfg σ.notes (cursor.region key) onTrue ids E trueKnown = one at firstRaw soundOne lengthOne ⊢
  obtain ⟨afterFirst, falseKnown, hA, hF, regions⟩ := chooseRegions_eq σ.cfg (idOf ids c.name) E Ek
    trueKnown one (walk σ.cfg σ.notes (cursor.otherwise key) onFalse ids)
  rw [regions]
  dsimp only
  have first := Grew.discount trueKnown firstRaw
  have valuesOne := discount_values trueKnown E one.state
  have leavesOne := discount_leaves trueKnown E one.state
  have boundsOne := discount_bounds trueKnown E one.state
  rw [← hA] at first valuesOne leavesOne boundsOne
  have secondRaw := growsFalse ids afterFirst falseKnown first.2.1
  have second := Grew.discount falseKnown secondRaw
  have soundTwo := soundFalse path ρ ids env afterFirst falseKnown
  have lengthTwo := walk_returned_length σ.cfg σ.notes (cursor.otherwise key) onFalse ids afterFirst falseKnown
  generalize walk σ.cfg σ.notes (cursor.otherwise key) onFalse ids afterFirst falseKnown = two
    at secondRaw second soundTwo lengthTwo ⊢
  have valuesTwo := discount_values falseKnown afterFirst two.state
  have leavesTwo := discount_leaves falseKnown afterFirst two.state
  have boundsTwo := discount_bounds falseKnown afterFirst two.state
  generalize hZ : discount σ.cfg falseKnown afterFirst two.state = final
    at second valuesTwo leavesTwo boundsTwo ⊢
  intro unchanged
  -- The refusals: none is added anywhere that counts.
  obtain ⟨entryUnchanged, rest⟩ := refusals_split entry.2.2.2
    (refusals_trans first.2.2.2.2.1 second.2.2.2.2.1) unchanged
  obtain ⟨afterFirstUnchanged, finalUnchanged⟩ := refusals_split first.2.2.2.2.1
    second.2.2.2.2.1 rest
  have inv₁ := entryInv entryUnchanged
  have conditionE := Reads.mono entry.1.1 (fun _ _ h => h) condition
  have conditionFinal := Reads.mono (first.1.trans second.1) (fun _ _ h => h) conditionE
  have lengths : one.returned.length = two.returned.length := lengthOne.trans lengthTwo.symm
  have oneFinal : one.state.values.table.Le final.values.table := by
    rw [← valuesOne]
    exact second.1
  have twoFinal : two.state.values.table.Le final.values.table := by
    rw [valuesTwo]
    exact Table.Le.refl _
  have oneLeaves : one.state.leaves ≤ final.leaves := by
    rw [leavesTwo, secondRaw.2.2.2.1, leavesOne]
    exact Nat.le_add_right _ _
  have beforeLe : E.values.table.Le final.values.table := first.1.trans second.1
  cases holds : σ.sem.holds ok (env.get c) with
  | true =>
      rw [holds] at truth
      have meansTrue : σ.domain.Means trueKnown E.values.table ρ := by
        rw [← hT]
        exact σ.domain.assume inv₁.wf.slots (Asks.nobody_sound _ _ _ _) inv₁.means conditionE truth
      have aliveTrue := σ.alive meansTrue
      rw [discount_alive aliveTrue] at hA
      subst hA
      simp only [Instr.EveryFact, Instr.EveryStep, holds, Bool.cond_true]
        at everyFact
      obtain ⟨every, required, loops⟩ := soundOne ⟨inv₁.toScope, inv₁.valid, meansTrue⟩ defined.1
        everyFact afterFirstUnchanged
      simp only [holds, Bool.cond_true, Instr.EveryRequired, Instr.EveryStep,
        Instr.EveryLoop]
      refine ⟨Process.every_mono _ _ (fun values region => chooseExit_returned σ w (idOf ids c.name)
          ok one two inv₁.means beforeLe second.2.1 lengths conditionFinal truth one
          (fun alive => List.mem_append_left _ (mem_live σ alive _)) rfl oneFinal oneLeaves region)
          (fun _ h => h) every, trivial, required, fun nodup apart recorded => ?_⟩
      obtain ⟨-, nodup'⟩ := List.nodup_cons.mp nodup
      obtain ⟨nodupOne, -, disjoint⟩ := nodup_append_parts nodup'
      refine loops nodupOne ?_ ?_
      · rw [BoundsApart, entry.2.2.1]
        exact fun q m bl key' place at_ =>
          apart q m bl key' place (List.mem_cons_of_mem _ (List.mem_append_left _ at_))
      · refine Recorded.before recorded
          (fun a m => List.mem_cons_of_mem _ (List.mem_append_left _ m)) disjoint ?_
        obtain ⟨-, -, -, -, -, new, bounds, added⟩ := secondRaw
        exact ⟨new, by rw [show (chooseExit σ.cfg w (idOf ids c.name) ok Ek one two final).state.bounds
          = final.bounds from rfl, boundsTwo, bounds, boundsOne], added⟩
  | false =>
      rw [holds] at truth
      have meansFalse : σ.domain.Means falseKnown afterFirst.values.table ρ := by
        rw [hF]
        exact σ.domain.assume first.2.1.slots (Asks.nobody_sound _ _ _ _)
          (σ.domain.mono first.1 (fun _ _ h => h) inv₁.means)
          (Reads.mono first.1 (fun _ _ h => h) conditionE) truth
      have aliveFalse := σ.alive meansFalse
      rw [discount_alive aliveFalse] at hZ
      subst hZ
      simp only [Instr.EveryFact, Instr.EveryStep, holds, Bool.cond_false]
        at everyFact
      have invA : Inv σ ρ ids env falseKnown afterFirst :=
        ⟨inv₁.toScope.grow ⟨first.1, first.2.1, first.2.2.1⟩
          (by rw [first.2.2.2.1]; exact Nat.le_add_right _ _), inv₁.valid, meansFalse⟩
      obtain ⟨every, required, loops⟩ := soundTwo invA defined.2 everyFact finalUnchanged
      simp only [holds, Bool.cond_false, Instr.EveryRequired, Instr.EveryStep,
        Instr.EveryLoop]
      refine ⟨Process.every_mono _ _ (fun values region => chooseExit_returned σ w (idOf ids c.name)
          ok one two inv₁.means beforeLe second.2.1 lengths conditionFinal truth two
          (fun alive => List.mem_append_right _ (mem_live σ alive _)) rfl twoFinal
          (Nat.le_refl _) region)
          (fun _ h => h) every, trivial, required, fun nodup apart recorded => ?_⟩
      obtain ⟨-, nodup'⟩ := List.nodup_cons.mp nodup
      obtain ⟨-, nodupTwo, disjoint⟩ := nodup_append_parts nodup'
      refine loops nodupTwo ?_ ?_
      · obtain ⟨-, -, -, -, -, new, bounds, added⟩ := first
        refine BoundsApart.after (C := (cursor.blocks, key) ::
            (Term.addresses cursor.blocks onTrue ++ Term.addresses cursor.blocks onFalse))
          (B := Term.addresses cursor.blocks onTrue) ?_
          (fun a m => List.mem_cons_of_mem _ (List.mem_append_right _ m))
          (fun a m inOne => disjoint a inOne m) ⟨new, bounds, added⟩
        rw [BoundsApart, entry.2.2.1]
        exact apart
      · exact Recorded.before (B := []) recorded
          (fun a m => List.mem_cons_of_mem _ (List.mem_append_right _ m)) (fun _ _ m => nomatch m)
          ⟨[], rfl, fun _ m => nomatch m⟩

#print axioms walk_returned_length
#print axioms chooseGrows
#print axioms chooseRuns
#print axioms chooseSound

end

end Zkc.Core.BodyAnalysis
