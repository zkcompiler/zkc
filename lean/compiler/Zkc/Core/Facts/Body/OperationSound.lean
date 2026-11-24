module

public import Zkc.Core.Facts.Body.EnteringSound

@[expose] public section

/-!
The three properties of an operation (`OpGrowsStatement`, `OpRunsStatement`, `OpSoundStatement`),
for a shared one and for one kept in order, with the annotations at its entry; and the lemmas that
every kind of instruction shares: how the state grows (`Grew.of_entered`, `Grew.leaves`, the bound
of a loop recorded, `Grew.recordBound`), leaves set from a number on, and what an instruction
returns on new result leaves (`Returned.atResults`).
-/

namespace Zkc.Core.BodyAnalysis

/-! ## Growth -/

section
variable {D : Dialect} {Raw : Type}

/-- Entering, deciding and learning, with no leaf made, grow the state by no leaf and add no
bound. -/
theorem Grew.of_entered (cfg : Config D Raw) (addresses : List (List (Key × Nat) × Key))
    {s s' : State Raw} (entered : State.Entered s s') : Grew cfg addresses s s' 0 := by
  obtain ⟨⟨table, wf, next⟩, leaves, bounds, refusals⟩ := entered
  exact ⟨table, wf, next, leaves, refusals, [], by rw [bounds]; rfl, fun _ m => nomatch m⟩

/-- Entering, deciding and learning before and after leaves are made grow the state by those
leaves and add no bound. -/
theorem Grew.of_entered_leaves (cfg : Config D Raw) (addresses : List (List (Key × Nat) × Key))
    {s t u : State Raw} (count : Nat) (first : State.Entered s t)
    (second : State.Entered { t with leaves := t.leaves + count } u) :
    Grew cfg addresses s u count := by
  obtain ⟨⟨table, wf, next⟩, leaves, bounds, new, refusals⟩ := first
  obtain ⟨⟨table', wf', next'⟩, leaves', bounds', new', refusals'⟩ := second
  refine ⟨table.trans table', wf', Nat.le_trans next next', ?_, ⟨new' ++ new, ?_⟩, [], ?_,
    fun _ m => nomatch m⟩
  · rw [leaves']
    exact congrArg (· + count) leaves
  · rw [refusals', List.append_assoc]
    exact congrArg (new' ++ ·) refusals
  · rw [bounds']
    exact bounds

/-- New leaves grow the state by as many leaves, and change nothing else. -/
theorem Grew.leaves {cfg : Config D Raw} {addresses : List (List (Key × Nat) × Key)} {s : State Raw} (n : Nat)
    (wf : s.values.WF) : Grew cfg addresses s { s with leaves := s.leaves + n } n :=
  ⟨Table.Le.refl _, wf, Nat.le_refl _, rfl, ⟨[], rfl⟩, [], rfl, fun _ m => nomatch m⟩

/-- Recording a bound keeps the values, the leaf counter and the refusals. -/
theorem recordBound_same {w : D.Who} (place : Place) (answers : Asks) (count : Count D w)
    (s : State Raw) :
    (recordBound place answers count s).values = s.values ∧
      (recordBound place answers count s).leaves = s.leaves ∧
      (recordBound place answers count s).refusals = s.refusals := by
  cases count with
  | fixed n => exact ⟨rfl, rfl, rfl⟩
  | value id ok =>
      simp only [recordBound]
      split <;> exact ⟨rfl, rfl, rfl⟩

/-- Recording a bound adds at most one bound, at the place, the domains' upper bound of the count's
identifier. -/
theorem recordBound_bounds {w : D.Who} (place : Place) (answers : Asks) (count : Count D w)
    (s : State Raw) :
    ∃ new, (recordBound place answers count s).bounds = new ++ s.bounds ∧
      ∀ q, q ∈ new → q.1 = place ∧
        ∃ (t : D.Ty) (id : Ident) (ok : D.Count w t), count = .value id ok ∧
          answers.upperAt id = some q.2 := by
  cases count with
  | fixed n => exact ⟨[], rfl, fun _ m => nomatch m⟩
  | value id ok =>
      cases found : answers.upperAt id with
      | none => exact ⟨[], by simp only [recordBound, found]; rfl, fun _ m => nomatch m⟩
      | some bound =>
          refine ⟨[(place, bound)], by simp only [recordBound, found]; rfl, fun q m => ?_⟩
          rw [List.mem_singleton] at m
          subst m
          exact ⟨rfl, _, id, ok, rfl, found⟩

/-- Recording the bound of a loop at its address grows the state by no leaf. -/
theorem Grew.recordBound (cfg : Config D Raw) {addresses : List (List (Key × Nat) × Key)} {w : D.Who}
    (blocks : List (Key × Nat)) (key : Key) (answers : Asks) (count : Count D w) {s : State Raw}
    (wf : s.values.WF) (here : (blocks, key) ∈ addresses) :
    Grew cfg addresses s (Zkc.Core.BodyAnalysis.recordBound (cfg.place blocks key) answers count s) 0 := by
  obtain ⟨values, leaves, refusals⟩ := recordBound_same (cfg.place blocks key) answers count s
  obtain ⟨new, bounds, added⟩ := recordBound_bounds (cfg.place blocks key) answers count s
  refine ⟨by rw [values]; exact Table.Le.refl _, by rw [values]; exact wf,
    by rw [values]; exact Nat.le_refl _, leaves, ⟨[], refusals⟩, new, bounds, fun q m => ?_⟩
  exact ⟨blocks, key, (added q m).1, here⟩

end

/-! ## Leaves set from a number on -/

section
variable {Val : Type}

/-- Leaves set at fresh numbers extend the leaves. -/
theorem Leaves.le_setFrom {ρ : Leaves Val} {lo : Nat} (fresh : ∀ n, lo ≤ n → ρ n = none)
    (vs : List Val) : ρ.Le (ρ.setFrom lo vs) := by
  intro n v valued
  simp only [Leaves.setFrom]
  rw [ite_eq_right fun inside => by rw [fresh n inside.1] at valued; cases valued]
  exact valued

/-- Above the leaves set, nothing has a value. -/
theorem Leaves.setFrom_fresh {ρ : Leaves Val} {lo : Nat} (fresh : ∀ n, lo ≤ n → ρ n = none)
    (vs : List Val) : ∀ n, lo + vs.length ≤ n → ρ.setFrom lo vs n = none := by
  intro n above
  simp only [Leaves.setFrom]
  rw [ite_eq_right fun inside => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le inside.2 above)]
  exact fresh n (Nat.le_trans (Nat.le_add_right _ _) above)

/-- A leaf set has its value. -/
theorem Leaves.setFrom_at (ρ : Leaves Val) (lo : Nat) (vs : List Val) {j : Nat}
    (below : j < vs.length) : ρ.setFrom lo vs (lo + j) = vs[j]? := by
  simp only [Leaves.setFrom]
  rw [ite_eq_left ⟨Nat.le_add_right _ _, Nat.add_lt_add_left below _⟩, Nat.add_sub_cancel_left]

/-- Leaves set to values that are valid, over leaves whose values are valid, have valid values. -/
theorem Leaves.setFrom_valid {ρ : Leaves Val} {Valid : Val → Prop}
    (valid : ∀ n v, ρ n = some v → Valid v) {lo : Nat} {vs : List Val}
    (valid' : ∀ v, v ∈ vs → Valid v) : ∀ n v, ρ.setFrom lo vs n = some v → Valid v := by
  intro n v valued
  simp only [Leaves.setFrom] at valued
  split at valued
  · exact valid' v (List.mem_of_getElem? valued)
  · exact valid n v valued

variable {Raw : Type} {Run : Raw → List Val → List Val → Prop} {truth : Val → Option Bool}

/-- Consecutive leaves read, position by position, as many values. -/
theorem ReadsAll.leaves {table : Table Raw} {ρ : Leaves Val} :
    ∀ (count lo : Nat) (results : List Val), results.length = count →
      (∀ j, j < count → ρ (lo + j) = results[j]?) →
      ReadsAll Run truth table ρ (Ident.leaves lo count) results
  | 0, _, [], _, _ => .nil
  | count + 1, lo, x :: results, length, each =>
      .cons (.leaf (each 0 (Nat.zero_lt_succ _)))
        (ReadsAll.leaves count (lo + 1) results (Nat.succ.inj length) fun j below => by
          have valued := each (j + 1) (Nat.succ_lt_succ below)
          rwa [← Nat.add_assoc, Nat.add_right_comm lo j 1] at valued)

/-- The leaves set read their values. -/
theorem ReadsAll.setFrom {table : Table Raw} (ρ : Leaves Val) (lo : Nat) (vs : List Val) :
    ReadsAll Run truth table (ρ.setFrom lo vs) (Ident.leaves lo vs.length) vs :=
  ReadsAll.leaves _ _ _ rfl fun _ below => Leaves.setFrom_at ρ lo vs below

end

/-! ## Values with their types -/

section
variable {D : Dialect} {Raw : Type}

/-- Identifiers that read values of types read, with their types, values of those types. -/
theorem ReadsAll.zip_typed {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {Valid : sem.Dyn → Prop} {truth : sem.Dyn → Option Bool} {table : Table Raw}
    {ρ : Leaves sem.Dyn} :
    ∀ {types : List D.Ty} {ids : List Ident} (values : HList sem.Val types),
      ReadsAll Run truth table ρ ids (sem.dyns values) → (∀ v, v ∈ sem.dyns values → Valid v) →
      ∀ p, p ∈ ids.zip types → ∃ v, Reads Run truth table ρ p.1 v ∧ TypedValue sem Valid v p.2
  | [], ids, .nil, reads, _, p, m => by
      have reads' : ReadsAll Run truth table ρ ids [] := reads
      cases reads'
      exact nomatch m
  | _ :: _, ids, .cons v rest, reads, valid, p, m => by
      have reads' : ReadsAll Run truth table ρ ids (⟨_, v⟩ :: sem.dyns rest) := reads
      cases reads' with
      | cons first others =>
          rcases List.mem_cons.mp m with rfl | m
          · exact ⟨_, first, valid _ List.mem_cons_self, rfl⟩
          · exact ReadsAll.zip_typed rest others (fun v m => valid v (List.mem_cons_of_mem _ m)) p m

end

/-! ## Results on new leaves -/

section
variable {D : Dialect} {Raw : Type} {sem : Semantics D}
  {Run : Raw → List sem.Dyn → List sem.Dyn → Prop} {R : Reading sem.Dyn}

/-- Results on new leaves at the counter: the leaves extend these, nothing has a value above the
results, and the result leaves read the values. -/
theorem Leaves.results {mid : List D.Ty} {ρ : Leaves sem.Dyn} {table : Table Raw} {lo : Nat}
    (fresh : ∀ n, lo ≤ n → ρ n = none) (values : HList sem.Val mid) :
    ρ.Le (ρ.setFrom lo (sem.dyns values)) ∧
      (∀ n, lo + mid.length ≤ n → ρ.setFrom lo (sem.dyns values) n = none) ∧
      ReadsAll Run R.bool table (ρ.setFrom lo (sem.dyns values)) (Ident.leaves lo mid.length)
        (sem.dyns values) := by
  refine ⟨Leaves.le_setFrom fresh _, fun n above => ?_, ?_⟩
  · refine Leaves.setFrom_fresh fresh _ n ?_
    rw [sem.dyns_length]
    exact above
  · have set := ReadsAll.setFrom (Run := Run) (truth := R.bool) (table := table) ρ lo
      (sem.dyns values)
    rwa [sem.dyns_length] at set

end

section
variable {D : Dialect} {Raw : Type} {σ : Setting D Raw}

/-- **What an instruction returns on new result leaves is what `Returned` says**, from a region's
exit: under leaves that extend these, of which the scope of before the instruction holds at the
state `t` after its regions, where the domain's state before the instruction and the region's exit
state mean the table, and the region's returned identifiers read the values; the results are new
leaves at the counter, the domain's `after` is told of the region's exit (asking nobody), then
`leaves` of the results' types. -/
theorem Returned.atResults {Γ : Ctx D.Ty} {mid : List D.Ty} {ρ ρ₂ : Leaves σ.sem.Dyn}
    {ids : Ctx Ident} {env : Env σ.sem.Val Γ} {t : State Raw} {before known : σ.cfg.domain.State}
    {exits : List (Asks × σ.cfg.domain.State × List Ident)} {returned : List Ident}
    {values : HList σ.sem.Val mid} (le : ρ.Le ρ₂) (scope : Scope σ.sem σ.Runs σ.R ρ₂ ids env t)
    (valid : ∀ n v, ρ₂ n = some v → σ.Valid v)
    (beforeMeans : σ.domain.Means before t.values.table ρ₂)
    (member : (Asks.nobody, known, returned) ∈ exits)
    (knownMeans : σ.domain.Means known t.values.table ρ₂)
    (reads : ReadsAll σ.Runs σ.R.bool t.values.table ρ₂ returned (σ.sem.dyns values)) :
    Returned σ ρ ids env
      (σ.cfg.domain.leaves
        (σ.cfg.domain.after t.values.table before exits (Ident.leaves t.leaves mid.length))
        ((Ident.leaves t.leaves mid.length).zip mid))
      { t with leaves := t.leaves + mid.length } (Ident.leaves t.leaves mid.length) values := by
  obtain ⟨le', fresh, made⟩ := Leaves.results (Run := σ.Runs) (R := σ.R)
    (table := t.values.table) scope.fresh values
  have valuesValid := ReadsAll.valid valid reads
  have afterMeans := σ.domain.after scope.wf.slots (σ.domain.mono (Table.Le.refl _) le' beforeMeans) member
    (σ.domain.mono (Table.Le.refl _) le' knownMeans) (Asks.nobody_sound _ _ _ _)
    ⟨σ.sem.dyns values, ReadsAll.mono (Table.Le.refl _) le' reads, made⟩
  have leavesMeans := σ.domain.leaves scope.wf.slots afterMeans (ReadsAll.zip_typed values made valuesValid)
  exact ⟨_, fun n v h => le' n v (le n v h),
    ⟨⟨fresh, fun τ x => by
        obtain ⟨id, found, read⟩ := scope.agree τ x
        exact ⟨id, found, Reads.mono (Table.Le.refl _) le' read⟩, scope.bound, scope.wf⟩,
      Leaves.setFrom_valid valid valuesValid, leavesMeans⟩, made⟩

end

/-! ## What an operation does, from the state after its annotations -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw]

/-- **What an operation does grows the state**: by no leaf when it is shared, by its results
otherwise. -/
theorem opStep_grew (cfg : Config D Raw) (addresses : List (List (Key × Nat) × Key)) (place : Place)
    {ins res : List D.Ty} (o : D.Op ins res) (args : List Ident) (t : State Raw)
    (known : cfg.domain.State) (wf : t.values.WF) :
    Grew cfg addresses t (opStep cfg place o args t known).state
      (if cfg.rules.shared o = true then 0 else res.length) := by
  have decided := decideClauses_entered cfg place (.requirement (cfg.rules.written o))
    (args.map some) (cfg.rules.contract (cfg.rules.written o)).preconditions 0 t known wf
  cases shared : cfg.rules.shared o with
  | true =>
      simp only [opStep, decideRequirements_eq, learnGuarantees_eq, shared, ↓reduceIte]
      generalize decideClauses cfg place (.requirement (cfg.rules.written o)) (args.map some) 0
        (cfg.rules.contract (cfg.rules.written o)).preconditions t known = dec at decided ⊢
      obtain ⟨u, uk⟩ := dec
      dsimp only at *
      have mid := State.Entered.values (s := u) (Values.apply_grew cfg.rules.commutes
        (cfg.rules.written o) args res.length decided.wf)
      let applied := cfg.apply (cfg.rules.written o) args res.length u.values uk
      have learned := learnAll_entered cfg ((args ++ applied.1).map some)
        (cfg.rules.contract (cfg.rules.written o)).ensures _
        (cfg.resultFacts o applied.2.1.table applied.2.2 args applied.1) mid.wf
      exact Grew.of_entered cfg _ (decided.trans (mid.trans learned))
  | false =>
      simp only [opStep, decideRequirements_eq, learnGuarantees_eq, shared, Bool.false_eq_true, ↓reduceIte]
      generalize decideClauses cfg place (.requirement (cfg.rules.written o)) (args.map some) 0
        (cfg.rules.contract (cfg.rules.written o)).preconditions t known = dec at decided ⊢
      obtain ⟨u, uk⟩ := dec
      dsimp only at *
      have learned := learnAll_entered cfg ((args ++ Ident.leaves u.leaves res.length).map some)
        (cfg.rules.contract (cfg.rules.written o)).ensures { u with leaves := u.leaves + res.length }
        (cfg.resultFacts o u.values.table uk args (Ident.leaves u.leaves res.length)) decided.wf
      exact Grew.of_entered_leaves cfg _ res.length decided learned

/-- **An operation grows the state**: by no leaf when it is shared, by its results otherwise. -/
theorem opGrows (cfg : Config D Raw) (notes : Annotations Raw) : OpGrowsStatement cfg notes := by
  intro cursor key Γ ins res o operands ids s k wf
  show Grew cfg _ s (opStep cfg (cfg.place cursor.blocks key) o (idsOf ids operands)
    (atEntry cfg notes (.instruction cursor key) ids s k).1 (atEntry cfg notes (.instruction cursor key) ids s k).2).state _
  have entry := atEntry_entered cfg notes (.instruction cursor key) ids s k wf
  have grew := opStep_grew cfg (Instr.addresses cursor.blocks key (.op o operands))
    (cfg.place cursor.blocks key) o (idsOf ids operands) _ (atEntry cfg notes (.instruction cursor key) ids s k).2 entry.wf
  obtain ⟨⟨table, wf', next⟩, leaves, bounds, new, refusals⟩ := entry
  obtain ⟨table', wf'', next', leaves', ⟨new', refusals'⟩, newBounds, bounds', added⟩ := grew
  refine ⟨table.trans table', wf'', Nat.le_trans next next', ?_, ⟨new' ++ new, ?_⟩, newBounds, ?_,
    added⟩
  · show _ = _ + (if cfg.rules.shared o = true then 0 else res.length)
    rw [leaves', leaves]
  · rw [refusals', refusals, List.append_assoc]
  · rw [bounds', bounds]

omit [DecidableEq Raw] in
/-- The refusals of a walk that adds nothing in all, after annotations that add refusals: the
annotations add none, and nor does what follows them. -/
theorem refusals_split {s t u : State Raw} (first : ∃ new, t.refusals = new ++ s.refusals)
    (second : ∃ new, u.refusals = new ++ t.refusals) (unchanged : u.refusals = s.refusals) :
    t.refusals = s.refusals ∧ u.refusals = t.refusals := by
  obtain ⟨new₁, r₁⟩ := first
  obtain ⟨new₂, r₂⟩ := second
  exact ⟨refusals_first r₁ r₂ unchanged, refusals_second r₁ r₂ unchanged⟩

end

/-! ## Soundness -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw) (laws : σ.Lawful)

omit [DecidableEq Raw] in
include laws in
private theorem resultFacts_sound {ins res} (o : D.Op ins res) {table : Table Raw}
    {ρ : Leaves σ.sem.Dyn} {k : σ.cfg.domain.State} {args made : List Ident}
    {values : HList σ.sem.Val ins} {results : HList σ.sem.Val res} {key path}
    (slots : table.WF) (means : σ.domain.Means k table ρ)
    (src : ReadsAll σ.Runs σ.R.bool table ρ args (σ.sem.dyns values))
    (dst : ReadsAll σ.Runs σ.R.bool table ρ made (σ.sem.dyns results))
    (valid : ∀ v ∈ σ.sem.dyns results, σ.Valid v)
    (ran : (σ.sem.op key o path values).CanReturn σ.permitted results) :
    σ.domain.Means (σ.cfg.resultFacts o table k args made) table ρ := by
  have typed := σ.domain.leaves slots means (ReadsAll.zip_typed results dst valid)
  unfold Config.resultFacts
  split
  · exact typed
  · rename_i i observed
    split
    · rename_i source result atSource atResult
      obtain ⟨x, hx, rx⟩ := src.get atSource
      obtain ⟨y, hy, ry⟩ := dst.get atResult
      exact σ.domain.observe slots (Asks.nobody_sound ..) typed rx ry
        (laws.rules.observedOperand o observed ran hx hy)
    · exact typed

include laws in
/-- **What an operation does is sound**, from the state after its annotations: when it refuses
nothing, its requirements hold, and what it runs returns, on every permitted path, what
`Returned` says and never stops `undefined`. -/
theorem opStep_sound {Γ : Ctx D.Ty} {ins res : List D.Ty} (o : D.Op ins res) (place : Place)
    (key : Key) (path : List Frame) {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident}
    {env : Env σ.sem.Val Γ} {t : State Raw} {known : σ.cfg.domain.State} {args : List Ident}
    {values : HList σ.sem.Val ins} (inv : Inv σ ρ ids env known t)
    (reads : ReadsAll σ.Runs σ.R.bool t.values.table ρ args (σ.sem.dyns values))
    (unchanged : (opStep σ.cfg place o args t known).state.refusals = t.refusals) :
    σ.cfg.rules.Required σ.sem σ.R σ.Run σ.Valid o values ∧
      (σ.sem.op key o path values).Every σ.permitted
        (Returned σ ρ ids env (opStep σ.cfg place o args t known).known
          (opStep σ.cfg place o args t known).state (opStep σ.cfg place o args t known).returned)
        (fun stop => ¬ σ.undefined stop) := by
  have valid := ReadsAll.valid inv.valid reads
  have defined := fun a m => laws.requires o a m values valid
  have decided := decideClauses_entered σ.cfg place (.requirement (σ.cfg.rules.written o))
    (args.map some) (σ.cfg.rules.contract (σ.cfg.rules.written o)).preconditions 0 t known inv.wf
  have decidedSound := fun unchanged =>
    decideClauses_sound σ laws.rules place (.requirement (σ.cfg.rules.written o))
      (σ.cfg.rules.contract (σ.cfg.rules.written o)).preconditions 0 t known inv.means inv.wf
      (PositionsRead.of_readsAll reads) defined unchanged
  revert unchanged
  cases shared : σ.cfg.rules.shared o with
  | true =>
      simp only [opStep, decideRequirements_eq, learnGuarantees_eq, shared, ↓reduceIte]
      generalize decideClauses σ.cfg place (.requirement (σ.cfg.rules.written o)) (args.map some) 0
        (σ.cfg.rules.contract (σ.cfg.rules.written o)).preconditions t known = dec
        at decided decidedSound ⊢
      obtain ⟨u, uk⟩ := dec
      dsimp only at *
      intro unchanged
      have mid := State.Entered.values (s := u) (Values.apply_grew σ.cfg.rules.commutes
        (σ.cfg.rules.written o) args res.length decided.wf)
      let applied := σ.cfg.apply (σ.cfg.rules.written o) args res.length u.values uk
      have learned := learnAll_entered σ.cfg ((args ++ applied.1).map some)
        (σ.cfg.rules.contract (σ.cfg.rules.written o)).ensures _
        (σ.cfg.resultFacts o applied.2.1.table applied.2.2 args applied.1) mid.wf
      obtain ⟨first, -⟩ := State.Entered.unchanged decided (mid.trans learned) unchanged
      obtain ⟨uMeans, required⟩ := decidedSound first
      refine ⟨required, ?_⟩
      obtain ⟨results, done, ran, ensured⟩ :=
        laws.rules.defined o shared key path values valid required
      have resultsValid := (laws.rules.keeps _ _ _ ran valid).1
      obtain ⟨appliedMeans, appliedReads⟩ := Config.apply_sound σ laws.rules (k := uk) decided.wf uMeans
        (ReadsAll.mono decided.1.1 (fun _ _ h => h) reads) ⟨ran, valid, resultsValid⟩
        (σ.sem.dyns_length results)
      have inputReads := ReadsAll.mono (decided.1.1.trans mid.1.1) (fun _ _ h => h) reads
      have leavesMeans := resultFacts_sound σ laws o mid.wf.slots appliedMeans inputReads
        appliedReads resultsValid (done ▸ Process.CanReturn.done results)
      have learnedMeans := learnAll_sound σ laws.rules (σ.cfg.rules.contract (σ.cfg.rules.written o)).ensures _ _
        leavesMeans mid.wf
        (PositionsRead.of_readsAll (ReadsAll.append inputReads appliedReads))
        ensured
      rw [done]
      exact ⟨ρ, fun _ _ h => h, inv.entered (decided.trans (mid.trans learned)) learnedMeans,
        ReadsAll.mono learned.1.1 (fun _ _ h => h) appliedReads⟩
  | false =>
      simp only [opStep, decideRequirements_eq, learnGuarantees_eq, shared, Bool.false_eq_true, ↓reduceIte]
      generalize decideClauses σ.cfg place (.requirement (σ.cfg.rules.written o)) (args.map some) 0
        (σ.cfg.rules.contract (σ.cfg.rules.written o)).preconditions t known = dec
        at decided decidedSound ⊢
      obtain ⟨u, uk⟩ := dec
      dsimp only at *
      intro unchanged
      have learned := learnAll_entered σ.cfg ((args ++ Ident.leaves u.leaves res.length).map some)
        (σ.cfg.rules.contract (σ.cfg.rules.written o)).ensures
        { u with leaves := u.leaves + res.length }
        (σ.cfg.resultFacts o u.values.table uk args (Ident.leaves u.leaves res.length)) decided.wf
      obtain ⟨first, -⟩ := refusals_split decided.2.2.2 learned.2.2.2 unchanged
      obtain ⟨uMeans, required⟩ := decidedSound first
      refine ⟨required, ?_⟩
      refine Process.every_mono _ _ (fun results holds => ?_) (fun _ h => h.1)
        (Process.every_and _ _ (laws.rules.effect o shared key path values valid required)
          (Process.every_canReturn _))
      obtain ⟨⟨resultsValid, ensured⟩, ran⟩ := holds
      have fresh : ∀ n, u.leaves ≤ n → ρ n = none := fun n above =>
        inv.fresh n (by rw [← decided.2.1]; exact above)
      obtain ⟨le, freshOut, leafReads⟩ := Leaves.results (Run := σ.Runs) (R := σ.R)
        (table := u.values.table) fresh results
      have inputReads := ReadsAll.mono decided.1.1 le reads
      have leavesMeans := resultFacts_sound σ laws o decided.wf.slots
        (σ.domain.mono (Table.Le.refl _) le uMeans) inputReads leafReads resultsValid ran
      have learnedMeans := learnAll_sound σ laws.rules (σ.cfg.rules.contract (σ.cfg.rules.written o)).ensures
        { u with leaves := u.leaves + res.length } _ leavesMeans decided.wf
        (PositionsRead.of_readsAll (ReadsAll.append inputReads leafReads))
        ensured
      refine ⟨ρ.setFrom u.leaves (σ.sem.dyns results), le, ⟨⟨fun n above => ?_, fun τ x => ?_,
        inv.bound, learned.wf⟩, Leaves.setFrom_valid inv.valid resultsValid, learnedMeans⟩,
        ReadsAll.mono learned.1.1 (fun _ _ h => h) leafReads⟩
      · rw [learned.2.1] at above
        exact freshOut n above
      · obtain ⟨id, found, read⟩ := inv.agree τ x
        exact ⟨id, found, Reads.mono (decided.1.1.trans learned.1.1) le read⟩

include laws in
/-- **An operation is sound**: from the invariant, with the annotations at its entry, when the walk
refuses nothing, its requirements hold and what it returns, shared or kept in order, is what
`Returned` says. -/
theorem opSound : OpSoundStatement σ := by
  intro _ cursor key Γ ins res o operands path ρ ids env s k
  dsimp only
  intro inv steps _ facts _ unchanged
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k inv.wf
  have entryInv := fun unchanged =>
    atEntry_inv σ laws cursor key (.op o operands) (path := path) inv steps facts unchanged
  simp only [walkInstr] at unchanged ⊢
  simp only [Instr.site] at entryInv
  generalize atEntry σ.cfg σ.notes (.instruction cursor key) ids s k = entered at entry entryInv unchanged ⊢
  obtain ⟨t, known⟩ := entered
  have grew := opStep_grew σ.cfg [] (σ.cfg.place cursor.blocks key) o (idsOf ids operands) t known entry.wf
  obtain ⟨first, second⟩ := refusals_split entry.2.2.2 grew.2.2.2.2.1 unchanged
  have inv₁ := entryInv first
  obtain ⟨required, every⟩ := opStep_sound σ laws o (σ.cfg.place cursor.blocks key) key path inv₁
    (inv₁.toScope.idsOf_reads operands) second
  exact ⟨every, required, trivial, fun _ _ _ => trivial⟩

end

/-! ## Running the skeleton -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

/-- **What an operation does runs its entry of the skeleton**, from the state after its
annotations: a shared one returns what its written operation gives, or stops `undefined`; one
kept in order is its entry, and what follows runs from every result on its result leaves. -/
theorem opStep_runs (laws : σ.ValueLaws) {ins res : List D.Ty} (o : D.Op ins res) (place : Place)
    (key : Key) (path : List Frame) {ρ : Leaves σ.sem.Dyn} {t : State Raw}
    {known : σ.cfg.domain.State} {args : List Ident} {values : HList σ.sem.Val ins}
    {table : Table Raw} {mid₀ outs : List D.Ty} {rest : Skel D mid₀} {after : Rests D mid₀ outs}
    {cont : HList σ.sem.Val res → Process σ.sem.S σ.sem.H (HList σ.sem.Val outs)}
    (fresh : ∀ n, t.leaves ≤ n → ρ n = none) (wf : t.values.WF)
    (reads : ReadsAll σ.Run σ.R.bool t.values.table ρ args (σ.sem.dyns values))
    (sub : (opStep σ.cfg place o args t known).state.values.table.Le table)
    (notUndefined : σ.NotUndefined ((σ.sem.op key o path values).bind cont))
    (next : ∀ ρ' results, ρ.Le ρ' →
      (∀ n, (opStep σ.cfg place o args t known).state.leaves ≤ n → ρ' n = none) →
      ReadsAll σ.Run σ.R.bool (opStep σ.cfg place o args t known).state.values.table ρ'
        (opStep σ.cfg place o args t known).returned (σ.sem.dyns results) →
      σ.NotUndefined (cont results) →
      Skel.Runs σ.sem σ.permitted σ.Run σ.R table path ρ' rest after (cont results)) :
    Skel.Runs σ.sem σ.permitted σ.Run σ.R table path ρ
      (Skel.stepOf key (opStep σ.cfg place o args t known).entry rest) after
      ((σ.sem.op key o path values).bind cont) := by
  have decided := decideClauses_entered σ.cfg place (.requirement (σ.cfg.rules.written o))
    (args.map some) (σ.cfg.rules.contract (σ.cfg.rules.written o)).preconditions 0 t known wf
  revert sub next
  cases shared : σ.cfg.rules.shared o with
  | true =>
      simp only [opStep, decideRequirements_eq, learnGuarantees_eq, shared, ↓reduceIte]
      generalize decideClauses σ.cfg place (.requirement (σ.cfg.rules.written o)) (args.map some) 0
        (σ.cfg.rules.contract (σ.cfg.rules.written o)).preconditions t known = dec at decided ⊢
      obtain ⟨u, uk⟩ := dec
      dsimp only at *
      have mid := State.Entered.values (s := u) (Values.apply_grew σ.cfg.rules.commutes
        (σ.cfg.rules.written o) args res.length decided.wf)
      let applied := σ.cfg.apply (σ.cfg.rules.written o) args res.length u.values uk
      have learned := learnAll_entered σ.cfg ((args ++ applied.1).map some)
        (σ.cfg.rules.contract (σ.cfg.rules.written o)).ensures _
        (σ.cfg.resultFacts o applied.2.1.table applied.2.2 args applied.1) mid.wf
      intro _ next
      rcases laws.1.computes o shared key path values with ⟨results, done, ran⟩ | ⟨stop, halted, undefined⟩
      · rw [done] at notUndefined ⊢
        have applied := Values.apply_reads σ.cfg.rules.commutes
          (fun commutes a b results ran => laws.1.commutative _ commutes a b results ran)
          (ReadsAll.mono decided.1.1 (fun _ _ h => h) reads) ran (σ.sem.dyns_length results)
        exact next ρ results (fun _ _ h => h)
          (fun n above => fresh n (Nat.le_trans (Nat.le_of_eq decided.2.1.symm)
            (Nat.le_trans (Nat.le_of_eq learned.2.1.symm) above)))
          (ReadsAll.mono learned.1.1 (fun _ _ h => h) applied) notUndefined
      · rw [halted] at notUndefined
        exact absurd undefined notUndefined
  | false =>
      simp only [opStep, decideRequirements_eq, learnGuarantees_eq, shared, Bool.false_eq_true, ↓reduceIte]
      generalize decideClauses σ.cfg place (.requirement (σ.cfg.rules.written o)) (args.map some) 0
        (σ.cfg.rules.contract (σ.cfg.rules.written o)).preconditions t known = dec at decided ⊢
      obtain ⟨u, uk⟩ := dec
      dsimp only at *
      have learned := learnAll_entered σ.cfg ((args ++ Ident.leaves u.leaves res.length).map some)
        (σ.cfg.rules.contract (σ.cfg.rules.written o)).ensures
        { u with leaves := u.leaves + res.length }
        (σ.cfg.resultFacts o u.values.table uk args (Ident.leaves u.leaves res.length)) decided.wf
      intro sub next
      have fresh' : ∀ n, u.leaves ≤ n → ρ n = none := fun n above =>
        fresh n (by rw [← decided.2.1]; exact above)
      refine Skel.Runs.effect values
        (ReadsAll.mono ((decided.1.1.trans learned.1.1).trans sub) (fun _ _ h => h) reads)
        fun returned returns => ?_
      refine next _ returned (Leaves.le_setFrom fresh' _) (fun n above => ?_) ?_
        (Process.Every.of_bind_canReturn notUndefined returns)
      · refine Leaves.setFrom_fresh fresh' _ n ?_
        rw [σ.sem.dyns_length]
        rw [learned.2.1] at above
        exact above
      · exact (Leaves.results (Run := σ.Run) (R := σ.R) fresh' returned).2.2

/-- **An operation runs its entry of the skeleton.** -/
theorem opRuns : OpRunsStatement σ := by
  intro laws cursor key Γ ins res o operands path ρ ids env s k table mid₀ outs rest after cont
  dsimp only
  intro scope sub notUndefined next
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k scope.wf
  have reads := scope.idsOf_reads operands
  exact opStep_runs σ laws o (σ.cfg.place cursor.blocks key) key path
    (fun n above => scope.fresh n (by rw [← entry.2.1]; exact above)) entry.wf
    (ReadsAll.mono entry.1.1 (fun _ _ h => h) reads) sub notUndefined next

end

end Zkc.Core.BodyAnalysis
