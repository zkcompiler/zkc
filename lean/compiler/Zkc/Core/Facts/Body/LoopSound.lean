module

public import Zkc.Core.Facts.Body.StepSound
public import Zkc.Core.Facts.Body.InvariantsSound
public import Zkc.Core.Meaning.ValidValues

@[expose] public section

/-!
The three properties of a loop from those of its body: `LoopGrowsStatement`, `LoopRunsStatement`,
`LoopSoundStatement`.

The walk of a loop decides its invariant on the initial values, makes the leaves of the index and
the carried values, tells the domain `enter`, learns the invariant there, walks the body once,
decides the invariant on the index's successor and what the body returns, records the bound of
the loop, makes the leaves of its results, tells the domain `afterLoop` and `leaves`, and learns
the invariant on the constructed final index and the carried results. Its soundness is an induction over the
iterations, about the program's values: at each iteration that a run reaches, the invariant holds
of the carried values, so the body's entry state means the leaves of the iteration; and the
carried values of every iteration of a run are what the domain's law `afterLoop` is given.
-/

namespace Zkc.Core.BodyAnalysis

/-! ## The parts of the walk of a loop -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw)

omit [DecidableEq Raw] in
/-- The index of a loop as the domain is told of it is its leaf. -/
theorem Loop.told_index (rules : Rules D Raw) (carried : List D.Ty) {w : D.Who} (count : Count D w)
    (initial : List Ident) (index : Nat) :
    (Loop.told rules carried count initial index).index = .leaf index :=
  rfl

omit [DecidableEq Raw] in
/-- The carried values of a loop as the domain is told of it are the leaves after its index. -/
theorem Loop.told_carried (rules : Rules D Raw) (carried : List D.Ty) {w : D.Who}
    (count : Count D w) (initial : List Ident) (index : Nat) :
    (Loop.told rules carried count initial index).carried =
      Ident.leaves (index + 1) carried.length :=
  rfl

/-- The walk of a loop before its body, with its parts named: the index's first value, the
invariant decided on the initial values, and the invariant learned at the body's entry. -/
theorem loopEnter_eq (notes : Annotations Raw) (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty}
    (carried : List D.Ty) (w : D.Who) (times : Times D w Γ) (initial : List Ident)
    (ids : Ctx Ident) (s : State Raw) (k : cfg.domain.State) :
    ∃ first decided learned,
      first = indexValue cfg (cfg.rules.indexAt w 0) [] s k ∧
      decided = decideInvariants cfg (.instruction cursor key) false ids first.1 initial (notes.invariantsAt (.instruction cursor key))
        first.2.1 first.2.2 ∧
      learned = learnInvariants cfg ids (some (.leaf decided.1.leaves))
        (Ident.leaves (decided.1.leaves + 1) carried.length) (notes.invariantsAt (.instruction cursor key))
        { decided.1 with leaves := decided.1.leaves + (carried.length + 1) }
        (cfg.domain.enter Asks.nobody decided.1.values.table decided.2
          (Loop.told cfg.rules carried (countOf ids times) initial decided.1.leaves)) ∧
      loopEnter cfg notes cursor key carried w times initial ids s k =
        ⟨decided.1, decided.2, Loop.told cfg.rules carried (countOf ids times) initial
          decided.1.leaves, learned.1, learned.2⟩ :=
  ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-- Expose the post-loop domain and the final typed index before learning exit invariants. -/
theorem loopExit_eq (notes : Annotations Raw) (cursor : StaticCursor) (key : Key) {Γ : Ctx D.Ty}
    (carried each : List D.Ty) (w : D.Who) (times : Times D w Γ) (initial : List Ident)
    (ids : Ctx Ident) (entry : LoopEntry D Raw cfg.domain.State)
    (body : Exit D Raw cfg.domain.State (carried ++ each)) :
    ∃ next kept recorded final learned,
        next = indexValue cfg (cfg.rules.indexNext w) [entry.loop.index] body.state body.known ∧
        kept = decideInvariants cfg (.instruction cursor key) true ids next.1 (body.returned.take carried.length)
          (notes.invariantsAt (.instruction cursor key)) next.2.1 next.2.2 ∧
        recorded = recordBound (cfg.place cursor.blocks key) (cfg.domain.answers entry.before) (countOf ids times)
          (discount cfg entry.known entry.body kept.1) ∧
        final = (countOf ids times).finalIndex cfg
          { recorded with leaves := recorded.leaves + (carried.length + each.length) }
          (cfg.domain.leaves
            (cfg.domain.afterLoop Asks.nobody Asks.nobody recorded.values.table entry.before
              entry.loop body.known (body.returned.take carried.length)
              ((Ident.leaves recorded.leaves (carried.length + each.length)).take carried.length))
            ((Ident.leaves recorded.leaves (carried.length + each.length)).zip
              (carried ++ each.map (D.collected times.size)))) ∧
        learned = learnInvariants cfg ids final.1
          ((Ident.leaves recorded.leaves (carried.length + each.length)).take carried.length)
          (notes.invariantsAt (.instruction cursor key)) final.2.1 final.2.2 ∧
        loopExit cfg notes cursor key carried each w times initial ids entry body =
          ⟨learned.1, learned.2, Ident.leaves recorded.leaves (carried.length + each.length),
            some (.loop w (countOf ids times) initial entry.decided.leaves body.skel
              recorded.leaves)⟩ :=
  ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Constructing a final index enters only table values, preserving the leaf environment. -/
theorem Count.finalIndex_entered {w : D.Who} (count : Count D w) (s : State Raw)
    (k : cfg.domain.State) (wf : s.values.WF) :
    State.Entered s (count.finalIndex cfg s k).2.1 := by
  cases count <;> exact indexValue_entered cfg _ _ s k wf

end

/-! ## A loop grows the state -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw) (notes : Annotations Raw)

/-- **A loop grows the state when its body does**: by the leaves of its index and carried values,
of its body and of its results, adding its own bound and those of its body. -/
theorem loopGrows : LoopGrowsStatement cfg notes := by
  intro cursor key Γ carried each w times gives initial inputs body growsBody ids s k wf
  have entry := atEntry_entered cfg notes (.instruction cursor key) ids s k wf
  simp only [walkInstr, Instr.leafCount]
  generalize atEntry cfg notes (.instruction cursor key) ids s k = e at entry
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry ⊢
  obtain ⟨first, decided, learned, hfirst, hdecided, hlearned, henter⟩ :=
    loopEnter_eq cfg notes cursor key carried w times (idsOf ids initial) ids E Ek
  rw [henter]
  simp only [Loop.told_index, Loop.told_carried]
  have firstE : State.Entered E first.2.1 := by
    rw [hfirst]; exact indexValue_entered cfg _ [] E Ek entry.wf
  have decidedE : State.Entered first.2.1 decided.1 := by
    rw [hdecided]; exact decideInvariants_entered cfg _ false ids _ _ _ _ _ firstE.wf
  have learnedE : State.Entered { decided.1 with leaves := decided.1.leaves + (carried.length + 1) }
      learned.1 := by
    rw [hlearned]; exact learnInvariants_entered cfg ids _ _ _ _ _ decidedE.wf
  have bodyGrew := growsBody
    (bindIds ids inputs
      (.leaf decided.1.leaves :: Ident.leaves (decided.1.leaves + 1) carried.length))
    learned.1 learned.2 learnedE.wf
  generalize walk cfg notes (cursor.region key) body _ learned.1 learned.2 = inner at bodyGrew ⊢
  obtain ⟨next, kept, recorded, finalIndex, learnedF, hnext, hkept, hrecorded, hfinalIndex, hlearnedF, hexit⟩ :=
    loopExit_eq cfg notes cursor key carried each w times (idsOf ids initial) ids
      _ inner
  rw [hexit]
  dsimp only at hnext hkept hrecorded hfinalIndex hlearnedF ⊢
  have nextE : State.Entered inner.state next.2.1 := by
    rw [hnext]; exact indexValue_entered cfg _ _ _ _ bodyGrew.2.1
  have keptE : State.Entered next.2.1 kept.1 := by
    rw [hkept]; exact decideInvariants_entered cfg _ true ids _ _ _ _ _ nextE.wf
  have toKept := bodyGrew.trans (Grew.of_entered cfg _ (nextE.trans keptE))
  have ended := Grew.discount learned.2 toKept
  have recordedG : Grew cfg ((cursor.blocks, key) :: Term.addresses cursor.blocks body)
      (discount cfg learned.2 learned.1 kept.1) recorded 0 := by
    rw [hrecorded]
    exact Grew.recordBound cfg cursor.blocks key _ _ ended.2.1 List.mem_cons_self
  have finalEntered : State.Entered
      { recorded with leaves := recorded.leaves + (carried.length + each.length) } finalIndex.2.1 := by
    rw [hfinalIndex]
    exact Count.finalIndex_entered cfg _ _ _ recordedG.2.1
  have learnedFE : State.Entered
      { recorded with leaves := recorded.leaves + (carried.length + each.length) } learnedF.1 := by
    rw [hlearnedF]
    exact finalEntered.trans (learnInvariants_entered cfg ids _ _ _ _ _ finalEntered.wf)
  have lastG := Grew.of_entered_leaves cfg ((cursor.blocks, key) :: Term.addresses cursor.blocks body)
    (carried.length + each.length) (State.Entered.refl recordedG.2.1) learnedFE
  have total := ((((Grew.of_entered cfg ((cursor.blocks, key) :: Term.addresses cursor.blocks body)
    entry).trans (Grew.of_entered_leaves cfg _ (carried.length + 1) (firstE.trans decidedE)
      learnedE)).trans (ended.widen fun _ m => List.mem_cons_of_mem _ m)).trans recordedG).trans
    lastG
  refine total.count ?_
  simp only [Nat.zero_add, Nat.add_zero]

end

/-! ## A loop runs its entry -/

section
variable {D : Dialect} {Raw : Type}

/-- What a loop gives, with its values, is the same whether the size of what it collects is the
skeleton's count's or the loop's. -/
theorem dyns_collected_countOf (sem : Semantics D) {w : D.Who} {Γ : Ctx D.Ty}
    {carried each : List D.Ty} (ids : Ctx Ident) (times : Times D w Γ)
    (final : sem.LoopState carried each) :
    sem.dyns (final.1.append (sem.collected (countOf ids times).size final.2)) =
      sem.dyns (final.1.append (sem.collected times.size final.2)) := by
  cases times <;> rfl

/-- The count of a loop, on the identifier of its count, says how often the loop runs. -/
theorem Scope.countOf_is {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn} {Γ : Ctx D.Ty} {ρ : Leaves sem.Dyn} {ids : Ctx Ident}
    {env : Env sem.Val Γ} {s : State Raw} (scope : Scope sem Run R ρ ids env s) {w : D.Who}
    (times : Times D w Γ) :
    (countOf ids times).Is sem Run R s.values.table ρ (sem.times times env) := by
  cases times with
  | fixed n => rfl
  | value c ok => exact ⟨env.get c, scope.idOf_reads c, rfl⟩

/-- The leaves of an iteration read the index and the carried values on the index's leaf and the
carried leaves after it. -/
theorem ReadsAll.iteration {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {truth : sem.Dyn → Option Bool} (table : Table Raw) (ρ : Leaves sem.Dyn) (lo : Nat)
    {w : D.Who} {carried : List D.Ty} (i : Nat) (values : HList sem.Val carried) :
    ReadsAll Run truth table (ρ.setFrom lo (sem.dyns (HList.cons (sem.index w i) values)))
      (.leaf lo :: Ident.leaves (lo + 1) carried.length)
      (sem.dyns (HList.cons (sem.index w i) values)) := by
  have set := ReadsAll.setFrom (Run := Run) (truth := truth) (table := table) ρ lo
    (sem.dyns (HList.cons (sem.index w i) values))
  rw [sem.dyns_length] at set
  exact set

/-- The scope of the names before a loop at the entry of an iteration: over a grown table and the
leaves of the iteration. -/
theorem Scope.iterationOuter {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn} {Γ : Ctx D.Ty} {ρ : Leaves sem.Dyn} {ids : Ctx Ident}
    {env : Env sem.Val Γ} {s t : State Raw} (scope : Scope sem Run R ρ ids env s)
    (grew : Values.Grew s.values t.values) {w : D.Who} {carried : List D.Ty}
    (leaves : t.leaves = s.leaves + (carried.length + 1)) (i : Nat)
    (values : HList sem.Val carried) :
    Scope sem Run R (ρ.setFrom s.leaves (sem.dyns (HList.cons (sem.index w i) values))) ids env
      t := by
  have le := Leaves.le_setFrom scope.fresh (sem.dyns (HList.cons (sem.index w i) values))
  refine ⟨fun n above => ?_, fun τ x => ?_, scope.bound, grew.2.1⟩
  · refine Leaves.setFrom_fresh scope.fresh _ n ?_
    rw [sem.dyns_length]
    rw [leaves] at above
    exact above
  · obtain ⟨id, found, read⟩ := scope.agree τ x
    exact ⟨id, found, Reads.mono grew.1 le read⟩

/-- The scope at the entry of an iteration: the names in scope before the loop read their values
over a grown table and more leaves, and the names of the body's inputs read the index and the
carried values on their leaves. -/
theorem Scope.iteration {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn} {Γ : Ctx D.Ty} {ρ : Leaves sem.Dyn} {ids : Ctx Ident}
    {env : Env sem.Val Γ} {s t : State Raw} (scope : Scope sem Run R ρ ids env s)
    (grew : Values.Grew s.values t.values) {w : D.Who} {carried : List D.Ty}
    (leaves : t.leaves = s.leaves + (carried.length + 1)) (inputs : Names (D.index w :: carried))
    (i : Nat) (values : HList sem.Val carried) :
    Scope sem Run R (ρ.setFrom s.leaves (sem.dyns (HList.cons (sem.index w i) values)))
      (bindIds ids inputs (.leaf s.leaves :: Ident.leaves (s.leaves + 1) carried.length))
      (env.extend inputs (.cons (sem.index w i) values)) t :=
  (scope.iterationOuter grew leaves i values).bind inputs _ (HList.cons (sem.index w i) values)
    (ReadsAll.iteration t.values.table ρ s.leaves i values)

variable [DecidableEq Raw] (σ : Setting D Raw)

/-- **A loop runs its entry of the skeleton when its body runs its skeleton**: the body runs alone
at every iteration that is reached, from the leaves before the loop with the index and the carried
values on its input leaves; what follows runs from every final state on the loop's result
leaves. -/
theorem loopRuns : LoopRunsStatement σ := by
  intro laws cursor key Γ carried each w times gives initial inputs body growsBody runsBody
  intro path ρ ids env s k table mid₀ outs rest after cont
  dsimp only
  intro scope sub notUndefined next
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k scope.wf
  rw [Instr.denote_loop, Process.bind_assoc] at notUndefined ⊢
  simp only [walkInstr] at sub next ⊢
  revert sub next
  generalize atEntry σ.cfg σ.notes (.instruction cursor key) ids s k = e at entry
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry ⊢
  obtain ⟨first, decided, learned, hfirst, hdecided, hlearned, henter⟩ :=
    loopEnter_eq σ.cfg σ.notes cursor key carried w times (idsOf ids initial)
      ids E Ek
  rw [henter]
  simp only [Loop.told_index, Loop.told_carried]
  have firstE : State.Entered E first.2.1 := by
    rw [hfirst]; exact indexValue_entered σ.cfg _ [] E Ek entry.wf
  have decidedE : State.Entered first.2.1 decided.1 := by
    rw [hdecided]; exact decideInvariants_entered σ.cfg _ false ids _ _ _ _ _ firstE.wf
  have learnedE : State.Entered { decided.1 with leaves := decided.1.leaves + (carried.length + 1) }
      learned.1 := by
    rw [hlearned]; exact learnInvariants_entered σ.cfg ids _ _ _ _ _ decidedE.wf
  have toDecided := entry.trans (firstE.trans decidedE)
  have bodyGrew := growsBody
    (bindIds ids inputs
      (.leaf decided.1.leaves :: Ident.leaves (decided.1.leaves + 1) carried.length))
    learned.1 learned.2 learnedE.wf
  have runsOne := fun path' ρ' env' => runsBody path' ρ'
    (bindIds ids inputs
      (.leaf decided.1.leaves :: Ident.leaves (decided.1.leaves + 1) carried.length))
    env' learned.1 learned.2 table .nil (fun values => Process.done values)
  generalize walk σ.cfg σ.notes (cursor.region key) body _ learned.1 learned.2 = inner at bodyGrew runsOne ⊢
  obtain ⟨next', kept, recorded, finalIndex, learnedF, hnext, hkept, hrecorded, hfinalIndex, hlearnedF, hexit⟩ :=
    loopExit_eq σ.cfg σ.notes cursor key carried each w times (idsOf ids initial)
      ids _ inner
  rw [hexit]
  dsimp only at hnext hkept hrecorded hfinalIndex hlearnedF ⊢
  intro sub next
  have nextE : State.Entered inner.state next'.2.1 := by
    rw [hnext]; exact indexValue_entered σ.cfg _ _ _ _ bodyGrew.2.1
  have keptE : State.Entered next'.2.1 kept.1 := by
    rw [hkept]; exact decideInvariants_entered σ.cfg _ true ids _ _ _ _ _ nextE.wf
  have ended :=
    Grew.discount learned.2 (bodyGrew.trans (Grew.of_entered σ.cfg _ (nextE.trans keptE)))
  have recordedG : Grew σ.cfg ((cursor.blocks, key) :: Term.addresses cursor.blocks body)
      (discount σ.cfg learned.2 learned.1 kept.1) recorded 0 := by
    rw [hrecorded]
    exact Grew.recordBound σ.cfg cursor.blocks key _ _ ended.2.1 List.mem_cons_self
  have finalEntered : State.Entered
      { recorded with leaves := recorded.leaves + (carried.length + each.length) } finalIndex.2.1 := by
    rw [hfinalIndex]
    exact Count.finalIndex_entered σ.cfg _ _ _ recordedG.2.1
  have learnedFE : State.Entered
      { recorded with leaves := recorded.leaves + (carried.length + each.length) } learnedF.1 := by
    rw [hlearnedF]
    exact finalEntered.trans (learnInvariants_entered σ.cfg ids _ _ _ _ _ finalEntered.wf)
  have toRecorded := (ended.widen fun _ m => List.mem_cons_of_mem _ m).trans recordedG
  -- the tables and the leaf counters
  have keptRecorded : kept.1.values.table.Le recorded.values.table := by
    have le := recordedG.1
    rw [discount_values] at le
    exact le
  have innerLe : inner.state.values.table.Le table :=
    (nextE.trans keptE).1.1.trans (keptRecorded.trans (learnedFE.1.1.trans sub))
  have wholeLe : s.values.table.Le table :=
    (toDecided.1.1.trans (learnedE.1.1.trans bodyGrew.1)).trans innerLe
  have decidedLeaves : decided.1.leaves = s.leaves := toDecided.2.1
  have recordedLeaves : s.leaves ≤ recorded.leaves := by
    rw [toRecorded.2.2.2.1, learnedE.2.1, decidedLeaves]
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have freshRecorded : ∀ n, recorded.leaves ≤ n → ρ n = none :=
    fun n above => scope.fresh n (Nat.le_trans recordedLeaves above)
  have step :
      σ.sem.loopStep w inputs (fun path' env' => body.denote σ.sem path' env') key path env =
      σ.sem.stepOf (fun i values => body.denote σ.sem (path ++ [.iteration key i])
        (env.extend inputs (.cons (σ.sem.index w i) values))) := rfl
  rw [step] at notUndefined ⊢
  refine Skel.Runs.loop (σ.sem.times times env)
    ((scope.countOf_is times).mono wholeLe (fun _ _ h => h)) (env.all initial)
    (ReadsAll.mono wholeLe (fun _ _ h => h) (scope.idsOf_reads initial)) _
    (fun i state below returns => ?_) (fun final returns => ?_)
  · -- an iteration: the body runs alone, from the leaves of the iteration
    have safe := Process.Every.iterate_step i _ 0 _ state below notUndefined.of_bind returns
    rw [Nat.zero_add] at safe
    have bodySafe : σ.NotUndefined
        ((body.denote σ.sem (path ++ [.iteration key i])
          (env.extend inputs (.cons (σ.sem.index w i) state.1))).bind
            fun values => Process.done values) := by
      rw [Process.bind_pure]
      exact safe.of_bind
    have scopeI := scope.iteration (toDecided.1.trans learnedE.1)
      (by rw [learnedE.2.1, decidedLeaves]) inputs i state.1
    rw [← decidedLeaves] at scopeI
    have ran := runsOne (path ++ [.iteration key i])
      (ρ.setFrom decided.1.leaves (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)))
      (env.extend inputs (.cons (σ.sem.index w i) state.1)) scopeI innerLe bodySafe
      (fun _ values _ _ _ _ => Rests.Runs.done values)
    rw [Process.bind_pure] at ran
    exact ran
  · -- after the iterations: what follows runs on the loop's result leaves
    rw [dyns_collected_countOf]
    have lengthR : (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2))).length =
        carried.length + each.length := by
      rw [σ.sem.dyns_length, List.length_append, List.length_map]
    refine next _ _ (Leaves.le_setFrom freshRecorded _) (fun n above => ?_) ?_
      (notUndefined.of_bind_canReturn returns)
    · refine Leaves.setFrom_fresh freshRecorded _ n ?_
      rw [lengthR]
      rw [learnedFE.2.1] at above
      exact above
    · have set := ReadsAll.setFrom (Run := σ.Run) (truth := σ.R.bool)
        (table := learnedF.1.values.table) ρ recorded.leaves
        (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2)))
      rw [lengthR] at set
      exact set

end

/-! ## A loop as the domain's laws read it -/

section
variable {D : Dialect} {Raw : Type}

/-- An iteration's leaves, as a loop's laws read them, over more leaves and a grown table. -/
theorem Loop.At.mono {T Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {Typed : Val → T → Prop} {table table' : Table Raw} {ρ ρ' : Leaves Val} {L : Loop T} {k : Nat}
    {carried : List Val} (sub : table.Le table') (le : ρ.Le ρ')
    (at_ : L.At Run R Typed table ρ k carried) : L.At Run R Typed table' ρ' k carried := by
  obtain ⟨⟨index, read, typed, numbered⟩, reads, length, types⟩ := at_
  exact ⟨⟨index, Reads.mono sub le read, typed, numbered⟩, ReadsAll.mono sub le reads, length,
    types⟩

/-- How often a loop runs, as a domain is told of it, over more leaves and a grown table. -/
theorem Loop.Counts.mono {T Val : Type} {Run : Raw → List Val → List Val → Prop} {R : Reading Val}
    {table table' : Table Raw} {ρ ρ' : Leaves Val} {L : Loop T} {N : Nat} (sub : table.Le table')
    (le : ρ.Le ρ') (counts : L.Counts Run R table ρ N) : L.Counts Run R table' ρ' N := by
  unfold Loop.Counts at counts ⊢
  split at counts
  · exact counts
  · obtain ⟨v, read, nat⟩ := counts
    exact ⟨v, Reads.mono sub le read, nat⟩

end

/-! ## The iterations of a loop -/

section
variable {D : Dialect} {Raw : Type}

/-- A history of iterations, one iteration longer: the values given after the last. -/
theorem history_extend {α : Type} {ran : Nat → α → α → Prop} {hist : Nat → α} {i : Nat}
    {start next : α} (zero : hist 0 = start) (before : ∀ j, j < i → ran j (hist j) (hist (j + 1)))
    (last : ran i (hist i) next) :
    ∃ hist' : Nat → α, hist' 0 = start ∧ hist' (i + 1) = next ∧
      ∀ j, j < i + 1 → ran j (hist' j) (hist' (j + 1)) := by
  refine ⟨fun j => if j ≤ i then hist j else next, ?_, ?_, fun j below => ?_⟩
  · simp only [Nat.zero_le, ↓reduceIte]
    exact zero
  · simp only [Nat.not_succ_le_self, ↓reduceIte]
  · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ below) with lt | rfl
    · have first : j ≤ i := Nat.le_of_lt lt
      have second : j + 1 ≤ i := lt
      simp only [first, second, ↓reduceIte]
      exact before j lt
    · simp only [Nat.le_refl, Nat.not_succ_le_self, ↓reduceIte]
      exact last

/-- A loop of a written number of iterations runs that often. -/
theorem times_fits (sem : Semantics D) {w : D.Who} {Γ : Ctx D.Ty} (env : Env sem.Val Γ) :
    ∀ (times : Times D w Γ) (m : Nat), times.size = some m → sem.times times env = m
  | .fixed _, _, same => Option.some.inj same
  | .value _ _, _, same => nomatch same

/-- The count of a loop on identifiers is a value's only where the loop runs as often as a count,
on the identifier of the count's name. -/
theorem countOf_eq_value {w : D.Who} {Γ : Ctx D.Ty} {ids : Ctx Ident} {t : D.Ty} {id : Ident}
    {ok : D.Count w t} : ∀ {times : Times D w Γ}, countOf ids times = .value id ok →
      ∃ c : Var Γ t, times = .value c ok ∧ id = idOf ids c.name
  | .fixed _, same => nomatch same
  | .value c _, same => by
      cases same
      exact ⟨c, rfl, rfl⟩

variable [DecidableEq Raw] (σ : Setting D Raw)

omit [DecidableEq Raw] in
/-- How often a loop runs, as the domain is told of it, on the leaves before it. -/
theorem countOf_counts (laws : σ.Lawful) {Γ : Ctx D.Ty} {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident}
    {env : Env σ.sem.Val Γ} {s : State Raw} (scope : Scope σ.sem σ.Runs σ.R ρ ids env s)
    (valid : ∀ n v, ρ n = some v → σ.Valid v) {w : D.Who} (times : Times D w Γ)
    {L : Loop D.Ty} (count : L.count = (countOf ids times).told) :
    L.Counts σ.Runs σ.R s.values.table ρ (σ.sem.times times env) := by
  unfold Loop.Counts
  rw [count]
  cases times with
  | fixed n => rfl
  | value c ok =>
      exact ⟨_, scope.idOf_reads c,
        laws.rules.count ok (env.get c) (Reads.valid valid (scope.idOf_reads c))⟩

/-- What holds at the entry of an iteration of a loop that a run reaches: the iteration is
reached, the carried values are valid, as many valid values are collected as iterations, the
invariants hold of the index and the carried values, and the carried values of the iterations up
to it are a history of which `ran` holds from each iteration to the next. -/
structure LoopAt {Γ : Ctx D.Ty} {carried each : List D.Ty} (w : D.Who)
    (step : Nat → σ.sem.LoopState carried each →
      Process σ.sem.S σ.sem.H (σ.sem.LoopState carried each))
    (start : σ.sem.LoopState carried each) (env : Env σ.sem.Val Γ)
    (invariants : List (List Name × List (Expr Raw)))
    (ran : Nat → List σ.sem.Dyn → List σ.sem.Dyn → Prop) (i : Nat)
    (state : σ.sem.LoopState carried each) : Prop where
  reached : (Process.iterate i step 0 start).CanReturn σ.permitted state
  valid : σ.AllValid state.1
  collected : CollectedOK σ.sem σ.Valid state.2 i
  holds : InvariantsHold σ env invariants ⟨D.index w, σ.sem.index w i⟩ (σ.sem.dyns state.1)
  history : ∃ hist : Nat → List σ.sem.Dyn, hist 0 = σ.sem.dyns start.1 ∧
    hist i = σ.sem.dyns state.1 ∧ ∀ j, j < i → ran j (hist j) (hist (j + 1))

end

/-! ## A loop is sound -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

omit [DecidableEq Raw] in
/-- The bounds that a setting's loops respect are the core's `Annotation.Bounded` of its bounds. -/
theorem Setting.bounded_eq :
    σ.Bounded = Zkc.Core.Annotation.Bounded ⟨σ.F⟩ σ.cfg.definition σ.cfg.role :=
  rfl

/-- A final-index operation reads the semantic index at the number of completed iterations.
This includes an empty loop and requires no equality between the count and index types. -/
theorem finalIndex_sound (laws : σ.Lawful) {w : D.Who} {Γ : Ctx D.Ty} (times : Times D w Γ)
    {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident} {env : Env σ.sem.Val Γ} {s : State Raw}
    {k : σ.cfg.domain.State} (inv : Inv σ ρ ids env k s) :
    let final := (countOf ids times).finalIndex σ.cfg s k
    σ.domain.Means final.2.2 final.2.1.values.table ρ ∧
      ∀ id, final.1 = some id → Reads σ.Runs σ.R.bool final.2.1.values.table ρ id
        ⟨D.index w, σ.sem.index w (σ.sem.times times env)⟩ := by
  cases times with
  | fixed n =>
      apply indexValue_sound σ laws inv.wf inv.means .nil
      intro raw found
      exact (laws.rules.indexAt w n raw found).2
  | value c ok =>
      have read := inv.toScope.idOf_reads c
      have valid := Reads.valid inv.valid read
      apply indexValue_sound σ laws inv.wf inv.means (.cons read .nil)
      intro raw found
      exact (laws.rules.indexFromCount ok raw found).2 _ valid

/-- **A loop is sound when its body is.** The invariant, decided on the initial values with the
index's first value, holds at every iteration that a run reaches (an induction over the
iterations, `LoopAt`, about the program's values): so the domain's `enter` and the invariant
learned at the body's entry mean the leaves of the iteration, the body is sound there, and the
invariant decided on the index's successor and what the body returns holds of the next carried
values. The carried values of each iteration of a run are the history that the domain's law
`afterLoop` is given; the invariant learned after the loop holds of the constructed final
index and the last carried values; the bound recorded from the domains' answer is an
upper bound of the count. -/
theorem loopSound : LoopSoundStatement σ := by
  intro laws cursor key Γ carried each w times gives initial inputs body growsBody soundBody
  intro path ρ ids env s k
  dsimp only
  intro inv steps defined facts everyFact unchanged
  obtain ⟨invariantsDefined, bodyDefined⟩ := defined
  simp only [Instr.EveryFact, Instr.EveryStep] at everyFact
  simp only [Instr.EveryRequired, Instr.EveryStep, Instr.EveryLoop,
    RequiredAt, requiredAt, Instr.addresses]
  rw [Instr.denote_loop, Process.every_bind]
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k inv.wf
  have entryInv := fun unchanged => atEntry_inv σ laws cursor key
    (.loop w times gives initial inputs body) (path := path) inv steps facts unchanged
  simp only [walkInstr] at unchanged ⊢
  revert unchanged
  simp only [Instr.site] at entryInv
  generalize atEntry σ.cfg σ.notes (.instruction cursor key) ids s k = e at entry entryInv
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry entryInv ⊢
  obtain ⟨first, decided, learned, hfirst, hdecided, hlearned, henter⟩ :=
    loopEnter_eq σ.cfg σ.notes cursor key carried w times (idsOf ids initial)
      ids E Ek
  rw [henter]
  simp only [Loop.told_index, Loop.told_carried]
  have firstE : State.Entered E first.2.1 := by
    rw [hfirst]; exact indexValue_entered σ.cfg _ [] E Ek entry.wf
  have decidedE : State.Entered first.2.1 decided.1 := by
    rw [hdecided]; exact decideInvariants_entered σ.cfg _ false ids _ _ _ _ _ firstE.wf
  have learnedE : State.Entered { decided.1 with leaves := decided.1.leaves + (carried.length + 1) }
      learned.1 := by
    rw [hlearned]; exact learnInvariants_entered σ.cfg ids _ _ _ _ _ decidedE.wf
  have toDecided := entry.trans (firstE.trans decidedE)
  have bodyGrew := growsBody
    (bindIds ids inputs
      (.leaf decided.1.leaves :: Ident.leaves (decided.1.leaves + 1) carried.length))
    learned.1 learned.2 learnedE.wf
  have soundOne := fun path' ρ' env' => soundBody path' ρ'
    (bindIds ids inputs
      (.leaf decided.1.leaves :: Ident.leaves (decided.1.leaves + 1) carried.length))
    env' learned.1 learned.2
  generalize walk σ.cfg σ.notes (cursor.region key) body _ learned.1 learned.2 = inner at bodyGrew soundOne ⊢
  obtain ⟨next', kept, recorded, finalIndex, learnedF, hnext, hkept, hrecorded, hfinalIndex, hlearnedF,
    hexit⟩ := loopExit_eq σ.cfg σ.notes cursor key carried each w times
      (idsOf ids initial) ids _ inner
  rw [hexit]
  dsimp only at hnext hkept hrecorded hfinalIndex hlearnedF ⊢
  intro unchanged
  -- how the state grows
  have nextE : State.Entered inner.state next'.2.1 := by
    rw [hnext]; exact indexValue_entered σ.cfg _ _ _ _ bodyGrew.2.1
  have keptE : State.Entered next'.2.1 kept.1 := by
    rw [hkept]; exact decideInvariants_entered σ.cfg _ true ids _ _ _ _ _ nextE.wf
  have ended :=
    Grew.discount learned.2 (bodyGrew.trans (Grew.of_entered σ.cfg _ (nextE.trans keptE)))
  have recordedG : Grew σ.cfg ((cursor.blocks, key) :: Term.addresses cursor.blocks body)
      (discount σ.cfg learned.2 learned.1 kept.1) recorded 0 := by
    rw [hrecorded]
    exact Grew.recordBound σ.cfg cursor.blocks key _ _ ended.2.1 List.mem_cons_self
  have finalEntered : State.Entered
      { recorded with leaves := recorded.leaves + (carried.length + each.length) } finalIndex.2.1 := by
    rw [hfinalIndex]
    exact Count.finalIndex_entered σ.cfg _ _ _ recordedG.2.1
  have learnedFE : State.Entered
      { recorded with leaves := recorded.leaves + (carried.length + each.length) } learnedF.1 := by
    rw [hlearnedF]
    exact finalEntered.trans (learnInvariants_entered σ.cfg ids _ _ _ _ _ finalEntered.wf)
  have keptRecorded : kept.1.values.table.Le recorded.values.table := by
    have le := recordedG.1
    rw [discount_values] at le
    exact le
  have innerToT : inner.state.values.table.Le recorded.values.table :=
    (nextE.trans keptE).1.1.trans keptRecorded
  have decidedToInner : decided.1.values.table.Le inner.state.values.table :=
    learnedE.1.1.trans bodyGrew.1
  have decidedToT : decided.1.values.table.Le recorded.values.table :=
    decidedToInner.trans innerToT
  have sToT : s.values.table.Le recorded.values.table := toDecided.1.1.trans decidedToT
  have decidedLeaves : decided.1.leaves = s.leaves := toDecided.2.1
  have recordedLeaves : s.leaves ≤ recorded.leaves := by
    rw [((ended.widen fun _ m => List.mem_cons_of_mem _ m).trans recordedG).2.2.2.1, learnedE.2.1,
      decidedLeaves]
    exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have freshRecorded : ∀ n, recorded.leaves ≤ n → ρ n = none :=
    fun n above => inv.fresh n (Nat.le_trans recordedLeaves above)
  -- the refusals: none is added anywhere that counts
  have refusalsDecided : ∃ new, decided.1.refusals = new ++ s.refusals := toDecided.2.2.2
  have refusalsLearned : ∃ new, learned.1.refusals = new ++ decided.1.refusals := learnedE.2.2.2
  have refusalsEnded : ∃ new, (discount σ.cfg learned.2 learned.1 kept.1).refusals =
      new ++ learned.1.refusals := ended.2.2.2.2.1
  have refusalsFinal : ∃ new, learnedF.1.refusals =
      new ++ (discount σ.cfg learned.2 learned.1 kept.1).refusals :=
    refusals_trans recordedG.2.2.2.2.1 learnedFE.2.2.2
  obtain ⟨decidedUnchanged, rest₁⟩ := refusals_split refusalsDecided
    (refusals_trans refusalsLearned (refusals_trans refusalsEnded refusalsFinal)) unchanged
  obtain ⟨-, rest₂⟩ := refusals_split refusalsLearned (refusals_trans refusalsEnded refusalsFinal)
    rest₁
  obtain ⟨endedUnchanged, -⟩ := refusals_split refusalsEnded refusalsFinal rest₂
  obtain ⟨entryUnchanged, rest₃⟩ := refusals_split entry.2.2.2 (firstE.trans decidedE).2.2.2
    decidedUnchanged
  obtain ⟨-, initialUnchanged⟩ := refusals_split firstE.2.2.2 decidedE.2.2.2 rest₃
  -- the invariant on the initial values
  have invE : Inv σ ρ ids env Ek E := entryInv entryUnchanged
  have firstSound := indexValue_sound σ laws (expression := σ.cfg.rules.indexAt w 0) (args := [])
    (result := ⟨D.index w, σ.sem.index w 0⟩) invE.wf invE.means .nil
    (fun e h => (laws.rules.indexAt w 0 e h).2)
  rw [← hfirst] at firstSound
  obtain ⟨firstMeans, firstIndex⟩ := firstSound
  have scopeFirst : Scope σ.sem σ.Runs σ.R ρ ids env first.2.1 :=
    invE.toScope.grow firstE.1 (Nat.le_of_eq firstE.2.1.symm)
  have initialValid : σ.AllValid (env.all initial) :=
    ReadsAll.valid inv.valid (inv.toScope.idsOf_reads initial)
  have definedInvariants : ∀ uses assertions, (uses, assertions) ∈ σ.notes.invariantsAt (.instruction cursor key) →
      ∀ τs, typesOf Γ uses = some τs → ∀ a, a ∈ assertions →
        Expr.Defined σ (τs ++ D.index w :: carried) a :=
    fun uses assertions m => invariantsDefined uses assertions (mem_invariantsAt m)
  have initialSound := decideInvariants_sound σ laws (.instruction cursor key) false (w := w)
    (indexValue := ⟨D.index w, σ.sem.index w 0⟩) (carriedValues := σ.sem.dyns (env.all initial))
    inv.valid rfl (laws.rules.index w 0).1 (dyns_map_fst σ.sem (env.all initial)) initialValid
    (σ.notes.invariantsAt (.instruction cursor key)) first.2.1 first.2.2 scopeFirst firstMeans firstIndex
    (ReadsAll.mono (entry.trans firstE).1.1 (fun _ _ h => h) (inv.toScope.idsOf_reads initial))
    definedInvariants (by rw [← hdecided]; exact initialUnchanged)
  rw [← hdecided] at initialSound
  obtain ⟨decidedMeans, holdsInitial⟩ := initialSound
  -- the leaves of an iteration, as the domain's laws read them
  have atIteration : ∀ (i : Nat) (c : HList σ.sem.Val carried), σ.AllValid c →
      ∀ table : Table Raw, Loop.At σ.Runs σ.R (TypedValue σ.sem σ.Valid) table
        (ρ.setFrom decided.1.leaves (σ.sem.dyns (HList.cons (σ.sem.index w i) c)))
        (Loop.told σ.cfg.rules carried (countOf ids times) (idsOf ids initial) decided.1.leaves) i
        (σ.sem.dyns c) := by
    intro i c cValid table
    have reads := ReadsAll.iteration (Run := σ.Runs) (truth := σ.R.bool) (w := w) table ρ
      decided.1.leaves i c
    cases reads with
    | cons indexRead carriedRead =>
        refine ⟨⟨_, indexRead, ⟨(laws.rules.index w i).1, rfl⟩, (laws.rules.index w i).2⟩,
          carriedRead, σ.sem.dyns_length c, fun j v τ hv hτ =>
            ⟨cValid v (List.mem_of_getElem? hv), ?_⟩⟩
        have typed := σ.sem.dyns_typed c j v hv
        have hτ' : carried[j]? = some τ := hτ
        rw [hτ'] at typed
        exact (Option.some.inj typed).symm
  have scopeDecided : Scope σ.sem σ.Runs σ.R ρ ids env decided.1 :=
    inv.toScope.grow toDecided.1 (Nat.le_of_eq decidedLeaves.symm)
  have counts := countOf_counts σ laws scopeDecided inv.valid times
    (L := Loop.told σ.cfg.rules carried (countOf ids times) (idsOf ids initial) decided.1.leaves)
    rfl
  have scopeOuter : ∀ (i : Nat) (c : HList σ.sem.Val carried),
      Scope σ.sem σ.Runs σ.R
        (ρ.setFrom decided.1.leaves (σ.sem.dyns (HList.cons (σ.sem.index w i) c))) ids env
        { decided.1 with leaves := decided.1.leaves + (carried.length + 1) } := by
    intro i c
    have outer := Scope.iterationOuter inv.toScope (w := w)
      (t := { decided.1 with leaves := decided.1.leaves + (carried.length + 1) }) toDecided.1
      (by show decided.1.leaves + (carried.length + 1) = s.leaves + (carried.length + 1)
          rw [decidedLeaves]) i c
    rw [← decidedLeaves] at outer
    exact outer
  -- the invariant of the walk at the body's entry, at an iteration of which the invariant holds
  have head : ∀ (i : Nat) (c : HList σ.sem.Val carried), i < σ.sem.times times env →
      σ.AllValid c →
      InvariantsHold σ env (σ.notes.invariantsAt (.instruction cursor key)) ⟨D.index w, σ.sem.index w i⟩ (σ.sem.dyns c) →
      Inv σ (ρ.setFrom decided.1.leaves (σ.sem.dyns (HList.cons (σ.sem.index w i) c)))
        (bindIds ids inputs
          (.leaf decided.1.leaves :: Ident.leaves (decided.1.leaves + 1) carried.length))
        (env.extend inputs (.cons (σ.sem.index w i) c)) learned.2 learned.1 := by
    intro i c below cValid holds
    have le : ρ.Le (ρ.setFrom decided.1.leaves (σ.sem.dyns (HList.cons (σ.sem.index w i) c))) :=
      Leaves.le_setFrom (fun n above => inv.fresh n (by rw [← decidedLeaves]; exact above)) _
    have enterMeans := σ.domain.enter (asks := Asks.nobody) scopeDecided.wf.slots decidedMeans counts le below
      (atIteration i c cValid _) (Asks.nobody_sound _ _ _ _)
    have reads := ReadsAll.iteration (Run := σ.Runs) (truth := σ.R.bool) (w := w)
      decided.1.values.table ρ
      decided.1.leaves i c
    cases reads with
    | cons indexRead carriedRead =>
        have learnedMeans : σ.domain.Means learned.2 learned.1.values.table
            (ρ.setFrom decided.1.leaves (σ.sem.dyns (HList.cons (σ.sem.index w i) c))) := by
          rw [hlearned]
          exact learnInvariants_sound σ laws (σ.notes.invariantsAt (.instruction cursor key)) _ _ (scopeOuter i c)
            enterMeans (fun id h => by cases h; exact indexRead) carriedRead holds
        have scopeI := Scope.iteration inv.toScope (toDecided.1.trans learnedE.1)
          (by rw [learnedE.2.1, decidedLeaves]) inputs i c
        rw [← decidedLeaves] at scopeI
        refine ⟨scopeI, Leaves.setFrom_valid inv.valid (fun v m => ?_), learnedMeans⟩
        rcases List.mem_cons.mp m with rfl | m
        · exact (laws.rules.index w i).1
        · exact cValid v m
  -- the iterations, named
  generalize hstep : σ.sem.loopStep w inputs
    (fun path' env' => Term.denote σ.sem body path' env') key path env = step
    at everyFact ⊢
  obtain ⟨ran, hran⟩ : ∃ ran : Nat → List σ.sem.Dyn → List σ.sem.Dyn → Prop, ran = fun j c c' =>
      ∃ ρk, ρ.Le ρk ∧ Loop.At σ.Runs σ.R (TypedValue σ.sem σ.Valid) recorded.values.table ρk
        (Loop.told σ.cfg.rules carried (countOf ids times) (idsOf ids initial) decided.1.leaves) j c ∧
        σ.domain.Means inner.known recorded.values.table ρk ∧
        Asks.nobody.Sound σ.Runs σ.R recorded.values.table ρk ∧
        ReadsAll σ.Runs σ.R.bool recorded.values.table ρk (inner.returned.take carried.length) c' :=
    ⟨_, rfl⟩
  -- the body at an iteration that a run reaches
  have bodyAt : ∀ (i : Nat) (state : σ.sem.LoopState carried each), i < σ.sem.times times env →
      LoopAt σ w step (env.all initial, HList.empties each) env (σ.notes.invariantsAt (.instruction cursor key)) ran i
        state →
      kept.1.refusals = next'.2.1.refusals ∧
      (Term.denote σ.sem body (path ++ [.iteration key i])
          (env.extend inputs (.cons (σ.sem.index w i) state.1))).Every σ.permitted
        (Returned σ (ρ.setFrom decided.1.leaves (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1)))
          (bindIds ids inputs
            (.leaf decided.1.leaves :: Ident.leaves (decided.1.leaves + 1) carried.length))
          (env.extend inputs (.cons (σ.sem.index w i) state.1)) inner.known inner.state
          inner.returned)
        (fun stop => ¬ σ.undefined stop) ∧
      Term.EveryRequired σ (cursor.region key) body (path ++ [.iteration key i])
        (env.extend inputs (.cons (σ.sem.index w i) state.1)) ∧
      ((Term.addresses cursor.blocks body).Nodup →
        BoundsApart σ learned.1 (Term.addresses cursor.blocks body) →
        Recorded σ (Term.addresses cursor.blocks body) inner.state →
        Term.EveryLoop σ.sem σ.permitted σ.Bounded body (path ++ [.iteration key i]) cursor.blocks
          (env.extend inputs (.cons (σ.sem.index w i) state.1))) := by
    intro i state below la
    have invI := head i state.1 below la.valid la.holds
    have alive := σ.alive invI.means
    have keptUnchanged : kept.1.refusals = learned.1.refusals := by
      have same := endedUnchanged
      rw [discount_alive alive] at same
      exact same
    obtain ⟨innerUnchanged, rest⟩ := refusals_split bodyGrew.2.2.2.2.1
      (refusals_trans nextE.2.2.2 keptE.2.2.2) keptUnchanged
    obtain ⟨-, keptDecided⟩ := refusals_split nextE.2.2.2 keptE.2.2.2 rest
    exact ⟨keptDecided, soundOne _ _ _ invI bodyDefined ((everyFact i below).canReturn la.reached)
      innerUnchanged⟩
  -- one iteration keeps what holds at an iteration
  have keeps : ∀ (i : Nat) (state : σ.sem.LoopState carried each), i < σ.sem.times times env →
      LoopAt σ w step (env.all initial, HList.empties each) env (σ.notes.invariantsAt (.instruction cursor key)) ran i
        state →
      (step i state).Every σ.permitted
        (LoopAt σ w step (env.all initial, HList.empties each) env (σ.notes.invariantsAt (.instruction cursor key)) ran
          (i + 1))
        (fun stop => ¬ σ.undefined stop) := by
    intro i state below la
    obtain ⟨keptDecided, every, -, -⟩ := bodyAt i state below la
    have leI :
        ρ.Le (ρ.setFrom decided.1.leaves (σ.sem.dyns (HList.cons (σ.sem.index w i) state.1))) :=
      Leaves.le_setFrom (fun n above => inv.fresh n (by rw [← decidedLeaves]; exact above)) _
    have stepEq : step i state = (Term.denote σ.sem body (path ++ [.iteration key i])
        (env.extend inputs (.cons (σ.sem.index w i) state.1))).bind fun out =>
          .done ((HList.split carried out).1, state.2.push (HList.split carried out).2) := by
      rw [← hstep]
      rfl
    rw [stepEq, Process.every_bind]
    refine Process.every_mono _ _ (fun out both => ?_) (fun _ h => h.1)
      (Process.every_and _ _ every (Process.every_canReturn _))
    obtain ⟨⟨ρ', le', inv', reads'⟩, returns⟩ := both
    have outValid : σ.AllValid out := ReadsAll.valid inv'.valid reads'
    have splitValid : σ.AllValid (HList.split carried out).1 := fun v m =>
      outValid v (by rw [σ.sem.dyns_split out]; exact List.mem_append_left _ m)
    have collectedValid : σ.AllValid (HList.split carried out).2 := fun v m =>
      outValid v (by rw [σ.sem.dyns_split out]; exact List.mem_append_right _ m)
    have returnedReads : ReadsAll σ.Runs σ.R.bool inner.state.values.table ρ'
        (inner.returned.take carried.length) (σ.sem.dyns (HList.split carried out).1) := by
      rw [← dyns_take_split]
      exact ReadsAll.take carried.length reads'
    have reads := ReadsAll.iteration (Run := σ.Runs) (truth := σ.R.bool) (w := w)
      inner.state.values.table ρ
      decided.1.leaves i state.1
    cases reads with
    | cons indexRead _ =>
        -- the invariant on the index's successor and what the body returns
        have nextSound : σ.domain.Means next'.2.2 next'.2.1.values.table ρ' ∧
            ∀ id, next'.1 = some id → Reads σ.Runs σ.R.bool next'.2.1.values.table ρ' id
              ⟨D.index w, σ.sem.index w (i + 1)⟩ := by
          rw [hnext]
          exact indexValue_sound σ laws inv'.wf inv'.means
            (.cons (Reads.mono (Table.Le.refl _) le' indexRead) .nil)
            (fun e h => (laws.rules.indexNext w e h).2 i)
        obtain ⟨nextMeans, nextIndex⟩ := nextSound
        have scopeNext : Scope σ.sem σ.Runs σ.R ρ' ids env next'.2.1 :=
          ⟨fun n above => inv'.fresh n (by rw [← nextE.2.1]; exact above),
            fun τ x => by
              obtain ⟨id, found, read⟩ := inv.agree τ x
              exact ⟨id, found, Reads.mono (toDecided.1.1.trans (decidedToInner.trans nextE.1.1))
                (fun n v h => le' n v (leI n v h)) read⟩,
            inv.bound, nextE.wf⟩
        have keptHolds : InvariantsHold σ env (σ.notes.invariantsAt (.instruction cursor key))
            ⟨D.index w, σ.sem.index w (i + 1)⟩ (σ.sem.dyns (HList.split carried out).1) :=
          (decideInvariants_sound σ laws (.instruction cursor key) true (w := w)
            (indexValue := ⟨D.index w, σ.sem.index w (i + 1)⟩)
            (carriedValues := σ.sem.dyns (HList.split carried out).1)
            inv'.valid rfl (laws.rules.index w (i + 1)).1 (dyns_map_fst σ.sem _) splitValid
            (σ.notes.invariantsAt (.instruction cursor key)) next'.2.1 next'.2.2 scopeNext nextMeans nextIndex
            (ReadsAll.mono nextE.1.1 (fun _ _ h => h) returnedReads) definedInvariants
            (by rw [← hkept]; exact keptDecided)).2
        -- the iteration, as the domain's law `afterLoop` is given it
        have doneI : ran i (σ.sem.dyns state.1) (σ.sem.dyns (HList.split carried out).1) := by
          rw [hran]
          exact ⟨ρ', fun n v h => le' n v (leI n v h),
            (atIteration i state.1 la.valid recorded.values.table).mono (Table.Le.refl _) le',
            σ.domain.mono innerToT (fun _ _ h => h) inv'.means, Asks.nobody_sound _ _ _ _,
            ReadsAll.mono innerToT (fun _ _ h => h) returnedReads⟩
        obtain ⟨hist, hist0, histI, before⟩ := la.history
        obtain ⟨hist', hist'0, hist'I, before'⟩ :=
          history_extend hist0 before (by rw [histI]; exact doneI)
        have stepReturns : (step i state).CanReturn σ.permitted
            ((HList.split carried out).1, state.2.push (HList.split carried out).2) := by
          rw [stepEq]
          exact Process.CanReturn.bind returns (.done _)
        exact ⟨Process.CanReturn.iterate_succ la.reached (by rw [Nat.zero_add]; exact stepReturns),
          splitValid, collectedOK_push la.collected collectedValid, keptHolds, hist', hist'0,
          hist'I, before'⟩
  -- before the first iteration
  have I0 : LoopAt σ w step (env.all initial, HList.empties each) env (σ.notes.invariantsAt (.instruction cursor key))
      ran 0 (env.all initial, HList.empties each) :=
    ⟨.done _, initialValid, collectedOK_empties each, holdsInitial,
      fun _ => σ.sem.dyns (env.all initial), rfl, rfl,
      fun _ below => absurd below (Nat.not_lt_zero _)⟩
  have all := Process.every_iterate_below σ.permitted (fun stop => ¬ σ.undefined stop) step
    (LoopAt σ w step (env.all initial, HList.empties each) env (σ.notes.invariantsAt (.instruction cursor key)) ran)
    (σ.sem.times times env) keeps
  -- after the last iteration
  have afterLoop : ∀ final : σ.sem.LoopState carried each,
      LoopAt σ w step (env.all initial, HList.empties each) env (σ.notes.invariantsAt (.instruction cursor key)) ran
        (σ.sem.times times env) final →
      Returned σ ρ ids env learnedF.2 learnedF.1
        (Ident.leaves recorded.leaves (carried.length + each.length))
        (final.1.append (σ.sem.collected times.size final.2)) := by
    intro final la
    have valuesValid : σ.AllValid (final.1.append (σ.sem.collected times.size final.2)) := by
      intro v m
      rw [σ.sem.dyns_append] at m
      rcases List.mem_append.mp m with m | m
      · exact la.valid v m
      · exact collected_valid laws.rules.collect times.size
          (fun m h => times_fits σ.sem env times m h) la.collected v m
    have lengthValues :
        (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2))).length =
          carried.length + each.length := by
      rw [σ.sem.dyns_length, List.length_append, List.length_map]
    have leF := Leaves.le_setFrom freshRecorded
      (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2)))
    have readsMade : ReadsAll σ.Runs σ.R.bool recorded.values.table
        (ρ.setFrom recorded.leaves
          (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2))))
        (Ident.leaves recorded.leaves (carried.length + each.length))
        (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2))) := by
      have set := ReadsAll.setFrom (Run := σ.Runs) (truth := σ.R.bool)
        (table := recorded.values.table) ρ recorded.leaves
        (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2)))
      rw [lengthValues] at set
      exact set
    have readsCarried : ReadsAll σ.Runs σ.R.bool recorded.values.table
        (ρ.setFrom recorded.leaves
          (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2))))
        ((Ident.leaves recorded.leaves (carried.length + each.length)).take carried.length)
        (σ.sem.dyns final.1) := by
      have taken := ReadsAll.take carried.length readsMade
      have takeEq : (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2))).take
          carried.length = σ.sem.dyns final.1 := by
        rw [σ.sem.dyns_append, take_append_length _ _ _ (σ.sem.dyns_length _)]
      rw [takeEq] at taken
      exact taken
    obtain ⟨hist, hist0, histN, iterations⟩ := la.history
    rw [hran] at iterations
    have afterMeans := σ.domain.afterLoop (before := Asks.nobody) (exit := Asks.nobody)
      (carried := hist) (N := σ.sem.times times env)
      recordedG.2.1.slots (Asks.nobody_sound _ _ _ _) (σ.domain.mono decidedToT (fun _ _ h => h) decidedMeans)
      (Loop.Counts.mono decidedToT (fun _ _ h => h) counts)
      (by rw [hist0]; exact ReadsAll.mono sToT (fun _ _ h => h) (inv.toScope.idsOf_reads initial))
      iterations leF (by rw [histN]; exact readsCarried)
    have leavesMeans := σ.domain.leaves recordedG.2.1.slots afterMeans
      (ReadsAll.zip_typed (final.1.append (σ.sem.collected times.size final.2)) readsMade
        valuesValid)
    have scopeF : Scope σ.sem σ.Runs σ.R
        (ρ.setFrom recorded.leaves
          (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2))))
        ids env { recorded with leaves := recorded.leaves + (carried.length + each.length) } :=
      ⟨fun n above => Leaves.setFrom_fresh freshRecorded _ n (by rw [lengthValues]; exact above),
        fun τ x => by
          obtain ⟨id, found, read⟩ := inv.agree τ x
          exact ⟨id, found, Reads.mono sToT leF read⟩,
        inv.bound, recordedG.2.1⟩
    have finalSound := finalIndex_sound σ laws times
      ⟨scopeF, Leaves.setFrom_valid inv.valid valuesValid, leavesMeans⟩
    rw [← hfinalIndex] at finalSound
    have finalScope := scopeF.grow finalEntered.1 (Nat.le_of_eq finalEntered.2.1.symm)
    have learnedFMeans : σ.domain.Means learnedF.2 learnedF.1.values.table
        (ρ.setFrom recorded.leaves
          (σ.sem.dyns (final.1.append (σ.sem.collected times.size final.2)))) := by
      rw [hlearnedF]
      exact learnInvariants_sound σ laws (σ.notes.invariantsAt (.instruction cursor key)) _ _ finalScope finalSound.1
        finalSound.2 (ReadsAll.mono finalEntered.1.1 (fun _ _ h => h) readsCarried) la.holds
    refine ⟨_, leF, ⟨⟨fun n above => ?_, fun τ x => ?_, inv.bound, learnedFE.wf⟩,
      Leaves.setFrom_valid inv.valid valuesValid, learnedFMeans⟩,
      ReadsAll.mono learnedFE.1.1 (fun _ _ h => h) readsMade⟩
    · refine Leaves.setFrom_fresh freshRecorded _ n ?_
      rw [lengthValues]
      rw [learnedFE.2.1] at above
      exact above
    · obtain ⟨id, found, read⟩ := inv.agree τ x
      exact ⟨id, found, Reads.mono (sToT.trans learnedFE.1.1) leF read⟩
  refine ⟨?_, trivial, ?_, ?_⟩
  · -- what the loop returns, and that it never stops `undefined`
    refine Process.every_mono _ _ (fun final la => ?_) (fun _ h => h)
      (all (σ.sem.times times env) 0 (env.all initial, HList.empties each)
        (Nat.le_of_eq (Nat.zero_add _)) I0)
    rw [Nat.zero_add] at la
    exact afterLoop final la
  · -- the requirements of the operations that the body reaches, at every iteration
    intro i below
    refine Process.every_mono _ _ (fun state la => ?_) (fun _ _ => trivial)
      (all i 0 (env.all initial, HList.empties each)
        (by rw [Nat.zero_add]; exact Nat.le_of_lt below) I0)
    rw [Nat.zero_add] at la
    exact (bodyAt i state below la).2.2.1
  · -- the loop's bound, and the loops of the body at every iteration
    intro nodup apart recordedF
    obtain ⟨notHere, nodupBody⟩ := List.nodup_cons.mp nodup
    have learnedBounds : learned.1.bounds = s.bounds := learnedE.2.2.1.trans toDecided.2.2.1
    have apartBody : BoundsApart σ learned.1 (Term.addresses cursor.blocks body) := by
      intro q m bl key' place at_
      rw [learnedBounds] at m
      exact apart q m bl key' place (List.mem_cons_of_mem _ at_)
    obtain ⟨newR, boundsR, addedR⟩ := recordBound_bounds (σ.cfg.place cursor.blocks key)
      (σ.cfg.domain.answers decided.2) (countOf ids times)
      (discount σ.cfg learned.2 learned.1 kept.1)
    rw [← hrecorded] at boundsR
    have innerBounds : (discount σ.cfg learned.2 learned.1 kept.1).bounds = inner.state.bounds := by
      rw [discount_bounds, keptE.2.2.1, nextE.2.2.1]
    have finalBounds : learnedF.1.bounds = newR ++ inner.state.bounds := by
      rw [learnedFE.2.2.1]
      show recorded.bounds = _
      rw [boundsR, innerBounds]
    have recordedBody : Recorded σ (Term.addresses cursor.blocks body) inner.state :=
      Recorded.before recordedF (fun a m => List.mem_cons_of_mem _ m)
        (fun a m same => notHere (by rw [List.mem_singleton] at same; rw [← same]; exact m))
        ⟨newR, finalBounds, fun q m => ⟨cursor.blocks, key, (addedR q m).1, List.mem_singleton_self _⟩⟩
    refine ⟨?_, fun i below => ?_⟩
    · unfold Setting.Bounded
      intro bound found
      simp only [Option.map_eq_some_iff] at found
      obtain ⟨q, hq, rfl⟩ := found
      have inF := List.mem_of_find?_eq_some hq
      have decided' := List.find?_some hq
      have placeQ : q.1 = ⟨σ.cfg.definition, cursor.blocks, some key, σ.cfg.role⟩ :=
        of_decide_eq_true decided'
      have inFinal := recordedF q.1 q.2 cursor.blocks key inF placeQ List.mem_cons_self
      rw [finalBounds] at inFinal
      rcases List.mem_append.mp inFinal with m | m
      · obtain ⟨-, t, id, ok, isValue, upper⟩ := addedR _ m
        obtain ⟨c, htimes, hid⟩ := countOf_eq_value isValue
        subst hid
        obtain ⟨v, n, read, nat, below⟩ := (σ.domain.answers decidedMeans).upperAt
          (fun raw operands ys zs a b => laws.rules.functional raw operands ys zs a.1 b.1) toDecided.wf.slots upper
        have read' := scopeDecided.idOf_reads c
        have same := Reads.functional (fun raw operands results results' first second =>
          laws.rules.functional raw operands results results' first.1 second.1) toDecided.wf
          read read'
        subst same
        have counted := laws.rules.count ok (env.get c) (Reads.valid inv.valid read')
        rw [counted] at nat
        cases nat
        rw [htimes]
        exact below
      · obtain ⟨newB, boundsB, addedB⟩ := bodyGrew.2.2.2.2.2
        rw [boundsB] at m
        rcases List.mem_append.mp m with m | m
        · obtain ⟨bl, key', place', at'⟩ := addedB _ m
          have place'' : q.1 = σ.cfg.place bl key' := place'
          rw [placeQ] at place''
          simp only [Config.place, Place.mk.injEq, Option.some.injEq, true_and, and_true]
            at place''
          obtain ⟨rfl, rfl⟩ := place''
          exact absurd at' notHere
        · rw [learnedBounds] at m
          exact absurd List.mem_cons_self (apart _ m cursor.blocks key placeQ)
    · refine Process.every_mono _ _ (fun state la => ?_) (fun _ _ => trivial)
        (all i 0 (env.all initial, HList.empties each)
          (by rw [Nat.zero_add]; exact Nat.le_of_lt below) I0)
      rw [Nat.zero_add] at la
      exact (bodyAt i state below la).2.2.2 nodupBody apartBody recordedBody

end

#print axioms loopGrows
#print axioms loopRuns
#print axioms loopSound

end Zkc.Core.BodyAnalysis
