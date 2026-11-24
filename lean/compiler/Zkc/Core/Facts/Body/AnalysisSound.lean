module

public import Zkc.Core.Facts.Body.WalkSound

@[expose] public section

/-!
The statements about the analysis of a definition: its process runs the skeleton of the analysis
(`AnalyseRunsStatement`); a body that the analysis accepts is safe, satisfies its summary's
guarantees and respects its bounds (`AnalyseSafeStatement`), is assured in the evidence layer's
sense (`AnalyseAssuredStatement`), satisfies its summary as a function of its inputs
(`AnalyseHoldsStatement`), meets the requirements of every operation that it reaches
(`AnalyseRequiredStatement`); and together, the analysis is sound (`AnalyseSoundStatement`).

All but the first are from one lemma (`analyseFrom_sound`): from the invariant of the walk at the
start, where the inputs are the first leaves, their identifiers read their values and the
domain's state, told their types and the summary's requirements, means them
(`analyseFrom_start`), the walk of the body is sound (`termSound`); the summary's guarantees are
decided where the body returns. Its part about what the body returns needs neither distinct
addresses nor recorded bounds, which only the part about loops does.
-/

namespace Zkc.Core.BodyAnalysis

/-! ## The start of the analysis -/

section
variable {D : Dialect} {Raw : Type}

/-- The values without entries are well formed. -/
theorem Values.empty_wf [DecidableEq Raw] (place : Raw → Nat) : (Values.empty place).WF :=
  ⟨fun _ m => (nomatch m), fun _ _ m => (nomatch m), fun _ _ _ _ m => (nomatch m)⟩

/-- No leaf at or above the number of the inputs has a value. -/
theorem inputLeaves_fresh (sem : Semantics D) {types : List D.Ty} (values : HList sem.Val types) :
    ∀ n, types.length ≤ n → inputLeaves sem values n = none :=
  fun n above => Leaves.setFrom_fresh (fun _ _ => rfl) (sem.dyns values) n
    (by rw [sem.dyns_length, Nat.zero_add]; exact above)

/-- The first leaves read the values of the inputs. -/
theorem inputLeaves_reads (sem : Semantics D) {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {truth : sem.Dyn → Option Bool} {table : Table Raw} {types : List D.Ty}
    (values : HList sem.Val types) :
    ReadsAll Run truth table (inputLeaves sem values) (Ident.leaves 0 types.length)
      (sem.dyns values) := by
  have set := ReadsAll.setFrom (Run := Run) (truth := truth) (table := table) (fun _ => none) 0
    (sem.dyns values)
  rw [sem.dyns_length] at set
  exact set

/-- The leaves of valid inputs have valid values. -/
theorem inputLeaves_valid {sem : Semantics D} {Valid : sem.Dyn → Prop} {types : List D.Ty}
    (values : HList sem.Val types) (valid : ∀ v, v ∈ sem.dyns values → Valid v) :
    ∀ n v, inputLeaves sem values n = some v → Valid v :=
  Leaves.setFrom_valid (fun _ _ found => (nomatch found)) valid

/-- **The scope at the start**: the inputs' names are bound to the first leaves, which read their
values, and no leaf at or above the counter has a value. -/
theorem Scope.start {sem : Semantics D} {Run : Raw → List sem.Dyn → List sem.Dyn → Prop}
    {R : Reading sem.Dyn} {types : List D.Ty} (inputs : Names types)
    (values : HList sem.Val types) (s : State Raw) (leaves : s.leaves = types.length)
    (wf : s.values.WF) :
    Scope sem Run R (inputLeaves sem values) (bindIds Ctx.empty inputs (Ident.leaves 0 types.length))
      (Env.empty.extend inputs values) s := by
  have empty : Scope sem Run R (inputLeaves sem values) Ctx.empty
      (Env.empty : Env sem.Val Ctx.empty) s :=
    ⟨fun n above => inputLeaves_fresh sem values n (by rw [← leaves]; exact above),
      fun τ x => absurd x.typed (by rw [Ctx.find?_empty]; exact fun same => nomatch same),
      fun name id found => absurd found (by rw [Ctx.find?_empty]; exact fun same => nomatch same),
      wf⟩
  exact empty.bind inputs _ values (inputLeaves_reads sem values)

variable [DecidableEq Raw]

/-- The analysis of a body, with its parts named: the requirements learned at the start, the walk
of the body, and the guarantees decided where it returns. -/
theorem analyseFrom_eq (cfg : Config D Raw) (notes : Annotations Raw) {types outs : List D.Ty}
    (summary : Contract Raw) (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) (start : Values Raw) :
    ∃ learned walked decided,
      learned = learnAll cfg ((Ident.leaves 0 types.length).map some) summary.requires
        ⟨start, types.length, [], []⟩
        (cfg.domain.leaves cfg.domain.init ((Ident.leaves 0 types.length).zip types)) ∧
      walked = walk cfg notes .root body (bindIds Ctx.empty inputs (Ident.leaves 0 types.length))
        learned.1 learned.2 ∧
      decided = decideClauses cfg cfg.exitPlace .guarantee
        ((Ident.leaves 0 types.length ++ walked.returned).map some) 0 summary.postconditions walked.state
        walked.known ∧
      analyseFrom cfg notes summary inputs body start =
        { walked with state := decided.1, known := decided.2 } :=
  ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-- Learning the requirements and deciding the guarantees preserve the walk's growth invariant,
including the body addresses at which it adds bounds. -/
theorem analyseFrom_stateGrew (cfg : Config D Raw) (notes : Annotations Raw) {types outs : List D.Ty}
    (summary : Contract Raw) (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) (start : Values Raw) (wf : start.WF) :
    Grew cfg (Term.addresses [] body) ⟨start, types.length, [], []⟩
      (analyseFrom cfg notes summary inputs body start).state
      (Term.leafCount cfg.rules body) := by
  obtain ⟨learned, walked, decided, hl, hw, hd, he⟩ :=
    analyseFrom_eq cfg notes summary inputs body start
  rw [he]
  have learnedE : State.Entered ⟨start, types.length, [], []⟩ learned.1 := by
    rw [hl]; exact learnAll_entered cfg _ summary.requires _ _ wf
  have grewW : Grew cfg (Term.addresses [] body) learned.1 walked.state
      (Term.leafCount cfg.rules body) := by
    rw [hw]; exact termGrows cfg notes .root body _ _ _ learnedE.wf
  have decidedE : State.Entered walked.state decided.1 := by
    rw [hd]; exact decideClauses_entered cfg _ _ _ summary.postconditions 0 _ _ grewW.2.1
  simpa only [Nat.zero_add, Nat.add_zero] using
    ((Grew.of_entered cfg _ learnedE).trans grewW).trans (Grew.of_entered cfg _ decidedE)

/-- **The analysis grows the table** that it starts from, and keeps its values well formed. -/
theorem analyseFrom_grew (cfg : Config D Raw) (notes : Annotations Raw) {types outs : List D.Ty}
    (summary : Contract Raw) (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) (start : Values Raw) (wf : start.WF) :
    start.table.Le (analyseFrom cfg notes summary inputs body start).state.values.table ∧
      (analyseFrom cfg notes summary inputs body start).state.values.WF := by
  have grew := analyseFrom_stateGrew cfg notes summary inputs body start wf
  exact ⟨grew.1, grew.2.1⟩

end

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

/-- **The invariant of the walk at the start of the analysis**: on valid inputs of which the
summary's requirements hold, the inputs as the first leaves, the domain told their types and the
requirements learned. -/
theorem analyseFrom_start (laws : σ.Lawful) {types : List D.Ty} (summary : Contract Raw)
    (inputs : Names types) (start : Values Raw) (wf : start.WF) (values : HList σ.sem.Val types)
    (valid : σ.AllValid values)
    (required : ∀ requirement, requirement ∈ summary.requires →
      requirement.Holds σ.Runs σ.R (σ.sem.dyns values)) :
    Inv σ (inputLeaves σ.sem values) (bindIds Ctx.empty inputs (Ident.leaves 0 types.length))
      (Env.empty.extend inputs values)
      (learnAll σ.cfg ((Ident.leaves 0 types.length).map some) summary.requires
        ⟨start, types.length, [], []⟩
        (σ.cfg.domain.leaves σ.cfg.domain.init ((Ident.leaves 0 types.length).zip types))).2
      (learnAll σ.cfg ((Ident.leaves 0 types.length).map some) summary.requires
        ⟨start, types.length, [], []⟩
        (σ.cfg.domain.leaves σ.cfg.domain.init ((Ident.leaves 0 types.length).zip types))).1 := by
  have entered := learnAll_entered σ.cfg ((Ident.leaves 0 types.length).map some) summary.requires
    ⟨start, types.length, [], []⟩
    (σ.cfg.domain.leaves σ.cfg.domain.init ((Ident.leaves 0 types.length).zip types)) wf
  have reads := inputLeaves_reads (Run := σ.Runs) (truth := σ.R.bool) (table := start.table)
    σ.sem values
  have initMeans := σ.domain.leaves wf.slots (σ.domain.init start.table (inputLeaves σ.sem values))
    (ReadsAll.zip_typed values reads valid)
  have means := learnAll_sound σ laws.rules summary.requires ⟨start, types.length, [], []⟩ _
    initMeans wf (PositionsRead.of_readsAll reads) required
  exact ⟨Scope.start inputs values _ entered.2.1 entered.wf, inputLeaves_valid values valid, means⟩

/-- **The analysis of a body that it accepts is sound**, from any table whose values are well
formed, on valid inputs of which the summary's requirements hold and where every given fact holds:
the body never stops `undefined` and returns valid values of which, with the inputs, every
guarantee of the summary holds where the guarantees are defined; the requirements of every
operation that it reaches hold; and, where its addresses are distinct and the setting's bounds of
the definition are recorded, every loop that it reaches respects them. -/
theorem analyseFrom_sound (laws : σ.Lawful) {types outs : List D.Ty} (summary : Contract Raw)
    (inputs : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (start : Values Raw) (wf : start.WF) (defined : Term.AnnotationsDefined σ .root body)
    (accepted : (analyseFrom σ.cfg σ.notes summary inputs body start).state.refusals = [])
    (path : List Frame) (values : HList σ.sem.Val types) (valid : σ.AllValid values)
    (required : ∀ requirement, requirement ∈ summary.requires →
      requirement.Holds σ.Runs σ.R (σ.sem.dyns values))
    (facts : Term.EveryFact σ .root body path (Env.empty.extend inputs values)) :
    (body.denote σ.sem path (Env.empty.extend inputs values)).Every σ.permitted
        (fun returned => σ.AllValid returned ∧
          ((∀ guarantee, guarantee ∈ summary.ensures → Expr.Defined σ (types ++ outs) guarantee) →
            ∀ guarantee, guarantee ∈ summary.ensures →
              guarantee.Holds σ.Runs σ.R (σ.sem.dyns values ++ σ.sem.dyns returned)))
        (fun stop => ¬ σ.undefined stop) ∧
      Term.EveryRequired σ .root body path (Env.empty.extend inputs values) ∧
      ((Term.addresses [] body).Nodup →
        (∀ p b, (p, b) ∈ σ.F → p.definition = σ.cfg.definition → p.role = σ.cfg.role →
          (p, b) ∈ (analyseFrom σ.cfg σ.notes summary inputs body start).state.bounds) →
        Term.EveryLoop σ.sem σ.permitted σ.Bounded body path []
          (Env.empty.extend inputs values)) := by
  obtain ⟨learned, walked, decided, hl, hw, hd, he⟩ :=
    analyseFrom_eq σ.cfg σ.notes summary inputs body start
  rw [he] at accepted ⊢
  dsimp only at accepted ⊢
  have learnedE : State.Entered ⟨start, types.length, [], []⟩ learned.1 := by
    rw [hl]; exact learnAll_entered σ.cfg _ summary.requires _ _ wf
  have startInv : Inv σ (inputLeaves σ.sem values)
      (bindIds Ctx.empty inputs (Ident.leaves 0 types.length)) (Env.empty.extend inputs values)
      learned.2 learned.1 := by
    rw [hl]; exact analyseFrom_start σ laws summary inputs start wf values valid required
  have grewW : Grew σ.cfg (Term.addresses [] body) learned.1 walked.state
      (Term.leafCount σ.cfg.rules body) := by
    rw [hw]; exact termGrows σ.cfg σ.notes .root body _ _ _ learnedE.wf
  have decidedE : State.Entered walked.state decided.1 := by
    rw [hd]; exact decideClauses_entered σ.cfg _ _ _ summary.postconditions 0 _ _ grewW.2.1
  -- no refusal anywhere: the start adds none to none, the walk none, the guarantees none
  obtain ⟨newD, refusalsD⟩ := decidedE.2.2.2
  obtain ⟨newW, refusalsW⟩ := grewW.2.2.2.2.1
  obtain ⟨newL, refusalsL⟩ := learnedE.2.2.2
  have walkedNone : walked.state.refusals = [] :=
    (List.append_eq_nil_iff.mp (refusalsD.symm.trans accepted)).2
  have learnedNone : learned.1.refusals = [] :=
    (List.append_eq_nil_iff.mp (refusalsW.symm.trans walkedNone)).2
  have sound := termSound σ laws .root body path (inputLeaves σ.sem values)
    (bindIds Ctx.empty inputs (Ident.leaves 0 types.length)) (Env.empty.extend inputs values)
    learned.1 learned.2 startInv defined facts
    (by rw [← hw]; exact walkedNone.trans learnedNone.symm)
  rw [← hw] at sound
  obtain ⟨every, requiredAll, loops⟩ := sound
  refine ⟨Process.every_mono _ _ (fun returned ret => ?_) (fun _ h => h) every, requiredAll,
    fun nodup recorded => loops nodup ?_ ?_⟩
  · -- what the body returns: valid, and the guarantees hold where they are defined
    obtain ⟨ρ', le, inv', reads⟩ := ret
    refine ⟨ReadsAll.valid inv'.valid reads, fun guarantees => ?_⟩
    have positions : PositionsRead σ walked.state.values.table ρ'
        ((Ident.leaves 0 types.length ++ walked.returned).map some)
        (σ.sem.dyns values ++ σ.sem.dyns returned) :=
      PositionsRead.of_readsAll (ReadsAll.append
        (ReadsAll.mono (Table.Le.refl _) le (inputLeaves_reads σ.sem values)) reads)
    have argsValid : ∀ v, v ∈ σ.sem.dyns values ++ σ.sem.dyns returned → σ.Valid v := by
      intro v m
      rcases List.mem_append.mp m with m | m
      · exact valid v m
      · exact ReadsAll.valid inv'.valid reads v m
    have typesEq : (σ.sem.dyns values ++ σ.sem.dyns returned).map Sigma.fst = types ++ outs := by
      rw [List.map_append, dyns_map_fst, dyns_map_fst]
    have decidedSound := decideClauses_sound σ laws.rules σ.cfg.exitPlace .guarantee summary.postconditions 0
      walked.state walked.known inv'.means grewW.2.1 positions
      (fun g m => Expr.Defined.at_values (by rw [typesEq]; exact guarantees g m) argsValid)
      (by rw [← hd]; exact accepted.trans walkedNone.symm)
    exact decidedSound.2
  · -- no bound recorded at the start
    intro q m
    have none : q ∈ ([] : List (Place × Nat)) := by
      rw [learnedE.2.2.1] at m
      exact m
    exact nomatch none
  · -- the setting's bounds of the definition, recorded where the guarantees are decided, were
    -- recorded by the walk
    intro p b bl key inF place _
    have found := recorded p b inF (by rw [place]) (by rw [place])
    rw [decidedE.2.2.1] at found
    exact found

/-! ## The statements -/

/-- **The process of a body that never stops `undefined` runs the skeleton of its analysis**, from
any table whose values are well formed, over the analysis's final table, from the values of its
inputs as the first leaves. -/
theorem analyseRuns : AnalyseRunsStatement σ := by
  intro laws types outs summary inputs body start
  dsimp only
  intro wf path values safe
  obtain ⟨learned, walked, decided, hl, hw, hd, he⟩ :=
    analyseFrom_eq σ.cfg σ.notes summary inputs body start
  rw [he]
  dsimp only
  have learnedE : State.Entered ⟨start, types.length, [], []⟩ learned.1 := by
    rw [hl]; exact learnAll_entered σ.cfg _ summary.requires _ _ wf
  have grewW : Grew σ.cfg (Term.addresses [] body) learned.1 walked.state
      (Term.leafCount σ.cfg.rules body) := by
    rw [hw]; exact termGrows σ.cfg σ.notes .root body _ _ _ learnedE.wf
  have decidedE : State.Entered walked.state decided.1 := by
    rw [hd]; exact decideClauses_entered σ.cfg _ _ _ summary.postconditions 0 _ _ grewW.2.1
  have scope : Scope σ.sem σ.Run σ.R (inputLeaves σ.sem values)
      (bindIds Ctx.empty inputs (Ident.leaves 0 types.length)) (Env.empty.extend inputs values)
      learned.1 :=
    Scope.start inputs values learned.1 learnedE.2.1 learnedE.wf
  have runs := termRuns σ laws .root body path (inputLeaves σ.sem values)
    (bindIds Ctx.empty inputs (Ident.leaves 0 types.length)) (Env.empty.extend inputs values)
    learned.1 learned.2 decided.1.values.table .nil (fun values => Process.done values)
  dsimp only at runs
  rw [← hw, Process.bind_pure] at runs
  exact runs scope decidedE.1.1 safe fun _ returned _ _ _ _ => Rests.Runs.done returned

/-- **A body that the analysis accepts is safe and satisfies its summary's guarantees, and respects
its bounds.** -/
theorem analyseSafe : AnalyseSafeStatement σ := by
  intro laws types outs summary inputs body start
  dsimp only
  intro wf defined guarantees nodup accepted recorded path values valid required facts
  have sound := analyseFrom_sound σ laws summary inputs body start wf defined accepted path values
    valid required facts
  exact ⟨sound.2.2 nodup recorded, Process.every_mono _ _
    (fun _ both => ⟨both.1, both.2 guarantees⟩) (fun _ h => h) sound.1⟩

/-- **A body that the analysis accepts is assured** on the starts that give valid inputs of which
the summary's requirements hold and where every given fact holds. -/
theorem analyseAssured : AnalyseAssuredStatement σ := by
  intro laws types outs summary inputs body defined _ accepted
  refine ⟨fun path env entry => ?_⟩
  obtain ⟨values, valid, required, facts, rfl⟩ := entry
  exact Process.every_mono _ _ (fun _ both => both.1) (fun _ h => h)
    (analyseFrom_sound σ laws summary inputs body _ (Values.empty_wf _) defined accepted path
      values valid required facts).1

/-- **A body that the analysis accepts satisfies its summary**, as a function of its inputs, where
every given fact holds. -/
theorem analyseHolds : AnalyseHoldsStatement σ := by
  intro laws types outs summary inputs body defined guarantees accepted facts values valid required
  exact Process.every_mono _ _ (fun _ both => ⟨both.1, both.2 guarantees⟩) (fun _ h => h)
    (analyseFrom_sound σ laws summary inputs body _ (Values.empty_wf _) defined accepted []
      values valid required (facts values)).1

/-- **The requirements of every operation that a run reaches hold there**, for a body that the
analysis accepts. -/
theorem analyseRequired : AnalyseRequiredStatement σ := by
  intro laws types outs summary inputs body defined accepted path values valid required facts
  exact (analyseFrom_sound σ laws summary inputs body _ (Values.empty_wf _) defined accepted path
    values valid required facts).2.1

/-- **The analysis of a definition is sound**: a body that it accepts respects its bounds, never
stops `undefined`, returns valid values of which, with the inputs, every guarantee of its summary
holds, and runs the skeleton of the analysis over its table. -/
theorem analyseSound : AnalyseSoundStatement σ := by
  intro laws conditions types outs summary inputs body
  dsimp only
  intro defined guarantees nodup accepted recorded values valid required facts
  have safe := analyseSafe σ laws summary inputs body (Values.empty σ.cfg.rules.place)
    (Values.empty_wf _) defined guarantees nodup accepted recorded [] values valid required facts
  exact ⟨safe.1, safe.2, analyseRuns σ ⟨laws.rules, conditions⟩ summary inputs body _
    (Values.empty_wf _) [] values
    (Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h) safe.2)⟩

end

end Zkc.Core.BodyAnalysis
