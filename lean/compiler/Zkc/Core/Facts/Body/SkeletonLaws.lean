module

public import Zkc.Core.Facts.Body.ValueLaws

@[expose] public section

/-!
The statements of the skeleton (`Seam/Skeleton.lean`): a run is kept when the table grows
(`SkelRunsGrowStatement`), two processes that run one skeleton followed by the same rests are the
same on permitted replies (`SkelRunsSameStatement`), and comparison is exact
(`SkelDifferStatement`).

The first two are by induction on the first run (`Skel.Runs.rec`, with the rests and the arms):
a run reads each identifier through the table, and an identifier reads one value when written
operations give one list of results and the table's values are well formed, with no condition on
the leaves. The third is by induction on the first skeleton (`Skel.rec`, with its entries and
arms), each entry of the second compared constructor by constructor.
-/

namespace Zkc.Core.BodyAnalysis

/-! ## A run is kept when the table grows -/

section
variable {D : Dialect} {Raw : Type}

/-- **A process that runs a skeleton over a table runs it over every table with its entries**:
every reading of the run is kept. -/
theorem skelRunsGrow : SkelRunsGrowStatement (D := D) (Raw := Raw) := by
  intro sem permitted Run R table table' sub path ρ mid outs skel after p runs
  refine Skel.Runs.rec
    (motive_1 := fun path ρ {_ _} skel after p _ =>
      Skel.Runs sem permitted Run R table' path ρ skel after p)
    (motive_2 := fun ρ {_ _} after values p _ =>
      Rests.Runs sem permitted Run R table' ρ after values p)
    (motive_3 := fun path ρ {_ _} arms pick p _ =>
      SkelArms.Runs sem permitted Run R table' path ρ arms pick p)
    ?ret ?effect ?guardHolds ?guardStops ?chooseTrue ?chooseFalse ?cases ?loop ?block ?attempt
    ?done ?resume ?here ?there runs
  case ret =>
    intro _ _ _ _ _ _ _ values read _ resume
    exact .ret values (ReadsAll.mono sub (fun _ _ h => h) read) resume
  case effect =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ values read _ next
    exact .effect values (ReadsAll.mono sub (fun _ _ h => h) read) next
  case guardHolds =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ v read holds _ next
    exact .guardHolds v (Reads.mono sub (fun _ _ h => h) read) holds next
  case guardStops =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ v read fails
    exact .guardStops v (Reads.mono sub (fun _ _ h => h) read) fails
  case chooseTrue =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v read holds _ first
    exact .chooseTrue v (Reads.mono sub (fun _ _ h => h) read) holds first
  case chooseFalse =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v read fails _ second
    exact .chooseFalse v (Reads.mono sub (fun _ _ h => h) read) fails second
  case cases =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v read _ _ arm next
    exact .cases v (Reads.mono sub (fun _ _ h => h) read) arm next
  case loop =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ count counted start read bodyOf _ _ iteration next
    exact .loop count (counted.mono sub (fun _ _ h => h)) start
      (ReadsAll.mono sub (fun _ _ h => h) read) bodyOf iteration next
  case block =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ inner
    exact .block inner
  case attempt =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ bodyOf _ _ _ inner next
    exact .attempt bodyOf inner next
  case done =>
    intro _ _ values
    exact .done values
  case resume =>
    intro _ _ _ _ _ _ _ _ _ _ next
    exact .resume next
  case here =>
    intro _ _ _ _ _ _ _ _ _ _ _ inner
    exact .here inner
  case there =>
    intro _ _ _ _ _ _ _ _ _ _ _ inner
    exact .there inner

end

/-! ## One skeleton, one process -/

section
variable {D : Dialect} {Raw : Type}

/-- **Two processes that run one skeleton, followed by the same rests, over one table whose values
are well formed, from the same path and the same leaves, are the same on permitted replies.** By
induction on the first run: each identifier reads one value, so both read the same operands and
the same condition, and so run the same entry; what follows each is the same from every result
that the first can return. Nothing is asked of the leaves. -/
theorem skelRunsSame : SkelRunsSameStatement (D := D) (Raw := Raw) := by
  intro sem permitted Run R functional v wf path ρ mid outs skel after p q first second
  revert q second
  refine Skel.Runs.rec
    (motive_1 := fun path ρ {_ _} skel after p _ => ∀ q,
      Skel.Runs sem permitted Run R v.table path ρ skel after q → Process.SameWhen permitted p q)
    (motive_2 := fun ρ {_ _} after values p _ => ∀ q,
      Rests.Runs sem permitted Run R v.table ρ after values q → Process.SameWhen permitted p q)
    (motive_3 := fun path ρ {_ _} arms pick p _ => ∀ q,
      SkelArms.Runs sem permitted Run R v.table path ρ arms pick q →
        Process.SameWhen permitted p q)
    ?ret ?effect ?guardHolds ?guardStops ?chooseTrue ?chooseFalse ?cases ?loop ?block ?attempt
    ?done ?resume ?here ?there first
  case ret =>
    intro _ _ _ _ _ _ _ values read _ same q second
    cases second with
    | ret values' read' resume' =>
        obtain rfl := sem.dyns_injective (ReadsAll.functional functional wf read read')
        exact same q resume'
  case effect =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ values read _ same q second
    cases second with
    | effect values' read' next' =>
        obtain rfl := sem.dyns_injective (ReadsAll.functional functional wf read read')
        exact Process.SameWhen.bind (.refl _) (Process.every_canReturn _)
          fun returned returns => same returned returns _ (next' returned returns)
  case guardHolds =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ v read holds _ same q second
    cases second with
    | guardHolds v' read' holds' next' => exact same q next'
    | guardStops v' read' fails' =>
        obtain rfl := sem.dyn_inj (Reads.functional functional wf read read')
        rw [holds] at fails'
        cases fails'
  case guardStops =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ v read fails q second
    cases second with
    | guardHolds v' read' holds' next' =>
        obtain rfl := sem.dyn_inj (Reads.functional functional wf read read')
        rw [fails] at holds'
        cases holds'
    | guardStops v' read' fails' => exact .refl _
  case chooseTrue =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v read holds _ same q second
    cases second with
    | chooseTrue v' read' holds' first' => exact same q first'
    | chooseFalse v' read' fails' second' =>
        obtain rfl := sem.dyn_inj (Reads.functional functional wf read read')
        rw [holds] at fails'
        cases fails'
  case chooseFalse =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v read fails _ same q second
    cases second with
    | chooseTrue v' read' holds' first' =>
        obtain rfl := sem.dyn_inj (Reads.functional functional wf read read')
        rw [fails] at holds'
        cases holds'
    | chooseFalse v' read' fails' second' => exact same q second'
  case cases =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v read _ _ sameArm sameNext q second
    cases second with
    | cases v' read' arm' next' =>
        obtain rfl := sem.dyn_inj (Reads.functional functional wf read read')
        have armsSame := sameArm _ arm'
        exact Process.SameWhen.bind armsSame (Process.every_canReturn _)
          fun returned returns => sameNext returned returns _
            (next' returned (armsSame.canReturn returns))
  case loop =>
    intro _ _ _ _ carried each _ _ _ _ _ _ _ _ _ _ count counted start read bodyOf _ _
      sameIteration sameNext q second
    cases second with
    | loop count' counted' start' read' bodyOf' iteration' next' =>
        obtain rfl := Count.Is.unique functional wf counted counted'
        obtain rfl := sem.dyns_injective (ReadsAll.functional functional wf read read')
        have stepSame : ∀ i (state : sem.LoopState carried each), i < count →
            (Process.iterate i (sem.stepOf bodyOf) 0 (start, HList.empties each)).CanReturn
              permitted state →
            (Process.iterate i (sem.stepOf bodyOf') 0 (start, HList.empties each)).CanReturn
              permitted state →
            Process.SameWhen permitted (sem.stepOf bodyOf i state) (sem.stepOf bodyOf' i state) :=
          fun i state below returns returns' =>
            Process.SameWhen.bind (sameIteration i state below returns _
                (iteration' i state below returns'))
              (Process.every_true _ _) fun _ _ => .refl _
        have iterationsSame := Process.SameWhen.iterate_below
          (fun i state =>
            (Process.iterate i (sem.stepOf bodyOf) 0 (start, HList.empties each)).CanReturn
                permitted state ∧
              (Process.iterate i (sem.stepOf bodyOf') 0 (start, HList.empties each)).CanReturn
                permitted state)
          count (fun i state below reached => stepSame i state below reached.1 reached.2)
          (fun i state below reached => Process.every_mono _ permitted
            (fun after returns =>
              ⟨Process.CanReturn.iterate_succ reached.1 (by rw [Nat.zero_add]; exact returns),
                Process.CanReturn.iterate_succ reached.2 (by
                  rw [Nat.zero_add]
                  exact (stepSame i state below reached.1 reached.2).canReturn returns)⟩)
            (fun _ h => h) (Process.every_canReturn _))
          count 0 (start, HList.empties each) (Nat.le_of_eq (Nat.zero_add _)) ⟨.done _, .done _⟩
        exact Process.SameWhen.bind iterationsSame (Process.every_canReturn _)
          fun final returns => sameNext final returns _
            (next' final (iterationsSame.canReturn returns))
  case block =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ same q second
    cases second with
    | block inner' => exact same q inner'
  case attempt =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ bodyOf _ _ _ sameInner sameNext q second
    cases second with
    | attempt bodyOf' inner' next' =>
        refine Process.SameWhen.bind (.refl _) (Process.every_canReturn _) fun number began => ?_
        have bodySame := sameInner number began _ (inner' number began)
        refine Process.SameWhen.bind bodySame (Process.every_canReturn _) fun returned ran => ?_
        refine Process.SameWhen.bind (.refl _) (Process.every_canReturn _) fun ended settled => ?_
        cases ended
        exact sameNext number returned began ran settled _
          (next' number returned began (bodySame.canReturn ran) settled)
  case done =>
    intro _ _ values q second
    cases second
    exact .refl _
  case resume =>
    intro _ _ _ _ _ _ _ _ _ _ same q second
    cases second with
    | resume next' => exact same q next'
  case here =>
    intro _ _ _ _ _ _ _ _ _ _ _ same q second
    cases second with
    | here inner' => exact same q inner'
  case there =>
    intro _ _ _ _ _ _ _ _ _ _ _ same q second
    cases second with
    | there inner' => exact same q inner'

end

/-! ## Comparison is exact -/

section
variable {D : Dialect} (checks : SkelRules D)

/-- Two counts that comparison finds the same are the same. -/
theorem Count.eq_of_same {w : D.Who} :
    ∀ {c c' : Count D w}, Count.same checks c c' = true → c = c'
  | .fixed n, .fixed n', same => by
      simp only [Count.same, decide_eq_true_eq] at same
      rw [same]
  | .value (t := t) id ok, .value (t := t') id' ok', same => by
      simp only [Count.same] at same
      split at same
      · next sameType _ =>
          subst sameType
          simp only [decide_eq_true_eq] at same
          subst same
          rfl
      · cases same
  | .fixed _, .value .., same => by cases same
  | .value .., .fixed _, same => by cases same

/-- Comparison finds a count the same as itself. -/
theorem Count.same_self {w : D.Who} : ∀ c : Count D w, Count.same checks c c = true
  | .fixed n => by
      simp only [Count.same]
      first | exact decide_eq_true trivial | exact decide_eq_true rfl
  | .value (t := t) id ok => by
      simp only [Count.same]
      generalize checks.sameTy t t = d
      cases d with
      | isFalse no => exact absurd rfl no
      | isTrue _ => first | exact decide_eq_true trivial | exact decide_eq_true rfl

/-- **A skeleton differs from itself nowhere**, for decisions that find an operation the same as
itself: by induction on the skeleton, with its entries and arms. -/
theorem Skel.differ_self
    (reflexive : ∀ {ins res : List D.Ty} (o : D.Op ins res), checks.sameOp o o = true)
    (at_ : Option Key) {outs : List D.Ty} (s : Skel D outs) : Skel.differ checks at_ s s = [] := by
  revert at_
  refine Skel.rec
    (motive_1 := fun _ s => ∀ at_, Skel.differ checks at_ s s = [])
    (motive_2 := fun kept => ∀ key, Kept.differ checks key kept kept = some [])
    (motive_3 := fun _ _ arms => ∀ key, SkelArms.differ checks key arms arms = some [])
    ?ret ?step ?effect ?guard ?choose ?cases ?loop ?block ?attempt ?nil ?cons s
  case ret =>
    intro _ exit at_
    simp only [Skel.differ, ↓reduceIte]
  case step =>
    intro _ key kept rest sameKept sameRest at_
    simp only [Skel.differ, ↓reduceIte, sameKept key, sameRest at_, List.nil_append]
  case effect =>
    intro ins _ o operands results key
    simp only [Kept.differ]
    generalize checks.sameTys ins ins = d
    cases d with
    | isFalse no => exact absurd rfl no
    | isTrue same =>
        simp only [cast_eq, reflexive o, and_self, ↓reduceIte]
  case guard =>
    intro t w condition ok why key
    simp only [Kept.differ]
    generalize checks.sameWho w w = dw
    generalize checks.sameTy t t = dt
    cases dw with
    | isFalse no => exact absurd rfl no
    | isTrue _ =>
        cases dt with
        | isFalse no => exact absurd rfl no
        | isTrue _ =>
            simp only [and_self, ↓reduceIte]
  case choose =>
    intro mid t w condition ok onTrue onFalse sameTrue sameFalse key
    simp only [Kept.differ]
    generalize checks.sameWho w w = dw
    generalize checks.sameTy t t = dt
    generalize checks.sameTys mid mid = dm
    cases dw with
    | isFalse no => exact absurd rfl no
    | isTrue _ =>
        cases dt with
        | isFalse no => exact absurd rfl no
        | isTrue _ =>
            cases dm with
            | isFalse no => exact absurd rfl no
            | isTrue _ =>
                simp only [↓reduceIte, sameTrue (some key), sameFalse (some key), List.append_nil]
  case cases =>
    intro mid t payloads w subject ok arms results sameArms key
    simp only [Kept.differ]
    generalize checks.sameWho w w = dw
    generalize checks.sameTy t t = dt
    generalize checks.sameTys mid mid = dm
    generalize checks.sameTys payloads payloads = dp
    cases dw with
    | isFalse no => exact absurd rfl no
    | isTrue _ =>
        cases dt with
        | isFalse no => exact absurd rfl no
        | isTrue _ =>
            cases dm with
            | isFalse no => exact absurd rfl no
            | isTrue _ =>
                cases dp with
                | isFalse no => exact absurd rfl no
                | isTrue _ =>
                    simp only [and_self, ↓reduceIte, sameArms key]
  case loop =>
    intro carried each w times initial inputs body results sameBody key
    simp only [Kept.differ]
    generalize checks.sameWho w w = dw
    generalize checks.sameTys carried carried = dc
    generalize checks.sameTys each each = de
    cases dw with
    | isFalse no => exact absurd rfl no
    | isTrue _ =>
        cases dc with
        | isFalse no => exact absurd rfl no
        | isTrue _ =>
            cases de with
            | isFalse no => exact absurd rfl no
            | isTrue _ =>
                simp only [cast_eq, Count.same_self checks times, and_self, ↓reduceIte,
                  sameBody (some key)]
  case block =>
    intro mid number body sameBody key
    simp only [Kept.differ]
    generalize checks.sameTys mid mid = dm
    cases dm with
    | isFalse no => exact absurd rfl no
    | isTrue _ =>
        simp only [↓reduceIte, sameBody (some key), List.map_nil]
  case attempt =>
    intro mid w input body results sameBody key
    simp only [Kept.differ]
    generalize checks.sameWho w w = dw
    generalize checks.sameTys mid mid = dm
    cases dw with
    | isFalse no => exact absurd rfl no
    | isTrue _ =>
        cases dm with
        | isFalse no => exact absurd rfl no
        | isTrue _ =>
            simp only [and_self, ↓reduceIte, sameBody (some key)]
  case nil =>
    intro _ key
    rfl
  case cons =>
    intro _ _ _ input arm rest sameArm sameRest key
    simp only [SkelArms.differ, ↓reduceIte, sameRest key, sameArm (some key), List.append_nil,
      Option.map_some]

/-- **Two skeletons that differ nowhere are equal**, for decisions under which operations found
the same are the same: by induction on the first skeleton, with its entries and arms, each entry
of the second taken constructor by constructor; types and performers are decided by equality. -/
theorem Skel.eq_of_differ (lawful : checks.Lawful) (at_ : Option Key) {outs : List D.Ty}
    (s s' : Skel D outs) : Skel.differ checks at_ s s' = [] → s = s' := by
  revert at_ s'
  refine Skel.rec
    (motive_1 := fun outs s => ∀ at_ (s' : Skel D outs), Skel.differ checks at_ s s' = [] → s = s')
    (motive_2 := fun kept => ∀ key kept',
      Kept.differ checks key kept kept' = some [] → kept = kept')
    (motive_3 := fun mid payloads arms => ∀ key (arms' : SkelArms D mid payloads),
      SkelArms.differ checks key arms arms' = some [] → arms = arms')
    ?ret ?step ?effect ?guard ?choose ?cases ?loop ?block ?attempt ?nil ?cons s
  case ret =>
    intro _ exit at_ s' differs
    cases s' with
    | ret exit' =>
        simp only [Skel.differ] at differs
        split at differs
        · next same => rw [same]
        · cases differs
    | step key' kept' rest' => cases differs
  case step =>
    intro _ key kept rest sameKept sameRest at_ s' differs
    cases s' with
    | ret exit' => cases differs
    | step key' kept' rest' =>
        simp only [Skel.differ] at differs
        split at differs
        · next sameKey =>
            subst sameKey
            split at differs
            · next found entries =>
                obtain ⟨none, others⟩ := List.append_eq_nil_iff.mp differs
                subst none
                rw [sameKept key kept' entries, sameRest at_ rest' others]
            · cases differs
        · cases differs
  case effect =>
    intro ins res o operands results key kept' differs
    cases kept'
    case effect ins' res' o' operands' results' =>
      simp only [Kept.differ] at differs
      generalize checks.sameTys ins ins' = d at differs
      cases d with
      | isFalse _ => cases differs
      | isTrue same =>
          subst same
          dsimp only at differs
          split at differs
          · next found =>
              obtain ⟨op, rfl, rfl⟩ := found
              rw [cast_eq] at op
              obtain ⟨rfl, same⟩ := lawful o o' op
              cases eq_of_heq same
              rfl
          · cases differs
    all_goals cases differs
  case guard =>
    intro t w condition ok why key kept' differs
    cases kept'
    case guard t' w' condition' ok' why' =>
      simp only [Kept.differ] at differs
      generalize checks.sameWho w w' = dw at differs
      generalize checks.sameTy t t' = dt at differs
      cases dw with
      | isFalse _ => cases differs
      | isTrue sameWho =>
          cases dt with
          | isFalse _ => cases differs
          | isTrue sameTy =>
              subst sameWho sameTy
              dsimp only at differs
              split at differs
              · next found =>
                  obtain ⟨rfl, rfl⟩ := found
                  rfl
              · cases differs
    all_goals cases differs
  case choose =>
    intro mid t w condition ok onTrue onFalse sameTrue sameFalse key kept' differs
    cases kept'
    case choose mid' t' w' condition' ok' onTrue' onFalse' =>
      simp only [Kept.differ] at differs
      generalize checks.sameWho w w' = dw at differs
      generalize checks.sameTy t t' = dt at differs
      generalize checks.sameTys mid mid' = dm at differs
      cases dw with
      | isFalse _ => cases differs
      | isTrue sameWho =>
          cases dt with
          | isFalse _ => cases differs
          | isTrue sameTy =>
              cases dm with
              | isFalse _ => cases differs
              | isTrue sameMid =>
                  subst sameWho sameTy sameMid
                  dsimp only at differs
                  split at differs
                  · next sameCondition =>
                      subst sameCondition
                      obtain ⟨none, others⟩ := List.append_eq_nil_iff.mp (Option.some.inj differs)
                      rw [sameTrue (some key) onTrue' none, sameFalse (some key) onFalse' others]
                  · cases differs
    all_goals cases differs
  case cases =>
    intro mid t payloads w subject ok arms results sameArms key kept' differs
    cases kept'
    case cases mid' t' payloads' w' subject' ok' arms' results' =>
      simp only [Kept.differ] at differs
      generalize checks.sameWho w w' = dw at differs
      generalize checks.sameTy t t' = dt at differs
      generalize checks.sameTys mid mid' = dm at differs
      generalize checks.sameTys payloads payloads' = dp at differs
      cases dw with
      | isFalse _ => cases differs
      | isTrue sameWho =>
          cases dt with
          | isFalse _ => cases differs
          | isTrue sameTy =>
              cases dm with
              | isFalse _ => cases differs
              | isTrue sameMid =>
                  cases dp with
                  | isFalse _ => cases differs
                  | isTrue samePayloads =>
                      subst sameWho sameTy sameMid samePayloads
                      dsimp only at differs
                      split at differs
                      · next found =>
                          obtain ⟨rfl, rfl⟩ := found
                          rw [sameArms key arms' differs]
                      · cases differs
    all_goals cases differs
  case loop =>
    intro carried each w times initial inputs body results sameBody key kept' differs
    cases kept'
    case loop carried' each' w' times' initial' inputs' body' results' =>
      simp only [Kept.differ] at differs
      generalize checks.sameWho w w' = dw at differs
      generalize checks.sameTys carried carried' = dc at differs
      generalize checks.sameTys each each' = de at differs
      cases dw with
      | isFalse _ => cases differs
      | isTrue sameWho =>
          cases dc with
          | isFalse _ => cases differs
          | isTrue sameCarried =>
              cases de with
              | isFalse _ => cases differs
              | isTrue sameEach =>
                  subst sameWho sameCarried sameEach
                  dsimp only at differs
                  split at differs
                  · next found =>
                      obtain ⟨sameTimes, rfl, rfl, rfl⟩ := found
                      rw [cast_eq] at sameTimes
                      rw [Count.eq_of_same checks sameTimes,
                        sameBody (some key) body' (Option.some.inj differs)]
                  · cases differs
    all_goals cases differs
  case block =>
    intro mid number body sameBody key kept' differs
    cases kept'
    case block mid' number' body' =>
      simp only [Kept.differ] at differs
      generalize checks.sameTys mid mid' = dm at differs
      cases dm with
      | isFalse _ => cases differs
      | isTrue sameMid =>
          subst sameMid
          dsimp only at differs
          split at differs
          · next sameNumber =>
              subst sameNumber
              rw [sameBody (some key) body' (List.map_eq_nil_iff.mp (Option.some.inj differs))]
          · cases differs
    all_goals cases differs
  case attempt =>
    intro mid w input body results sameBody key kept' differs
    cases kept'
    case attempt mid' w' input' body' results' =>
      simp only [Kept.differ] at differs
      generalize checks.sameWho w w' = dw at differs
      generalize checks.sameTys mid mid' = dm at differs
      cases dw with
      | isFalse _ => cases differs
      | isTrue sameWho =>
          cases dm with
          | isFalse _ => cases differs
          | isTrue sameMid =>
              subst sameWho sameMid
              dsimp only at differs
              split at differs
              · next found =>
                  obtain ⟨rfl, rfl⟩ := found
                  rw [sameBody (some key) body' (Option.some.inj differs)]
              · cases differs
    all_goals cases differs
  case nil =>
    intro _ key arms' _
    cases arms'
    rfl
  case cons =>
    intro _ _ _ input arm rest sameArm sameRest key arms' differs
    cases arms' with
    | cons input' arm' rest' =>
        simp only [SkelArms.differ] at differs
        split at differs
        · next sameInput =>
            subst sameInput
            obtain ⟨found, others, joined⟩ := Option.map_eq_some_iff.mp differs
            obtain ⟨none, rfl⟩ := List.append_eq_nil_iff.mp joined
            rw [sameArm (some key) arm' none, sameRest key rest' others]
        · cases differs

end

/-- **Comparison is exact**: for decisions that are sound and reflexive, two skeletons of the same
types differ nowhere exactly when they are equal. -/
theorem skelDiffer {D : Dialect} : SkelDifferStatement (D := D) := by
  intro checks exact at_ outs s s'
  constructor
  · exact Skel.eq_of_differ checks exact.1 at_ s s'
  · intro same
    subst same
    exact Skel.differ_self checks exact.2 at_ s

end Zkc.Core.BodyAnalysis
