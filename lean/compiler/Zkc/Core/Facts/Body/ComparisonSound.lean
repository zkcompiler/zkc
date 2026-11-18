module

public import Zkc.Core.Facts.Body.AnalysisSound
public import Zkc.Core.Facts.Body.SkeletonLaws

@[expose] public section

/-!
Validation by comparison (`CompareSameStatement`) and the statements about following
(`FollowSafeStatement`, `FollowsAssuredStatement`, `FollowsSoundStatement`).

Validation by comparison: the second body is walked from the first's final table, its inputs on
the same leaves; when the two skeletons differ nowhere they are equal (`Skel.eq_of_differ`); the
first body's process runs its skeleton over the first table, so over the second, which has its
entries (`skelRunsGrow`); the second body's process runs the same skeleton over the second table;
and two processes that run one skeleton from the same leaves over one table whose values are well
formed are the same on permitted replies (`skelRunsSame`). Both safeties are hypotheses, since a
skeleton is run only by a process that never stops `undefined`. A body that follows another is the
analysis of the second, from the first's final table, in the setting of the second definition
(`Setting.second`).
-/

namespace Zkc.Core.BodyAnalysis

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

omit [DecidableEq Raw] in
/-- The laws of a setting are those of the setting of a second definition: only the definition's
key and its annotations differ. -/
theorem Setting.Lawful.second {σ : Setting D Raw} (laws : σ.Lawful) (definition' : Key)
    (notes' : Annotations Raw) : (σ.second definition' notes').Lawful :=
  ⟨laws.rules, laws.lemmas, laws.requires⟩

/-- **Validation by comparison**: when the skeletons of two bodies differ nowhere and neither body
stops `undefined`, the two have the same process on permitted replies, on every input. -/
theorem compareSame : CompareSameStatement σ := by
  intro laws checks definition' notes' types outs summary inputs inputs' body body' lawful same path
    values safe safe'
  have firstGrew := analyseFrom_grew σ.cfg σ.notes summary inputs body
    (Values.empty σ.cfg.rules.place) (Values.empty_wf _)
  have runs := analyseRuns σ laws summary inputs body (Values.empty σ.cfg.rules.place)
    (Values.empty_wf _) path values safe
  have equal : (analyseFrom σ.cfg σ.notes summary inputs body
        (Values.empty σ.cfg.rules.place)).skel =
      (analyseFrom { σ.cfg with definition := definition' } notes' summary inputs' body'
        (analyseFrom σ.cfg σ.notes summary inputs body
          (Values.empty σ.cfg.rules.place)).state.values).skel :=
    Skel.eq_of_differ checks lawful none _ _ same
  generalize analyseFrom σ.cfg σ.notes summary inputs body (Values.empty σ.cfg.rules.place) = first
    at firstGrew runs equal
  have secondGrew := analyseFrom_grew { σ.cfg with definition := definition' } notes' summary
    inputs' body' first.state.values firstGrew.2
  have runs' := analyseRuns (σ.second definition' notes') laws summary inputs' body'
    first.state.values firstGrew.2 path values safe'
  have grown := skelRunsGrow σ.sem σ.permitted σ.Run σ.R _ _ secondGrew.1 path _ _ .nil _ runs
  rw [equal] at grown
  exact skelRunsSame σ.sem σ.permitted σ.Run σ.R laws.1.functional _ secondGrew.2 path _ _ .nil _ _
    grown runs'

theorem follows_eq (cfg : Config D Raw) (checks : SkelRules D) (definition' : Key)
    (notes notes' : Annotations Raw) {types outs : List D.Ty} (summary : Contract Raw)
    (inputs inputs' : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs) :
    letI := checks.sameTy
    follows cfg checks definition' notes notes' summary inputs inputs' body body' =
      ((checkDefinition cfg.assertions cfg.lemmas inputs body notes summary).isOk &&
       ((checkDefinition cfg.assertions cfg.lemmas inputs' body' notes' summary).isOk &&
        (let both := analyseBoth cfg definition' notes notes' summary inputs inputs' body body'
         (Skel.differ checks none both.1.skel both.2.skel).isEmpty && both.2.state.refusals.isEmpty))) := by
  letI := checks.sameTy
  cases x : checkDefinition cfg.assertions cfg.lemmas inputs body notes summary with
  | error _ => rw [follows, followChecked, x]; rfl
  | ok u =>
    cases y : checkDefinition cfg.assertions cfg.lemmas inputs' body' notes' summary with
    | error _ => rw [follows, followChecked, x, y]; rfl
    | ok v =>
      rw [follows, followChecked, x, y]
      generalize analyseBoth cfg definition' notes notes' summary inputs inputs' body body' = pair
      cases pair with | mk source target =>
        cases h : (Skel.differ checks none source.skel target.skel).isEmpty && target.state.refusals.isEmpty <;>
          simp [h, Except.mapError, bind, Except.bind, Except.isOk, Except.toBool] <;> rfl

/-- **A body that follows another is safe**: its walk, from the first's final table, refuses
nothing, so in the setting of the second definition it is a body that the analysis accepts. -/
theorem followSafe : FollowSafeStatement σ := by
  intro laws checks definition' notes' types outs summary inputs inputs' body body'
  dsimp only
  intro followed defined guarantees nodup recorded path values valid required facts
  simp only [follows_eq, Bool.and_eq_true, List.isEmpty_iff] at followed
  have firstGrew := analyseFrom_grew σ.cfg σ.notes summary inputs body
    (Values.empty σ.cfg.rules.place) (Values.empty_wf _)
  exact analyseSafe (σ.second definition' notes') (laws.second definition' notes') summary inputs'
    body' _ firstGrew.2 defined
    guarantees nodup followed.2.2.2 recorded path values valid required facts

/-- **A body that follows a safe body is safe and means the same**, however the first is known to
be safe. -/
theorem followsAssured : FollowsAssuredStatement σ := by
  intro laws conditions checks definition' notes' types outs summary inputs inputs' body body'
  dsimp only
  intro lawful followed defined guarantees nodup recorded path values valid required facts safe
  have second := followSafe σ laws checks definition' notes' summary inputs inputs' body body'
    followed defined guarantees nodup recorded path values valid required facts
  have parts := followed
  simp only [follows_eq, Bool.and_eq_true, List.isEmpty_iff] at parts
  exact ⟨second.1, second.2, compareSame σ ⟨laws.rules, conditions⟩ checks definition' notes'
    summary inputs inputs' body body' lawful parts.2.2.1 path values safe
    (Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h) second.2)⟩

/-- **A body that follows an accepted body is safe and means the same**: the first is safe because
the analysis accepts it (`analyseFrom_sound`, which needs neither its distinct addresses nor its
bounds for that). -/
theorem followsSound : FollowsSoundStatement σ := by
  intro laws conditions checks definition' notes' types outs summary inputs inputs' body body'
  dsimp only
  intro lawful defined defined' guarantees _ nodup' accepted followed recorded path values valid
    required facts facts'
  have first := analyseFrom_sound σ laws summary inputs body (Values.empty σ.cfg.rules.place)
    (Values.empty_wf _) defined accepted path values valid required facts
  exact followsAssured σ laws conditions checks definition' notes' summary inputs inputs' body body'
    lawful followed defined' guarantees nodup' recorded path values valid required facts'
    (Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h) first.1)

#print axioms compareSame
#print axioms followSafe
#print axioms followsAssured
#print axioms followsSound

end

end Zkc.Core.BodyAnalysis
