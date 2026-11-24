module

public import Zkc.Core.Transform.FunctionAdmission

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {hs : List (FnHeader V)} {hdr : FnHeader V}

/-- A successful function comparison exposes the candidate verdict under the translated header. -/
theorem FunctionContracts.checkedPair (contracts : FunctionContracts hs)
    (source candidate : TypedFn V hs hdr)
    {lemmas notes notes' bs} (accepted : contracts.compareFunctions source candidate lemmas notes notes' = .ok bs) :
    ∃ summary, HeaderContracts.translate hdr.ins hdr.outs hdr.summary = some summary ∧
      followChecked (contracts.config hdr.key lemmas hdr.summary.ensures) (localRules hs).skel hdr.key notes notes' summary
        source.inputs candidate.inputs source.body candidate.body = .ok bs := by
  cases h : readHeader hdr with
  | error c => simp [FunctionContracts.compareFunctions, h, Except.mapError, bind, Except.bind] at accepted
  | ok summary =>
    refine ⟨summary.val, summary.property, ?_⟩
    have cert : (⟨true, (HeaderContracts.body_check contracts summary).symm⟩ :
        {b : Bool // b = Contract.check (D := localDialect V hs)
          (contracts.config hdr.key lemmas hdr.summary.ensures).assertions summary.val hdr.ins hdr.outs}) = ⟨_, rfl⟩ :=
      Subtype.ext (HeaderContracts.body_check contracts summary).symm
    simp only [FunctionContracts.compareFunctions, h, Except.mapError, bind, Except.bind] at accepted
    rw [cert] at accepted
    cases checked : followChecked (contracts.config hdr.key lemmas hdr.summary.ensures) (localRules hs).skel hdr.key notes notes' summary.val
        source.inputs candidate.inputs source.body candidate.body <;> simp_all

/-- A safe source may have obtained its safety from any producer. Comparison needs
semantic evidence for the candidate's annotations at the sites its executions reach. -/
theorem FunctionContracts.compareAnnotated_assured (contracts : FunctionContracts hs)
    (source candidate : TypedFn V hs hdr) (safe : source.Safe) {lemmas sourceNotes candidateNotes bounds}
    (evidence : contracts.AnnotationEvidence candidate lemmas candidateNotes)
    (accepted : contracts.compareFunctions source candidate lemmas sourceNotes candidateNotes = .ok bounds) :
    candidate.Assured bounds ∧ source.SameAs candidate := by
  obtain ⟨summary,translated,checked⟩ := contracts.checkedPair source candidate accepted
  have distinct : (Term.addresses [] candidate.body).Nodup := by
    have h := candidate.conditions.distinct
    simp only [Term.Distinct, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  let cfg := contracts.config hdr.key lemmas hdr.summary.ensures
  let checks := (localRules hs).skel
  have followed : follows cfg checks hdr.key sourceNotes candidateNotes summary source.inputs candidate.inputs
      source.body candidate.body = true := by
    change (followChecked _ _ _ _ _ _ _ _ _ _).isOk = true
    rw [checked]; rfl
  have listEq := followChecked_bounds cfg checks hdr.key _ _ _ _ _ _ _ checked
  have run (M : Model V) (table : FnTable M hs) (callees : Callees M table) (F : List (Place × Nat))
      (recorded : ∀ p b, (p,b) ∈ F → p.definition = hdr.key → p.role = none → (p,b) ∈ bounds)
      (ins : HList M.Val hdr.ins) (valid : ∀ v ∈ (localSem M hs table).dyns ins, ValidDyn M v)
      (required : FnHeader.Required M table hdr ins) :
      source.meaning M table ins = candidate.meaning M table ins ∧
      candidate.body.EveryLoop (localSem M hs table) (fun _ _ => True) (Annotation.Bounded ⟨F⟩ hdr.key none)
        [] [] (Env.empty.extend candidate.inputs ins) := by
    let σ := contracts.setting M table hdr.key lemmas sourceNotes F hdr.summary.ensures
    have parts := translated
    simp only [HeaderContracts.translate, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at parts
    obtain ⟨_,pre,_,_,same⟩ := parts
    have req : ∀ e ∈ summary.requires, e.Holds σ.Runs σ.R (σ.sem.dyns ins) := by
      rw [←Option.some.inj same]
      exact (HeaderContracts.clauses_exact M table (ArgumentsMatch.ofValues (sem := localSem M hs table) ins valid)
        contracts.distinct pre).mpr required
    have conditions : ConditionsRead σ.sem σ.R := by
      intro w t ok v
      change t = .bool at ok
      subst t
      rfl
    have sourceSafe := safe M table callees ins valid required
    have quiet : σ.NotUndefined (source.body.denote σ.sem [] (Env.empty.extend source.inputs ins)) := by
      exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h) sourceSafe
    obtain ⟨loops,_,sameRun⟩ := follows_checked_assured σ (contracts.settingLawful M table _ _ _ _ callees (evidence.laws M table callees) hdr.summary.ensures)
      conditions (contracts.readerLawful M table _ _ _ _ callees hdr.summary.ensures) checks hdr.key candidateNotes summary source.inputs candidate.inputs
      source.body candidate.body (Rules.skel_lawful (localRules_lawful contracts.distinct))
      followed distinct (fun p b mem defn role => List.mem_reverse.mp (listEq ▸ recorded p b mem defn role))
      [] ins valid req (evidence.facts M table callees ins (((localSem M hs table).dyns_valid_iff ins).mp valid) required) quiet
    exact ⟨sameRun.eq_of_noSig,loops⟩
  have eq : source.SameAs candidate := fun M table callees ins valid req =>
    (run M table callees [] (by simp) ins (((localSem M hs table).dyns_valid_iff ins).mpr valid) req).1
  refine ⟨⟨?_,?_⟩,eq⟩
  · intro M table callees ins valid required
    rw [←eq M table callees ins (((localSem M hs table).dyns_valid_iff ins).mp valid) required]
    exact safe M table callees ins valid required
  · intro M table callees F recorded ins valid req
    exact (run M table callees F recorded ins (((localSem M hs table).dyns_valid_iff ins).mpr valid) req).2

/-- An unannotated checked replacement is assured and means the same as its safe source. -/
theorem FunctionContracts.compareFunctions_assured (contracts : FunctionContracts hs)
    (source candidate : TypedFn V hs hdr) (safe : source.Safe) {bounds}
    (accepted : contracts.compareFunctions source candidate = .ok bounds) :
    candidate.Assured bounds ∧ source.SameAs candidate :=
  contracts.compareAnnotated_assured source candidate safe (contracts.emptyEvidence candidate) accepted

end Zkc.Core.BodyAnalysis
