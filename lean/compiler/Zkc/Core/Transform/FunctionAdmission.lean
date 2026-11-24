module

public import Zkc.Core.Transform.FunctionChecking
public import Zkc.Core.Facts.Contracts.FunctionSetting
public import Zkc.Core.Facts.Body.Verdicts
public import Zkc.Core.Facts.Body.Traversal

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {V : Vocabulary} {hs : List (FnHeader V)} {hdr : FnHeader V}

theorem FunctionContracts.checkedBody (contracts : FunctionContracts hs) (f : TypedFn V hs hdr)
    {lemmas notes bs} (accepted : contracts.checkFunction f lemmas notes = .ok bs) :
    ∃ summary, HeaderContracts.translate hdr.ins hdr.outs hdr.summary = some summary ∧
      checkFacts (contracts.config hdr.key lemmas hdr.summary.ensures) notes summary f.inputs f.body = .ok bs := by
  cases h : readHeader hdr with
  | error c => simp [FunctionContracts.checkFunction, h, Except.mapError, bind, Except.bind] at accepted
  | ok summary =>
    refine ⟨summary.val, summary.property, ?_⟩
    have cert : (⟨true, (HeaderContracts.body_check contracts summary).symm⟩ :
        {b : Bool // b = Contract.check (D := localDialect V hs)
          (contracts.config hdr.key lemmas hdr.summary.ensures).assertions summary.val hdr.ins hdr.outs}) = ⟨_, rfl⟩ :=
      Subtype.ext (HeaderContracts.body_check contracts summary).symm
    simp only [FunctionContracts.checkFunction, h, Except.mapError, bind, Except.bind] at accepted
    rw [cert] at accepted
    cases checked : checkFacts (contracts.config hdr.key lemmas hdr.summary.ensures) notes summary.val f.inputs f.body <;> simp_all

/-- Evidence a producer supplies for the annotations of one typed function. Inputs range
over legal calls, and a given fact is required only on executions that reach its site. -/
structure FunctionContracts.AnnotationEvidence (catalog : FunctionContracts hs) (f : TypedFn V hs hdr)
    (lemmas : List (Lemma V.Ty (LocalRaw V))) (notes : Annotations (LocalRaw V)) : Prop where
  laws : ∀ (M : Model V) (table : FnTable M hs), Callees M table → ∀ l ∈ lemmas,
    l.Valid (HeaderContracts.Runs M table) (localReading M) (TypedValue (localSem M hs table) (ValidDyn M))
  facts : ∀ (M : Model V) (table : FnTable M hs), Callees M table → ∀ ins : HList M.Val hdr.ins,
    ins.All M.Valid → FnHeader.Required M table hdr ins →
    Term.EveryFact (catalog.setting M table hdr.key lemmas notes [] hdr.summary.ensures)
      .root f.body [] (Env.empty.extend f.inputs ins)

/-- A body with no supplied facts only needs proofs of its registered lemmas. -/
theorem FunctionContracts.evidenceOfLaws (catalog : FunctionContracts hs) (f : TypedFn V hs hdr)
    {lemmas : List (Lemma V.Ty (LocalRaw V))} {notes : Annotations (LocalRaw V)}
    (internal : notes.any (fun e : AnnotationSite × Annotation (LocalRaw V) => e.2.isGiven) = false)
    (valid : ∀ (M : Model V) (table : FnTable M hs), Callees M table → ∀ l ∈ lemmas,
      l.Valid (HeaderContracts.Runs M table) (localReading M) (TypedValue (localSem M hs table) (ValidDyn M))) :
    catalog.AnnotationEvidence f lemmas notes :=
  ⟨valid, fun _ _ _ _ _ _ => everyFact_of_noGiven _ internal _ _ _⟩

/-- An unannotated function has no premises for an external producer. -/
theorem FunctionContracts.emptyEvidence (catalog : FunctionContracts hs) (f : TypedFn V hs hdr) :
    catalog.AnnotationEvidence f [] [] :=
  ⟨by simp, fun _ _ _ _ _ _ => noGivenFacts _ rfl _ _ _⟩

/-- Checking annotated code yields the same assurance as ordinary function admission when
the producer supplies its registered laws and facts at reached sites. -/
theorem FunctionContracts.checkAnnotated_assured (contracts : FunctionContracts hs) (f : TypedFn V hs hdr)
    {lemmas notes bounds} (evidence : contracts.AnnotationEvidence f lemmas notes)
    (accepted : contracts.checkFunction f lemmas notes = .ok bounds) : f.Assured bounds := by
  obtain ⟨summary,translated,checked⟩ := contracts.checkedBody f accepted
  have distinct : (Term.addresses [] f.body).Nodup := by
    have h := f.conditions.distinct
    simp only [Term.Distinct, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  have run (M : Model V) (table : FnTable M hs) (callees : Callees M table) (F : List (Place × Nat))
      (recorded : ∀ p b, (p,b) ∈ F → p.definition = hdr.key → p.role = none → (p,b) ∈ bounds)
      (ins : HList M.Val hdr.ins) (valid : ∀ v ∈ (localSem M hs table).dyns ins, ValidDyn M v)
      (required : FnHeader.Required M table hdr ins) :
      f.body.EveryLoop (localSem M hs table) (fun _ _ => True) (Annotation.Bounded ⟨F⟩ hdr.key none)
        [] [] (Env.empty.extend f.inputs ins) ∧
      (f.meaning M table ins).Every (fun _ _ => True) (fun ys =>
        (∀ v ∈ (localSem M hs table).dyns ys, ValidDyn M v) ∧
        ∀ q ∈ hdr.summary.ensures, q.Holds M
          ((localSem M hs table).dyns ins ++ (localSem M hs table).dyns ys)) (fun stop => stop ≠ .undefined) := by
    let σ := contracts.setting M table hdr.key lemmas notes F hdr.summary.ensures
    have parts := translated
    simp only [HeaderContracts.translate, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at parts
    obtain ⟨before,pre,after_,post,same⟩ := parts
    have actual := ArgumentsMatch.ofValues (sem := localSem M hs table) ins valid
    have req : ∀ e ∈ summary.requires, e.Holds σ.Runs σ.R (σ.sem.dyns ins) := by
      rw [←Option.some.inj same]
      exact (HeaderContracts.clauses_exact M table actual contracts.distinct pre).mpr required
    obtain ⟨loops,body⟩ := checkFacts_safe σ (contracts.settingLawful M table _ _ _ _ callees (evidence.laws M table callees) hdr.summary.ensures)
      (contracts.readerLawful M table _ _ _ _ callees hdr.summary.ensures) summary f.inputs f.body bounds checked distinct
      recorded [] ins valid req (evidence.facts M table callees ins (((localSem M hs table).dyns_valid_iff ins).mp valid) required)
    have returns := Process.every_mono _ σ.permitted (fun ys kept => And.intro kept.1
      (show ∀ q ∈ hdr.summary.ensures, q.Holds M
        (σ.sem.dyns ins ++ σ.sem.dyns ys) from
        (HeaderContracts.clauses_exact M table (HeaderContracts.appendArguments actual
          (ArgumentsMatch.ofValues (sem := localSem M hs table) ys kept.1)) contracts.distinct post).mp
          (by have h := kept.2; rw [←Option.some.inj same] at h; exact h))) (fun _ h => h) body
    exact And.intro (loops) returns
  constructor
  · intro M table callees ins valid required
    exact (run M table callees [] (by simp) ins valid required).2
  · intro M table callees F recorded ins valid required
    exact (run M table callees F recorded ins (((localSem M hs table).dyns_valid_iff ins).mpr valid) required).1

/-- A checked unannotated function is assured for all legal implementations of its callees. -/
theorem FunctionContracts.checkFunction_assured (contracts : FunctionContracts hs) (f : TypedFn V hs hdr)
    {bounds} (accepted : contracts.checkFunction f = .ok bounds) : f.Assured bounds :=
  contracts.checkAnnotated_assured f (contracts.emptyEvidence f) accepted

end Zkc.Core.BodyAnalysis
