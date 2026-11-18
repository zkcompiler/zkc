module

public import Zkc.Core.Facts.Contracts.Annotations
public import Zkc.Core.Facts.Contracts.TypeLaws
public import Zkc.Core.Facts.Body.AnalysisSound

@[expose] public section

namespace Zkc.Core.BodyAnalysis

variable {D : Dialect} {Raw : Type} [DecidableEq D.Ty] {types : AssertionTypes D.Ty Raw}
    {σ : Setting D Raw} (laws : types.Lawful σ)

omit [DecidableEq D.Ty] in
include laws in
theorem AssertionTypes.assertionDefined {context : List D.Ty} {expr : Expr Raw}
    (h : types.isAssertion context expr = true) : Expr.Defined σ context expr := by
  cases inferred : types.infer context expr with
  | none => simp [AssertionTypes.isAssertion, inferred] at h
  | some _ => exact AssertionTypes.defined laws inferred

private def Checked (e : AnnotationContext D.Ty) : Prop :=
  ∀ note ∈ σ.notes.at_ e.site, Annotation.check (D := D) types σ.cfg.lemmas e.names e.invariantTypes note = true

include laws in
private theorem checkedSteps {e : AnnotationContext D.Ty} (checked : Checked (σ := σ) (types := types) e) :
    StepsDefinedAt σ e.names e.site := by
  intro number names member
  have passed := checked _ member
  cases resolved : Lemma.resolve? σ.cfg.lemmas e.names number names with
  | none => simp [Annotation.check, resolved] at passed
  | some lemma =>
    obtain ⟨registered, actual⟩ := (Lemma.resolve?_eq_some ..).mp resolved
    simp only [Annotation.check, resolved, Bool.and_eq_true, List.all_eq_true] at passed
    exact ⟨lemma, registered, actual, fun premise m => AssertionTypes.assertionDefined laws (passed.1 _ m)⟩

include laws in
private theorem checkedInvariants {Γ : Ctx D.Ty} {site : AnnotationSite} {w : D.Who}
    {carried : List D.Ty} (checked : Checked (σ := σ) (types := types) ⟨site, Γ, some (D.index w :: carried)⟩) :
    InvariantsDefinedAt σ Γ site w carried := by
  intro uses expressions member ts named expr m
  have passed := checked _ member
  simp [Annotation.check, named] at passed
  exact AssertionTypes.assertionDefined laws (passed _ m)

private abbrev AllChecked (entries : List (AnnotationContext D.Ty)) :=
  ∀ e ∈ entries, Checked (σ := σ) (types := types) e

private theorem AllChecked.left {a b : List (AnnotationContext D.Ty)}
    (h : AllChecked (σ := σ) (types := types) (a ++ b)) : AllChecked (σ := σ) (types := types) a :=
  fun e m => h e (List.mem_append_left _ m)
private theorem AllChecked.right {a b : List (AnnotationContext D.Ty)}
    (h : AllChecked (σ := σ) (types := types) (a ++ b)) : AllChecked (σ := σ) (types := types) b :=
  fun e m => h e (List.mem_append_right _ m)

set_option linter.unusedSectionVars false in
include laws in
mutual
  private theorem checkedTerm (cursor : StaticCursor) : ∀ {Γ outs} (body : Term D Γ outs),
      AllChecked (σ := σ) (types := types) (Term.annotationContexts cursor body) →
        Term.AnnotationsDefined σ cursor body
    | _, _, .ret _, _ => trivial
    | _, _, .step key i _ rest, h => by
      have atEntry := h _ List.mem_cons_self
      have others := fun e m => h e (List.mem_cons_of_mem _ m)
      exact ⟨checkedSteps laws atEntry, checkedInstr cursor key i atEntry (AllChecked.left others),
        checkedTerm cursor.next rest (AllChecked.right others)⟩
  private theorem checkedInstr (cursor : StaticCursor) (key : Key) :
      ∀ {Γ mid} (i : Instr D Γ mid),
        Checked (σ := σ) (types := types) ⟨Instr.site cursor key i, Γ, Instr.invariantTypes i⟩ →
        AllChecked (σ := σ) (types := types) (Instr.regionContexts cursor key i) →
          Instr.AnnotationsDefined σ cursor key i
    | _, _, .op .., _, _ | _, _, .guard .., _, _ => trivial
    | _, _, .choose _ _ _ _ t f, _, h =>
        ⟨checkedTerm (cursor.region key) t (AllChecked.left h), checkedTerm (cursor.otherwise key) f (AllChecked.right h)⟩
    | _, _, .cases _ _ _ _ arms, _, h => checkedArms (cursor.region key) arms h
    | _, _, .loop _ _ _ _ _ body, entry, h => ⟨checkedInvariants laws entry, checkedTerm (cursor.region key) body h⟩
    | _, _, .block n body, _, h => checkedTerm (cursor.block key n) body h
    | _, _, .attempt _ _ _ body, _, h => checkedTerm (cursor.region key) body h
  private theorem checkedArms (cursor : StaticCursor) : ∀ {Γ mid payloads} (arms : Arms D Γ mid payloads),
      AllChecked (σ := σ) (types := types) (Arms.annotationContexts cursor arms) →
        Arms.AnnotationsDefined σ cursor arms
    | _, _, _, .nil, _ => trivial
    | _, _, _, .cons _ arm rest, h =>
        ⟨checkedTerm cursor.arm arm (AllChecked.left h), checkedArms cursor.next rest (AllChecked.right h)⟩
end

include laws in
theorem checkAnnotations_defined {Γ outs} (body : Term D Γ outs)
    (checked : checkAnnotations types σ.cfg.lemmas body σ.notes = true) :
    Term.AnnotationsDefined σ .root body := by
  apply checkedTerm laws
  intro entry member note atEntry
  cases notes : σ.notes with
  | nil => simp [notes, Annotations.at_] at atEntry
  | cons first rest =>
    simp only [checkAnnotations, notes, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      Bool.and_eq_true, List.all_eq_true] at checked
    rw [notes] at atEntry
    exact checked.2 _ member _ atEntry

/-- Successful structural checking produces both definedness obligations used by the walk. -/
theorem analyseCheckedFrom_ok_iff [DecidableEq Raw] {ins outs : List D.Ty} (summary : Contract Raw)
    (inputs : Names ins) (body : Term D (Ctx.empty.extend inputs) outs)
    (start : Values Raw) (e : Exit D Raw σ.cfg.domain.State outs) :
    analyseCheckedFrom σ.cfg σ.notes summary inputs body start = .ok e ↔
      σ.cfg.lemmas.all (Lemma.check σ.cfg.assertions) = true ∧
      checkAnnotations σ.cfg.assertions σ.cfg.lemmas body σ.notes = true ∧
      Contract.check (D := D) σ.cfg.assertions summary ins outs = true ∧
      analyseFrom σ.cfg σ.notes summary inputs body start = e := by
  cases reg : σ.cfg.lemmas.all (Lemma.check σ.cfg.assertions) <;>
    cases h : checkAnnotations σ.cfg.assertions σ.cfg.lemmas body σ.notes <;>
    cases k : Contract.check (D := D) σ.cfg.assertions summary ins outs <;>
    simp [analyseCheckedFrom, checkDefinition, reg, h, k]

/-- An accepted checked analysis supplies structural definedness. Given facts still have to
hold when reached, and the operation and domain laws still come from their owners. -/
theorem analyseCheckedFrom_safe [DecidableEq Raw] (reader : σ.cfg.assertions.Lawful σ) (lawful : σ.Lawful) {ins outs : List D.Ty}
    (summary : Contract Raw) (inputs : Names ins) (body : Term D (Ctx.empty.extend inputs) outs)
    (start : Values Raw) (e : Exit D Raw σ.cfg.domain.State outs)
    (checked : analyseCheckedFrom σ.cfg σ.notes summary inputs body start = .ok e)
    (wf : start.WF) (distinct : (Term.addresses [] body).Nodup) (accepted : e.state.refusals = [])
    (recorded : ∀ p b, (p, b) ∈ σ.F → p.definition = σ.cfg.definition → p.role = σ.cfg.role →
      (p, b) ∈ e.state.bounds) (path : List Frame) (values : HList σ.sem.Val ins)
    (valid : σ.AllValid values) (requires : ∀ expr ∈ summary.requires, expr.Holds σ.Runs σ.R (σ.sem.dyns values))
    (facts : Term.EveryFact σ .root body path (Env.empty.extend inputs values)) :
    Term.EveryLoop σ.sem σ.permitted σ.Bounded body path [] (Env.empty.extend inputs values) ∧
      (body.denote σ.sem path (Env.empty.extend inputs values)).Every σ.permitted
        (fun returned => σ.AllValid returned ∧ ∀ expr ∈ summary.ensures,
          expr.Holds σ.Runs σ.R (σ.sem.dyns values ++ σ.sem.dyns returned)) (fun stop => ¬ σ.undefined stop) := by
  obtain ⟨_, annotations, contract, rfl⟩ := (analyseCheckedFrom_ok_iff summary inputs body start e).mp checked
  have guarantees := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp contract).1).2
  exact analyseSafe σ lawful summary inputs body start wf (checkAnnotations_defined reader body annotations)
    (fun expr m => AssertionTypes.assertionDefined reader (List.all_eq_true.mp guarantees expr m))
    distinct accepted recorded path values valid requires facts

#print axioms checkAnnotations_defined
#print axioms analyseCheckedFrom_safe

end Zkc.Core.BodyAnalysis
