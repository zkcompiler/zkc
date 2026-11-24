module

public import Zkc.Core.Facts.Contracts.AnnotationLaws
public import Zkc.Core.Facts.Body.ComparisonSound

@[expose] public section

namespace Zkc.Core.BodyAnalysis
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw)

omit [DecidableEq Raw] in
/-- Successful preflight covers even unused registry entries and dead code annotations. -/
theorem checkDefinition_ok_iff [DecidableEq D.Ty] {ins outs : List D.Ty} (inputs : Names ins)
    (body : Term D (Ctx.empty.extend inputs) outs) (notes : Annotations Raw) (summary : Contract Raw) :
    checkDefinition cfg.assertions cfg.lemmas inputs body notes summary = .ok () ↔
      cfg.lemmas.all (Lemma.check cfg.assertions) = true ∧ checkAnnotations cfg.assertions cfg.lemmas body notes = true ∧
      Contract.check (D := D) cfg.assertions summary ins outs = true := by
  unfold checkDefinition
  cases cfg.lemmas.all (Lemma.check cfg.assertions) <;>
    cases checkAnnotations cfg.assertions cfg.lemmas body notes <;>
    cases Contract.check (D := D) cfg.assertions summary ins outs <;> simp

/-- The bounds returned by the public fact checker are exactly those of a structurally checked,
refusal-free walk, in source order. -/
theorem checkFacts_ok_iff [DecidableEq D.Ty] {ins outs : List D.Ty} (inputs : Names ins)
    (body : Term D (Ctx.empty.extend inputs) outs) (notes : Annotations Raw) (summary : Contract Raw)
    (bounds : List (Place × Nat)) :
    checkFacts cfg notes summary inputs body = .ok bounds ↔
      checkDefinition cfg.assertions cfg.lemmas inputs body notes summary = .ok () ∧
      (analyse cfg notes summary inputs body).state.refusals = [] ∧
      (analyse cfg notes summary inputs body).state.bounds.reverse = bounds := by
  cases pre : checkDefinition cfg.assertions cfg.lemmas inputs body notes summary with
  | error => simp [checkFacts,pre,Except.mapError,Bind.bind,Except.bind]
  | ok passed =>
    cases passed
    cases refs : (analyse cfg notes summary inputs body).state.refusals <;>
      simp [checkFacts,analyseDiagnostics_eq,pre,refs,Except.mapError,Bind.bind,Except.bind]

/-- A successful comparison checks the source and the candidate using their respective lexical
contexts. The type equality comes from the same dialect comparator as the comparison. -/
theorem follows_checked (checks : SkelRules D) (definition' : Key) {ins outs : List D.Ty}
    (inputs inputs' : Names ins) (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs) (notes notes' : Annotations Raw) (summary : Contract Raw)
    (yes : follows cfg checks definition' notes notes' summary inputs inputs' body body' = true) :
    letI := checks.sameTy
    checkDefinition cfg.assertions cfg.lemmas inputs body notes summary = .ok () ∧
      checkDefinition cfg.assertions cfg.lemmas inputs' body' notes' summary = .ok () := by
  letI := checks.sameTy
  simp only [follows_eq, Bool.and_eq_true] at yes
  cases a : checkDefinition cfg.assertions cfg.lemmas inputs body notes summary <;>
    cases b : checkDefinition cfg.assertions cfg.lemmas inputs' body' notes' summary <;>
    simp_all [Except.isOk, Except.toBool]

/-- A successful comparison returns the candidate walk's own bound list. -/
theorem followChecked_bounds (checks : SkelRules D) (definition' : Key) {ins outs}
    (inputs inputs' : Names ins) (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs) (notes notes' : Annotations Raw) (summary : Contract Raw)
    {bs} (ok : followChecked cfg checks definition' notes notes' summary inputs inputs' body body' = .ok bs) :
    bs = (analyseBoth cfg definition' notes notes' summary inputs inputs' body body').2.state.bounds.reverse := by
  letI := checks.sameTy
  cases x : checkDefinition cfg.assertions cfg.lemmas inputs body notes summary <;>
    cases y : checkDefinition cfg.assertions cfg.lemmas inputs' body' notes' summary <;>
    simp only [followChecked, x, y, Except.mapError, bind, Except.bind] at ok
  all_goals try contradiction
  split at ok <;> cases ok
  rfl

variable (σ : Setting D Raw)

/-- The public fact verdict supplies all structural hypotheses for soundness. -/
theorem checkFacts_safe [DecidableEq D.Ty] (lawful : σ.Lawful) (reader : σ.cfg.assertions.Lawful σ)
    {ins outs : List D.Ty} (summary : Contract Raw) (inputs : Names ins)
    (body : Term D (Ctx.empty.extend inputs) outs) (bounds : List (Place × Nat))
    (ok : checkFacts σ.cfg σ.notes summary inputs body = .ok bounds)
    (distinct : (Term.addresses [] body).Nodup)
    (recorded : ∀ p b, (p, b) ∈ σ.F → p.definition = σ.cfg.definition → p.role = σ.cfg.role → (p,b) ∈ bounds)
    (path : List Frame) (values : HList σ.sem.Val ins) (valid : σ.AllValid values)
    (requires : ∀ e ∈ summary.requires, e.Holds σ.Runs σ.R (σ.sem.dyns values))
    (facts : Term.EveryFact σ .root body path (Env.empty.extend inputs values)) :
    Term.EveryLoop σ.sem σ.permitted σ.Bounded body path [] (Env.empty.extend inputs values) ∧
      (body.denote σ.sem path (Env.empty.extend inputs values)).Every σ.permitted
        (fun ys => σ.AllValid ys ∧ ∀ e ∈ summary.ensures, e.Holds σ.Runs σ.R (σ.sem.dyns values ++ σ.sem.dyns ys))
        (fun stop => ¬ σ.undefined stop) := by
  obtain ⟨pre,accepted,rfl⟩ := (checkFacts_ok_iff σ.cfg inputs body σ.notes summary bounds).mp ok
  exact analyseCheckedFrom_safe reader lawful summary inputs body (Values.empty σ.cfg.rules.place) (analyse σ.cfg σ.notes summary inputs body) (by simp [analyseCheckedFrom,pre,analyse])
    (Values.empty_wf _) distinct accepted (fun p b mem same role => List.mem_reverse.mp (recorded p b mem same role))
    path values valid requires facts

/-- A successful comparison against an independently safe source supplies its own candidate
typing evidence. Reached external facts remain the responsibility of their producer. -/
theorem follows_checked_assured (lawful : σ.Lawful) (conditions : ConditionsRead σ.sem σ.R) (reader : σ.cfg.assertions.Lawful σ) :
    ∀ (checks : SkelRules D) (definition' : Key) (notes' : Annotations Raw)
      {types outs : List D.Ty} (summary : Contract Raw) (inputs inputs' : Names types)
      (body : Term D (Ctx.empty.extend inputs) outs)
      (body' : Term D (Ctx.empty.extend inputs') outs),
      let σ' := σ.second definition' notes'
      let second := (analyseBoth σ.cfg definition' σ.notes notes' summary inputs inputs' body body').2
      checks.Lawful →
      follows σ.cfg checks definition' σ.notes notes' summary inputs inputs' body body' = true →
      (Term.addresses [] body').Nodup →
      (∀ p b, (p, b) ∈ σ.F → p.definition = definition' → p.role = σ.cfg.role →
        (p, b) ∈ second.state.bounds) →
      ∀ (path : List Frame) (values : HList σ.sem.Val types), σ.AllValid values →
        (∀ requirement, requirement ∈ summary.requires →
          requirement.Holds σ.Runs σ.R (σ.sem.dyns values)) →
        Term.EveryFact σ' .root body' path (Env.empty.extend inputs' values) →
        σ.NotUndefined (body.denote σ.sem path (Env.empty.extend inputs values)) →
        Term.EveryLoop σ.sem σ.permitted σ'.Bounded body' path []
            (Env.empty.extend inputs' values) ∧
          (body'.denote σ.sem path (Env.empty.extend inputs' values)).Every σ.permitted
            (fun returned => σ.AllValid returned ∧ ∀ guarantee, guarantee ∈ summary.ensures →
              guarantee.Holds σ.Runs σ.R (σ.sem.dyns values ++ σ.sem.dyns returned))
            (fun stop => ¬ σ.undefined stop) ∧
          Process.SameWhen σ.permitted (body.denote σ.sem path (Env.empty.extend inputs values))
            (body'.denote σ.sem path (Env.empty.extend inputs' values)) := by
  intro checks definition' notes' ins outs summary inputs inputs' body body'
  dsimp only
  intro lawfulChecks passed
  letI := checks.sameTy
  have checked := (follows_checked σ.cfg checks definition' inputs inputs' body body' σ.notes notes' summary passed).2
  obtain ⟨_, typedNotes, typedSummary⟩ := (checkDefinition_ok_iff σ.cfg inputs' body' notes' summary).mp checked
  let candidate := σ.second definition' notes'
  have candidateReader : candidate.cfg.assertions.Lawful candidate := ⟨reader.admissible, reader.total, reader.boolean⟩
  exact followsAssured σ lawful conditions checks definition' notes' summary inputs inputs' body body' lawfulChecks passed
    (checkAnnotations_defined candidateReader body' typedNotes)
    (fun g m => AssertionTypes.assertionDefined candidateReader (List.all_eq_true.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp typedSummary).1).2 g m))

end Zkc.Core.BodyAnalysis
