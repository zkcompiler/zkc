module

public import Zkc.Core.Facts.WalkRuns
public import Zkc.Core.Facts.SoundnessFollowing

@[expose] public section

/-!
The theorems of the analysis, for any dialect and any semantics whose rules are lawful
(`FactRules.Lawful`), from its two sides.

The value side: the process of a body that never stops `undefined` runs the skeleton of its
analysis over the table of the analysis (`analyse_runs`), and two bodies of which the second
follows the analysis of the first with no place that differs mean the same on every input on
which neither stops `undefined` (`follow_same`). The facts side: a body that the analysis refuses
nowhere is safe and respects its loop bounds (`analyse_safe`), and so is a body that follows an
accepted body with no refusal and no place that differs (`follow_safe`); nothing is assumed of
the safety of either. Together: the analysis of a definition is sound (`analyse_sound`), and a
definition that follows an accepted definition is safe and means the same (`follow_sound`).
-/

namespace Zkc.Core.Analysis

open FactCheck

/-! ## The value side: a body runs its skeleton, and two bodies that follow mean the same -/

section
variable {D : Dialect} {Raw : Type}

variable [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D) (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (undefined : sem.H → Prop)

/-- The process of a body that never stops `undefined` runs the skeleton of its analysis over
the table of the analysis, from the values of its inputs as the first leaves. -/
theorem analyse_runs (binding : rules.values.Binding sem Run undefined) (definition : Key)
    (role : Option Role) {types outs : List D.Ty} (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) (path : List Frame)
    (values : HList sem.Val types)
    (safe : (body.denote sem path (Env.empty.extend inputs values)).Every permitted
      (fun _ => True) (fun stop => ¬ undefined stop)) :
    Skel.Runs sem permitted Run (analyse rules checks definition role inputs body).state.st.table
      path (Valuation.setFrom (fun _ => none) 0 (sem.dyns values))
      (analyse rules checks definition role inputs body).skel
      (body.denote sem path (Env.empty.extend inputs values)) := by
  obtain ⟨support, agrees⟩ := Agrees.start (Run := Run)
    (table := (Table.empty rules.place : Table Raw)) inputs values
  simp only [analyse]
  exact ValueSide.walk_runs_built rules checks definition role sem permitted Run binding [] body _ _
    ⟨⟨Table.empty rules.place, types.length, [], []⟩, []⟩ path _ _ trivial support agrees safe

/-- Two bodies of which the second follows the analysis of the first with no place that differs
mean the same on every input on which neither stops `undefined`. -/
theorem follow_same (binding : rules.values.Binding sem Run undefined) (lawful : checks.Lawful)
    (definition definition' : Key) (role : Option Role) {types outs : List D.Ty}
    (inputs inputs' : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs)
    (followed : (follow rules checks definition' role
      (analyse rules checks definition role inputs body) inputs' body').state.differs = [])
    (path : List Frame) (values : HList sem.Val types)
    (safe : (body.denote sem path (Env.empty.extend inputs values)).Every permitted
      (fun _ => True) (fun stop => ¬ undefined stop))
    (safe' : (body'.denote sem path (Env.empty.extend inputs' values)).Every permitted
      (fun _ => True) (fun stop => ¬ undefined stop)) :
    Process.SameWhen permitted (body.denote sem path (Env.empty.extend inputs values))
      (body'.denote sem path (Env.empty.extend inputs' values)) := by
  obtain ⟨support, agrees⟩ := Agrees.start (Run := Run)
    (table := (Table.empty rules.place : Table Raw)) inputs values
  obtain ⟨-, agrees'⟩ := Agrees.start (Run := Run)
    (table := (Table.empty rules.place : Table Raw)) inputs' values
  have wf : Table.WF types.length (Table.empty rules.place : Table Raw) := trivial
  have runs := analyse_runs rules checks sem permitted Run undefined binding definition role inputs
    body path values safe
  have grown := Facts.walk_grows rules checks definition role [] body none
    (bindIds Ctx.empty inputs (List.range types.length)) (start rules types)
    ⟨⟨Table.empty rules.place, types.length, [], []⟩, []⟩ ⟨wf, agrees.inScope⟩ trivial
  have built := Facts.walk_skeleton rules checks definition role [] body
    (bindIds Ctx.empty inputs (List.range types.length)) (start rules types)
    ⟨⟨Table.empty rules.place, types.length, [], []⟩, []⟩ ⟨wf, agrees.inScope⟩
  simp only [analyse, follow] at runs followed
  generalize walk rules checks definition role [] body none _ _ _ = first
    at runs followed grown built
  obtain ⟨⟨wf1, -⟩, grows1⟩ := grown
  obtain ⟨ordered1, apart1⟩ := built
  have below1 := ordered1.below
  have agrees1 := agrees'.mono grows1.sub grows1.next (.refl _)
  have runs' := ValueSide.walk_runs_followed rules checks definition' role sem permitted Run binding
    lawful [] body' first.skel _ (start rules types)
    ⟨{ first.state.st with refusals := [], bounds := [] }, []⟩ path _ _ types.length followed wf1
    below1 apart1 support ordered1.fresh agrees1 safe'
  have grown' := Facts.walk_grows rules checks definition' role [] body' (some first.skel)
    (bindIds Ctx.empty inputs' (List.range types.length)) (start rules types)
    ⟨{ first.state.st with refusals := [], bounds := [] }, []⟩ ⟨wf1, agrees1.inScope⟩ below1
  generalize walk rules checks definition' role [] body' _ _ _ _ = second at runs' grown'
  obtain ⟨⟨wf2, -⟩, grows2⟩ := grown'
  have grows1' : St.Grows (⟨Table.empty rules.place, types.length, [], []⟩ : St D.Ty Raw)
      { first.state.st with refusals := [], bounds := [] } := ⟨grows1.next, grows1.table⟩
  have leaves : Leaves second.state.st.table
      (Valuation.setFrom (fun _ => none) 0 (sem.dyns values)) := by
    intro e known j _
    obtain ⟨_, new, entries, above⟩ := grows1'.trans grows2
    have known' : e ∈ new ++ [] := by
      have known'' : e ∈ second.state.st.table.entries := known
      rw [entries] at known''
      exact known''
    rw [List.append_nil] at known'
    have low : types.length ≤ e.lo := above e known'
    exact support _ (by omega)
  exact Skel.Runs.same sem permitted Run binding.functional wf2 _
    (Skel.Apart.grows grows2 _ apart1 below1) leaves
    (Skel.Runs.grow sem permitted Run _ grows2.sub _ runs) runs'

end

/-! ## The facts side: a body refused nowhere is safe, and so is a body that follows it -/

section
variable {D : Dialect} {Raw : Type}

variable [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D) (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop) (R : Reading sem.Dyn)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
  (undefined : sem.H → Prop)

set_option linter.unusedVariables false in
/-- A body with distinct addresses that the analysis refuses nowhere, on valid inputs and
permitted replies: every loop that a run reaches respects the bound that the analysis recorded
for it, and the body never stops `undefined` and returns valid values. -/
theorem analyse_safe (laws : rules.Lawful sem permitted R Run Valid undefined)
    (lawful : checks.Lawful) (definition : Key) (role : Option Role) {types outs : List D.Ty}
    (inputs : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (distinct : Term.Distinct body)
    (accepted : (analyse rules checks definition role inputs body).state.st.refusals = [])
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition → p.role = role →
      (p, b) ∈ (analyse rules checks definition role inputs body).state.st.bounds)
    (values : HList sem.Val types) (valid : ∀ v, v ∈ sem.dyns values → Valid v) :
    body.EveryLoop sem permitted (Annotation.Bounded ⟨F⟩ definition role) [] []
        (Env.empty.extend inputs values) ∧
      (body.denote sem [] (Env.empty.extend inputs values)).Every permitted
        (fun returned => ∀ v, v ∈ sem.dyns returned → Valid v) (fun stop => ¬ undefined stop) := by
  let σ : Facts.Setting D Raw :=
    ⟨rules, checks, sem, permitted, R, Run, Valid, undefined, definition, role, F⟩
  have nodup : (body.addresses []).Nodup := by
    simp only [Term.Distinct, Bool.and_eq_true, decide_eq_true_eq] at distinct
    exact distinct.1
  have shows := Facts.walk_sound_fresh (σ := σ) laws [] body [] _ _ _ _
    ⟨⟨Table.empty rules.place, types.length, [], []⟩, []⟩ 0 0
    (Facts.start_inv (σ := σ) laws inputs values valid rules.place) trivial
    (Facts.walk_free_differs rules checks definition role [] body _ _ _) accepted nodup
    (fun _ m => nomatch m) (by
      intro p b bl key m eq _
      have := recorded p b m (by rw [eq]) (by rw [eq])
      exact this)
  refine ⟨shows.1, Process.every_mono _ _ (fun returned h => ?_) (fun _ h => h) shows.2⟩
  obtain ⟨ρ', _, ex, _⟩ := h
  exact valuesOf_valid ex.rets ex.coherent.valid

set_option linter.unusedVariables false in
/-- A body with distinct addresses that follows the analysis of a first body with no refusal and
no place that differs, on valid inputs and permitted replies: every loop that a run reaches
respects the bound recorded for it while following, and the body never stops `undefined` and
returns valid values. -/
theorem follow_safe (laws : rules.Lawful sem permitted R Run Valid undefined)
    (lawful : checks.Lawful) (definition definition' : Key) (role : Option Role)
    {types outs : List D.Ty} (inputs inputs' : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs) (distinct' : Term.Distinct body')
    (followed : (follow rules checks definition' role
      (analyse rules checks definition role inputs body) inputs' body').accepted = true)
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition' → p.role = role →
      (p, b) ∈ (follow rules checks definition' role
        (analyse rules checks definition role inputs body) inputs' body').state.st.bounds)
    (values : HList sem.Val types) (valid : ∀ v, v ∈ sem.dyns values → Valid v) :
    body'.EveryLoop sem permitted (Annotation.Bounded ⟨F⟩ definition' role) [] []
        (Env.empty.extend inputs' values) ∧
      (body'.denote sem [] (Env.empty.extend inputs' values)).Every permitted
        (fun returned => ∀ v, v ∈ sem.dyns returned → Valid v) (fun stop => ¬ undefined stop) := by
  let σ : Facts.Setting D Raw :=
    ⟨rules, checks, sem, permitted, R, Run, Valid, undefined, definition', role, F⟩
  have nodup : (body'.addresses []).Nodup := by
    simp only [Term.Distinct, Bool.and_eq_true, decide_eq_true_eq] at distinct'
    exact distinct'.1
  simp only [Exit.accepted, Bool.and_eq_true, List.isEmpty_iff] at followed
  obtain ⟨accepted', differs'⟩ := followed
  -- the first analysis: its table is well formed and its skeleton's leaves are made in order
  -- from the first identifier after the inputs on, below its next identifier, apart from its table
  have startFirst := Facts.start_inv (σ := { σ with definition := definition }) laws inputs values
    valid rules.place
  have scopedFirst := Facts.Inv.scoped startFirst
  obtain ⟨fitsFirst, growsFirst⟩ := Facts.walk_grows rules checks definition role [] body none
    (bindIds Ctx.empty inputs (List.range types.length)) (start rules types)
    ⟨⟨Table.empty rules.place, types.length, [], []⟩, []⟩ scopedFirst trivial
  obtain ⟨ordered, apartFirst⟩ := Facts.walk_skeleton rules checks definition role [] body
    (bindIds Ctx.empty inputs (List.range types.length)) (start rules types)
    ⟨⟨Table.empty rules.place, types.length, [], []⟩, []⟩ scopedFirst
  simp only [follow, analyse] at accepted' differs' recorded ⊢
  generalize walk rules checks definition role [] body none
    (bindIds Ctx.empty inputs (List.range types.length)) (start rules types)
    ⟨⟨Table.empty rules.place, types.length, [], []⟩, []⟩ = first
    at fitsFirst growsFirst ordered apartFirst accepted' differs' recorded ⊢
  have startSecond := Facts.start_inv (σ := σ) laws inputs' values valid rules.place
  have inv : Facts.Inv σ (Valuation.setFrom (fun _ => none) 0 (sem.dyns values))
      (bindIds Ctx.empty inputs' (List.range types.length)) (Env.empty.extend inputs' values)
      (start rules types) { first.state.st with refusals := [], bounds := [] } :=
    ⟨Facts.Coherent.grow startSecond.coherent ⟨growsFirst.next, growsFirst.table⟩ fitsFirst.1,
      startSecond.agree, startSecond.holds⟩
  have quiet : Facts.Quiet types.length (Valuation.setFrom (fun _ => none) 0 (sem.dyns values))
      first.state.st.table := by
    intro i hi valued
    exfalso
    apply valued
    simp only [Valuation.setFrom]
    rw [ite_eq_right (by rw [sem.dyns_length]; omega)]
  have shows := Facts.walk_sound_follow (σ := σ) laws [] body' first.skel [] _ _ _ _
    ⟨{ first.state.st with refusals := [], bounds := [] }, []⟩ types.length
    first.state.st.next inv ⟨ordered, Nat.le_refl _, apartFirst, quiet⟩ differs' accepted' nodup
    (fun _ m => nomatch m) (by
      intro p b bl key m eq _
      have := recorded p b m (by rw [eq]) (by rw [eq])
      exact this)
  refine ⟨shows.1, Process.every_mono _ _ (fun returned h => ?_) (fun _ h => h) shows.2⟩
  obtain ⟨ρ', _, ex, _⟩ := h
  exact valuesOf_valid ex.rets ex.coherent.valid

end

/-! ## The two theorems of the analysis -/

section
variable {D : Dialect} {Raw : Type}

variable [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D) (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop) (R : Reading sem.Dyn)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
  (undefined : sem.H → Prop)

/-- **The analysis of a definition is sound.** A body with distinct addresses that the analysis
refuses nowhere, on valid inputs and permitted replies: every loop that a run reaches respects
the bound that the analysis recorded for it, the body never stops `undefined` and returns valid
values, and its process runs the skeleton of the analysis over its table. -/
theorem analyse_sound (laws : rules.Lawful sem permitted R Run Valid undefined)
    (lawful : checks.Lawful) (definition : Key) (role : Option Role) {types outs : List D.Ty}
    (inputs : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (distinct : Term.Distinct body)
    (accepted : (analyse rules checks definition role inputs body).state.st.refusals = [])
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition → p.role = role →
      (p, b) ∈ (analyse rules checks definition role inputs body).state.st.bounds)
    (values : HList sem.Val types) (valid : ∀ v, v ∈ sem.dyns values → Valid v) :
    body.EveryLoop sem permitted (Annotation.Bounded ⟨F⟩ definition role) [] []
        (Env.empty.extend inputs values) ∧
      (body.denote sem [] (Env.empty.extend inputs values)).Every permitted
        (fun returned => ∀ v, v ∈ sem.dyns returned → Valid v) (fun stop => ¬ undefined stop) ∧
      Skel.Runs sem permitted Run (analyse rules checks definition role inputs body).state.st.table
        [] (Valuation.setFrom (fun _ => none) 0 (sem.dyns values))
        (analyse rules checks definition role inputs body).skel
        (body.denote sem [] (Env.empty.extend inputs values)) := by
  have safe := analyse_safe rules checks sem permitted R Run Valid undefined laws lawful definition
    role inputs body distinct accepted F recorded values valid
  exact ⟨safe.1, safe.2,
    analyse_runs rules checks sem permitted Run undefined laws.binding definition role inputs body
      [] values (Process.every_mono _ permitted (fun _ _ => trivial) (fun _ stop => stop) safe.2)⟩

/-- **A definition that follows an accepted definition is safe and means the same.** For two
bodies with distinct addresses and the same types, of which the first is refused nowhere and the
second follows the first with no refusal and no place that differs, on valid inputs and
permitted replies: every loop of the second respects the bound recorded for it, the second never
stops `undefined` and returns valid values, and the two processes mean the same. Nothing is
assumed of the safety of the second. -/
theorem follow_sound (laws : rules.Lawful sem permitted R Run Valid undefined)
    (lawful : checks.Lawful) (definition definition' : Key) (role : Option Role)
    {types outs : List D.Ty} (inputs inputs' : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs)
    (distinct : Term.Distinct body) (distinct' : Term.Distinct body')
    (accepted : (analyse rules checks definition role inputs body).state.st.refusals = [])
    (followed : (follow rules checks definition' role
      (analyse rules checks definition role inputs body) inputs' body').accepted = true)
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition' → p.role = role →
      (p, b) ∈ (follow rules checks definition' role
        (analyse rules checks definition role inputs body) inputs' body').state.st.bounds)
    (values : HList sem.Val types) (valid : ∀ v, v ∈ sem.dyns values → Valid v) :
    body'.EveryLoop sem permitted (Annotation.Bounded ⟨F⟩ definition' role) [] []
        (Env.empty.extend inputs' values) ∧
      (body'.denote sem [] (Env.empty.extend inputs' values)).Every permitted
        (fun returned => ∀ v, v ∈ sem.dyns returned → Valid v) (fun stop => ¬ undefined stop) ∧
      Process.SameWhen permitted (body.denote sem [] (Env.empty.extend inputs values))
        (body'.denote sem [] (Env.empty.extend inputs' values)) := by
  have first := analyse_safe rules checks sem permitted R Run Valid undefined laws lawful
    definition role inputs body distinct accepted [] (fun _ _ inside => nomatch inside) values
    valid
  have second := follow_safe rules checks sem permitted R Run Valid undefined laws lawful
    definition definition' role inputs inputs' body body' distinct' followed F recorded values
    valid
  have differs : (follow rules checks definition' role
      (analyse rules checks definition role inputs body) inputs' body').state.differs = [] := by
    simp only [Exit.accepted, Bool.and_eq_true, List.isEmpty_iff] at followed
    exact followed.2
  exact ⟨second.1, second.2,
    follow_same rules checks sem permitted Run undefined laws.binding lawful definition
      definition' role inputs inputs' body body' differs [] values
      (Process.every_mono _ permitted (fun _ _ => trivial) (fun _ stop => stop) first.2)
      (Process.every_mono _ permitted (fun _ _ => trivial) (fun _ stop => stop) second.2)⟩

end

end Zkc.Core.Analysis
