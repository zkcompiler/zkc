module

public import Zkc.Core.Facts.WalkRuns
public import Zkc.Core.Facts.SoundnessFollowing
public import Zkc.Core.Evidence.Summary

@[expose] public section

/-!
The theorems of the analysis, for any dialect and any semantics whose rules are lawful
(`FactRules.Lawful`), from its two sides, for a body analysed under a summary of its definition
(`Summary`): what the summary requires of the inputs is known at the start, and what it
guarantees is decided where the body returns.

The value side: the process of a body that never stops `undefined` runs the skeleton of its
analysis over the table of the analysis (`analyse_runs`), and two bodies of which the second
follows the analysis of the first with no place that differs mean the same on every input on
which neither stops `undefined` (`follow_same`). The facts side: on inputs of which every
requirement of the summary holds, a body that the analysis refuses nowhere is safe, respects its
loop bounds, and returns values of which, with the inputs, every guarantee of the summary holds
(`analyse_safe`), and so is a body that follows the analysis of a first body with no refusal and
no place that differs (`follow_safe`), which does not need the first body to be accepted. That
the two mean the same needs the first to be safe too, however that is known: a body that follows
a safe body is safe and means the same as it (`follow_assured`), which reads neither the first's
addresses nor whether its analysis refuses anything. Nothing is assumed of the safety of the body
that follows; the facts side asks that the addresses of the body that it is about be distinct,
which elaboration decides. Together: the analysis of a definition is sound (`analyse_sound`), and
a definition that follows an accepted definition is safe and means the same (`follow_sound`,
`follow_assured` with the first safe because the analysis accepts it). A body that the analysis
under a summary refuses nowhere satisfies the summary as a function of its inputs
(`analyse_holds`, `Summary.Holds`). With the summary with no requirement and no guarantee, each
is the theorem about a body analysed alone.
-/

namespace Zkc.Core.Analysis

open FactCheck

/-! ## The value side: a body runs its skeleton, and two bodies that follow mean the same -/

section
variable {D : Dialect} {Raw : Type}

variable [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D) (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (undefined : sem.H → Prop)

/-- The process of a body that never stops `undefined` runs the skeleton of its analysis under a
summary over the table of the analysis, from the values of its inputs as the first leaves. -/
theorem analyse_runs (binding : rules.values.Binding sem Run undefined) (definition : Key)
    (role : Option Role) {types outs : List D.Ty} (summary : Summary Raw) (inputs : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs) (path : List Frame)
    (values : HList sem.Val types)
    (safe : (body.denote sem path (Env.empty.extend inputs values)).Every permitted
      (fun _ => True) (fun stop => ¬ undefined stop)) :
    Skel.Runs sem permitted Run
      (analyse rules checks definition role summary inputs body).state.st.table path
      (Valuation.setFrom (fun _ => none) 0 (sem.dyns values))
      (analyse rules checks definition role summary inputs body).skel
      (body.denote sem path (Env.empty.extend inputs values)) := by
  obtain ⟨wf, grows⟩ := learnRequirements_grows rules.ops (List.range types.length)
    summary.requires (start rules types)
    (⟨Table.empty rules.place, types.length, [], []⟩ : St D.Ty Raw) trivial
    (fun _ m => List.mem_range.mp m)
  obtain ⟨support, agrees⟩ := Agrees.start (Run := Run)
    (table := (startUnder rules summary types
      ⟨Table.empty rules.place, types.length, [], []⟩).2.table) inputs values
  simp only [analyse, exitUnder]
  exact ValueSide.walk_runs_built rules checks definition role sem permitted Run binding [] body _ _
    _ path _ _ wf (support.mono grows.next) (agrees.mono (fun _ m => m) grows.next (.refl _)) safe

/-- Two bodies of which the second follows the analysis of the first, both under a summary, with
no place that differs mean the same on every input on which neither stops `undefined`. -/
theorem follow_same (binding : rules.values.Binding sem Run undefined) (lawful : checks.Lawful)
    (definition definition' : Key) (role : Option Role) {types outs : List D.Ty}
    (summary : Summary Raw) (inputs inputs' : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs)
    (followed : (follow rules checks definition' role summary
      (analyse rules checks definition role summary inputs body) inputs' body').state.differs = [])
    (path : List Frame) (values : HList sem.Val types)
    (safe : (body.denote sem path (Env.empty.extend inputs values)).Every permitted
      (fun _ => True) (fun stop => ¬ undefined stop))
    (safe' : (body'.denote sem path (Env.empty.extend inputs' values)).Every permitted
      (fun _ => True) (fun stop => ¬ undefined stop)) :
    Process.SameWhen permitted (body.denote sem path (Env.empty.extend inputs values))
      (body'.denote sem path (Env.empty.extend inputs' values)) := by
  have runs := analyse_runs rules checks sem permitted Run undefined binding definition role
    summary inputs body path values safe
  -- the start of the first, from the empty table
  obtain ⟨wf0, grows0⟩ := learnRequirements_grows rules.ops (List.range types.length)
    summary.requires (start rules types)
    (⟨Table.empty rules.place, types.length, [], []⟩ : St D.Ty Raw) trivial
    (fun _ m => List.mem_range.mp m)
  obtain ⟨support, agrees⟩ := Agrees.start (Run := Run)
    (table := (startUnder rules summary types
      ⟨Table.empty rules.place, types.length, [], []⟩).2.table) inputs values
  have agrees0 := agrees.mono (fun _ m => m) grows0.next (.refl _)
  have grown := Facts.walk_grows rules checks definition role [] body none
    (bindIds Ctx.empty inputs (List.range types.length))
    (startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).1
    ⟨(startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).2, []⟩
    ⟨wf0, agrees0.inScope⟩ trivial
  have built := Facts.walk_skeleton rules checks definition role [] body
    (bindIds Ctx.empty inputs (List.range types.length))
    (startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).1
    ⟨(startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).2, []⟩
    ⟨wf0, agrees0.inScope⟩
  simp only [analyse, follow, exitUnder] at runs followed
  generalize walk rules checks definition role [] body none _ _ _ = first
    at runs followed grown built
  obtain ⟨⟨wf1, -⟩, grows1⟩ := grown
  obtain ⟨ordered1, apart1⟩ := built
  have below1 := ordered1.below
  have ordered1' := Facts.Skel.Ordered.low ordered1 grows0.next
  -- the start of the second, from the table of the first
  have grows1' : St.Grows
      (startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).2
      { first.state.st with refusals := [], bounds := [] } := ⟨grows1.next, grows1.table⟩
  obtain ⟨wf2, grows2⟩ := learnRequirements_grows rules.ops (List.range types.length)
    summary.requires (start rules types) { first.state.st with refusals := [], bounds := [] } wf1
    (fun a m => Nat.lt_of_lt_of_le (List.mem_range.mp m) (grows0.trans grows1').next)
  obtain ⟨-, agrees'⟩ := Agrees.start (Run := Run)
    (table := (startUnder rules summary types
      { first.state.st with refusals := [], bounds := [] }).2.table) inputs' values
  have agrees2 := agrees'.mono (fun _ m => m) ((grows0.trans grows1').trans grows2).next (.refl _)
  have runs' := ValueSide.walk_runs_followed rules checks definition' role sem permitted Run binding
    lawful [] body' first.skel _ _
    ⟨(startUnder rules summary types { first.state.st with refusals := [], bounds := [] }).2, []⟩
    path _ _ types.length followed wf2 (below1.mono grows2.next)
    (Skel.Apart.grows grows2 _ apart1 below1) support ordered1'.fresh agrees2 safe'
  have grown' := Facts.walk_grows rules checks definition' role [] body' (some first.skel)
    (bindIds Ctx.empty inputs' (List.range types.length))
    (startUnder rules summary types { first.state.st with refusals := [], bounds := [] }).1
    ⟨(startUnder rules summary types { first.state.st with refusals := [], bounds := [] }).2, []⟩
    ⟨wf2, agrees2.inScope⟩ (below1.mono grows2.next)
  generalize walk rules checks definition' role [] body' _ _ _ _ = second at runs' grown'
  obtain ⟨⟨wf3, -⟩, grows3⟩ := grown'
  have leaves : Leaves second.state.st.table
      (Valuation.setFrom (fun _ => none) 0 (sem.dyns values)) := by
    intro e known j _
    obtain ⟨_, new, entries, above⟩ := grows0.trans (grows1'.trans (grows2.trans grows3))
    have known' : e ∈ new ++ [] := by
      have known'' : e ∈ second.state.st.table.entries := known
      rw [entries] at known''
      exact known''
    rw [List.append_nil] at known'
    have low : types.length ≤ e.lo := above e known'
    exact support _ (by omega)
  exact Skel.Runs.same sem permitted Run binding.functional wf3 _
    (Skel.Apart.grows (grows2.trans grows3) _ apart1 below1) leaves
    (Skel.Runs.grow sem permitted Run _ (grows2.trans grows3).sub _ runs) runs'

end

/-! ## The facts side: a body refused nowhere is safe, and so is a body that follows it -/

section
variable {D : Dialect} {Raw : Type}

variable [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D) (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop) (R : Reading sem.Dyn)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
  (undefined : sem.H → Prop)

set_option linter.unusedVariables false in
/-- A body with distinct addresses that the analysis under a summary refuses nowhere, on valid
inputs of which every requirement of the summary holds, and permitted replies: every loop that a
run reaches respects the bound that the analysis recorded for it, and the body never stops
`undefined` and returns valid values of which, with the inputs, every guarantee of the summary
holds. -/
theorem analyse_safe (laws : rules.Lawful sem permitted R Run Valid undefined)
    (lawful : checks.Lawful) (definition : Key) (role : Option Role) {types outs : List D.Ty}
    (summary : Summary Raw) (inputs : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (distinct : Term.Distinct body)
    (accepted : (analyse rules checks definition role summary inputs body).state.st.refusals = [])
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition → p.role = role →
      (p, b) ∈ (analyse rules checks definition role summary inputs body).state.st.bounds)
    (values : HList sem.Val types) (valid : ∀ v, v ∈ sem.dyns values → Valid v)
    (required : ∀ requirement, requirement ∈ summary.requires →
      requirement.Holds (ValidRun sem Run Valid) R (sem.dyns values)) :
    body.EveryLoop sem permitted (Annotation.Bounded ⟨F⟩ definition role) [] []
        (Env.empty.extend inputs values) ∧
      (body.denote sem [] (Env.empty.extend inputs values)).Every permitted
        (fun returned => (∀ v, v ∈ sem.dyns returned → Valid v) ∧
          ∀ guarantee, guarantee ∈ summary.ensures →
            guarantee.Holds (ValidRun sem Run Valid) R (sem.dyns values ++ sem.dyns returned))
        (fun stop => ¬ undefined stop) := by
  let σ : Facts.Setting D Raw :=
    ⟨rules, checks, sem, permitted, R, Run, Valid, undefined, definition, role, F⟩
  have nodup : (body.addresses []).Nodup := by
    simp only [Term.Distinct, Bool.and_eq_true, decide_eq_true_eq] at distinct
    exact distinct.1
  obtain ⟨ρ₀, le₀, inv₀, -, -⟩ := Facts.startUnder_inv (σ := σ) laws inputs values summary required
    (Facts.start_inv (σ := σ) laws inputs values valid rules.place)
  have started : (startUnder rules summary types
      ⟨Table.empty rules.place, types.length, [], []⟩).2.bounds = [] :=
    (learnRequirements_state rules.ops _ _ _ _).2
  simp only [analyse, exitUnder] at accepted recorded ⊢
  obtain ⟨new, enew⟩ := checkGuarantees_adds rules.ops _ _ _ _ summary.ensures
    (walk rules checks definition role [] body none
      (bindIds Ctx.empty inputs (List.range types.length))
      (startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).1
      ⟨(startUnder rules summary types
        ⟨Table.empty rules.place, types.length, [], []⟩).2, []⟩).state.st.refusals
  have refused := (List.append_eq_nil_iff.mp (enew.symm.trans accepted)).2
  have shows := Facts.walk_sound_fresh (σ := σ) laws [] body [] ρ₀ _ _ _
    ⟨(startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).2, []⟩ 0 0
    inv₀ trivial (Facts.walk_free_differs rules checks definition role [] body _ _ _) refused nodup
    (fun q m => by rw [started] at m; cases m) (by
      intro p b bl key m eq _
      have := recorded p b m (by rw [eq]) (by rw [eq])
      exact this)
  refine ⟨shows.1, Process.every_mono _ _ (fun returned h => ?_) (fun _ h => h) shows.2⟩
  obtain ⟨ρ', le', ex, _⟩ := h
  refine ⟨valuesOf_valid ex.rets ex.coherent.valid, ?_⟩
  exact checkGuarantees_sound laws.ops ex.coherent.consistent ex.coherent.closed ex.holds
    (valuesOf_append (valuesOf_le (le₀.trans le') (Facts.start_values (σ := σ) values)) ex.rets)
    summary.ensures _ accepted

set_option linter.unusedVariables false in
/-- A body with distinct addresses that follows the analysis of a first body, both under a
summary, with no refusal and no place that differs, on valid inputs of which every requirement
of the summary holds, and permitted replies: every loop that a run reaches respects the bound
recorded for it while following, and the body never stops `undefined` and returns valid values of
which, with the inputs, every guarantee of the summary holds. -/
theorem follow_safe (laws : rules.Lawful sem permitted R Run Valid undefined)
    (lawful : checks.Lawful) (definition definition' : Key) (role : Option Role)
    {types outs : List D.Ty} (summary : Summary Raw) (inputs inputs' : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs) (distinct' : Term.Distinct body')
    (followed : (follow rules checks definition' role summary
      (analyse rules checks definition role summary inputs body) inputs' body').accepted = true)
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition' → p.role = role →
      (p, b) ∈ (follow rules checks definition' role summary
        (analyse rules checks definition role summary inputs body) inputs' body').state.st.bounds)
    (values : HList sem.Val types) (valid : ∀ v, v ∈ sem.dyns values → Valid v)
    (required : ∀ requirement, requirement ∈ summary.requires →
      requirement.Holds (ValidRun sem Run Valid) R (sem.dyns values)) :
    body'.EveryLoop sem permitted (Annotation.Bounded ⟨F⟩ definition' role) [] []
        (Env.empty.extend inputs' values) ∧
      (body'.denote sem [] (Env.empty.extend inputs' values)).Every permitted
        (fun returned => (∀ v, v ∈ sem.dyns returned → Valid v) ∧
          ∀ guarantee, guarantee ∈ summary.ensures →
            guarantee.Holds (ValidRun sem Run Valid) R (sem.dyns values ++ sem.dyns returned))
        (fun stop => ¬ undefined stop) := by
  let σ : Facts.Setting D Raw :=
    ⟨rules, checks, sem, permitted, R, Run, Valid, undefined, definition', role, F⟩
  have nodup : (body'.addresses []).Nodup := by
    simp only [Term.Distinct, Bool.and_eq_true, decide_eq_true_eq] at distinct'
    exact distinct'.1
  simp only [Exit.accepted, Bool.and_eq_true, List.isEmpty_iff] at followed
  obtain ⟨accepted', differs'⟩ := followed
  -- the first analysis: its table is well formed and its skeleton's leaves are made in order
  -- from the first identifier after its start on, below its next identifier, apart from its table
  have startFirst := Facts.start_inv (σ := { σ with definition := definition }) laws inputs values
    valid rules.place
  obtain ⟨wf0, grows0⟩ := learnRequirements_grows rules.ops (List.range types.length)
    summary.requires (start rules types)
    (⟨Table.empty rules.place, types.length, [], []⟩ : St D.Ty Raw) trivial
    (fun _ m => List.mem_range.mp m)
  have scopedFirst : Scoped (Ctx.empty.extend inputs)
      (bindIds Ctx.empty inputs (List.range types.length))
      (startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).2 :=
    ⟨wf0, (Facts.Inv.scoped startFirst).2.mono grows0.next⟩
  obtain ⟨fitsFirst, growsFirst⟩ := Facts.walk_grows rules checks definition role [] body none
    (bindIds Ctx.empty inputs (List.range types.length))
    (startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).1
    ⟨(startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).2, []⟩
    scopedFirst trivial
  obtain ⟨ordered, apartFirst⟩ := Facts.walk_skeleton rules checks definition role [] body
    (bindIds Ctx.empty inputs (List.range types.length))
    (startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).1
    ⟨(startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).2, []⟩
    scopedFirst
  simp only [follow, analyse, exitUnder] at accepted' differs' recorded ⊢
  generalize walk rules checks definition role [] body none
    (bindIds Ctx.empty inputs (List.range types.length))
    (startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).1
    ⟨(startUnder rules summary types ⟨Table.empty rules.place, types.length, [], []⟩).2, []⟩ =
      first at fitsFirst growsFirst ordered apartFirst accepted' differs' recorded ⊢
  -- the start of the second, from the table of the first
  have startSecond := Facts.start_inv (σ := σ) laws inputs' values valid rules.place
  have grownFirst : St.Grows (⟨Table.empty rules.place, types.length, [], []⟩ : St D.Ty Raw)
      { first.state.st with refusals := [], bounds := [] } :=
    ⟨(grows0.trans growsFirst).next, (grows0.trans growsFirst).table⟩
  have inv : Facts.Inv σ (Valuation.setFrom (fun _ => none) 0 (sem.dyns values))
      (bindIds Ctx.empty inputs' (List.range types.length)) (Env.empty.extend inputs' values)
      (start rules types) { first.state.st with refusals := [], bounds := [] } :=
    ⟨Facts.Coherent.grow startSecond.coherent grownFirst fitsFirst.1, startSecond.agree,
      startSecond.holds⟩
  obtain ⟨ρ₀, le₀, inv₀, grows₀, fills₀⟩ := Facts.startUnder_inv (σ := σ) laws inputs' values
    summary required inv
  have quiet : Facts.Quiet types.length (Valuation.setFrom (fun _ => none) 0 (sem.dyns values))
      first.state.st.table := by
    intro i hi valued
    exfalso
    apply valued
    simp only [Valuation.setFrom]
    rw [ite_eq_right (by rw [sem.dyns_length]; omega)]
  have started : (startUnder rules summary types
      { first.state.st with refusals := [], bounds := [] }).2.bounds = [] :=
    (learnRequirements_state rules.ops _ _ _ _).2
  obtain ⟨new, enew⟩ := checkGuarantees_adds rules.ops _ _ _ _ summary.ensures
    (walk rules checks definition' role [] body' (some first.skel)
      (bindIds Ctx.empty inputs' (List.range types.length))
      (startUnder rules summary types { first.state.st with refusals := [], bounds := [] }).1
      ⟨(startUnder rules summary types
        { first.state.st with refusals := [], bounds := [] }).2, []⟩).state.st.refusals
  have refused := (List.append_eq_nil_iff.mp (enew.symm.trans accepted')).2
  have shows := Facts.walk_sound_follow (σ := σ) laws [] body' first.skel [] ρ₀ _ _ _
    ⟨(startUnder rules summary types { first.state.st with refusals := [], bounds := [] }).2, []⟩
    types.length first.state.st.next inv₀
    ⟨Facts.Skel.Ordered.low ordered grows0.next, grows₀.next,
      Facts.Skel.Ordered.apart ordered (Nat.le_refl _) apartFirst ⟨grows₀.next, grows₀.table⟩,
      quiet.fills fills₀ grows₀.sub⟩
    differs' refused nodup (fun q m => by rw [started] at m; cases m) (by
      intro p b bl key m eq _
      have := recorded p b m (by rw [eq]) (by rw [eq])
      exact this)
  refine ⟨shows.1, Process.every_mono _ _ (fun returned h => ?_) (fun _ h => h) shows.2⟩
  obtain ⟨ρ', le', ex, _⟩ := h
  refine ⟨valuesOf_valid ex.rets ex.coherent.valid, ?_⟩
  exact checkGuarantees_sound laws.ops ex.coherent.consistent ex.coherent.closed ex.holds
    (valuesOf_append (valuesOf_le (le₀.trans le') (Facts.start_values (σ := σ) values)) ex.rets)
    summary.ensures _ accepted'

end

/-! ## The theorems of the analysis -/

section
variable {D : Dialect} {Raw : Type}

variable [DecidableEq Raw] (rules : FactRules D Raw) (checks : SkelRules D) (sem : Semantics D)
  (permitted : ∀ op, sem.S.Reply op → Prop) (R : Reading sem.Dyn)
  (Run : Raw → List sem.Dyn → List sem.Dyn → Prop) (Valid : sem.Dyn → Prop)
  (undefined : sem.H → Prop)

/-- **The analysis of a definition is sound.** A body with distinct addresses that the analysis
under a summary refuses nowhere, on valid inputs of which every requirement of the summary holds,
and permitted replies: every loop that a run reaches respects the bound that the analysis
recorded for it, the body never stops `undefined` and returns valid values of which, with the
inputs, every guarantee of the summary holds, and its process runs the skeleton of the analysis
over its table. -/
theorem analyse_sound (laws : rules.Lawful sem permitted R Run Valid undefined)
    (lawful : checks.Lawful) (definition : Key) (role : Option Role) {types outs : List D.Ty}
    (summary : Summary Raw) (inputs : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (distinct : Term.Distinct body)
    (accepted : (analyse rules checks definition role summary inputs body).state.st.refusals = [])
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition → p.role = role →
      (p, b) ∈ (analyse rules checks definition role summary inputs body).state.st.bounds)
    (values : HList sem.Val types) (valid : ∀ v, v ∈ sem.dyns values → Valid v)
    (required : ∀ requirement, requirement ∈ summary.requires →
      requirement.Holds (ValidRun sem Run Valid) R (sem.dyns values)) :
    body.EveryLoop sem permitted (Annotation.Bounded ⟨F⟩ definition role) [] []
        (Env.empty.extend inputs values) ∧
      (body.denote sem [] (Env.empty.extend inputs values)).Every permitted
        (fun returned => (∀ v, v ∈ sem.dyns returned → Valid v) ∧
          ∀ guarantee, guarantee ∈ summary.ensures →
            guarantee.Holds (ValidRun sem Run Valid) R (sem.dyns values ++ sem.dyns returned))
        (fun stop => ¬ undefined stop) ∧
      Skel.Runs sem permitted Run
        (analyse rules checks definition role summary inputs body).state.st.table
        [] (Valuation.setFrom (fun _ => none) 0 (sem.dyns values))
        (analyse rules checks definition role summary inputs body).skel
        (body.denote sem [] (Env.empty.extend inputs values)) := by
  have safe := analyse_safe rules checks sem permitted R Run Valid undefined laws lawful definition
    role summary inputs body distinct accepted F recorded values valid required
  exact ⟨safe.1, safe.2,
    analyse_runs rules checks sem permitted Run undefined laws.binding definition role summary
      inputs body [] values
      (Process.every_mono _ permitted (fun _ _ => trivial) (fun _ stop => stop) safe.2)⟩

/-- **A definition that follows a safe definition is safe and means the same.** For two bodies
of the same types, of which the second has distinct addresses and follows the analysis of the
first, both under a summary, with no refusal and no place that differs, on valid inputs of which
every requirement of the summary holds and on which the first never stops `undefined`, and
permitted replies: every loop of the second respects the bound recorded for it, the second never
stops `undefined` and returns valid values of which, with the inputs, every guarantee of the
summary holds, and the two processes mean the same. How the first is known to be safe does not
matter: that the analysis accepts it is one way (`follow_sound`), following a safe body is
another. Nothing is assumed of the safety of the second; its addresses are distinct, which
elaboration decides. -/
theorem follow_assured (laws : rules.Lawful sem permitted R Run Valid undefined)
    (lawful : checks.Lawful) (definition definition' : Key) (role : Option Role)
    {types outs : List D.Ty} (summary : Summary Raw) (inputs inputs' : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs)
    (distinct' : Term.Distinct body')
    (followed : (follow rules checks definition' role summary
      (analyse rules checks definition role summary inputs body) inputs' body').accepted = true)
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition' → p.role = role →
      (p, b) ∈ (follow rules checks definition' role summary
        (analyse rules checks definition role summary inputs body) inputs' body').state.st.bounds)
    (values : HList sem.Val types) (valid : ∀ v, v ∈ sem.dyns values → Valid v)
    (required : ∀ requirement, requirement ∈ summary.requires →
      requirement.Holds (ValidRun sem Run Valid) R (sem.dyns values))
    (safe : (body.denote sem [] (Env.empty.extend inputs values)).Every permitted
      (fun _ => True) (fun stop => ¬ undefined stop)) :
    body'.EveryLoop sem permitted (Annotation.Bounded ⟨F⟩ definition' role) [] []
        (Env.empty.extend inputs' values) ∧
      (body'.denote sem [] (Env.empty.extend inputs' values)).Every permitted
        (fun returned => (∀ v, v ∈ sem.dyns returned → Valid v) ∧
          ∀ guarantee, guarantee ∈ summary.ensures →
            guarantee.Holds (ValidRun sem Run Valid) R (sem.dyns values ++ sem.dyns returned))
        (fun stop => ¬ undefined stop) ∧
      Process.SameWhen permitted (body.denote sem [] (Env.empty.extend inputs values))
        (body'.denote sem [] (Env.empty.extend inputs' values)) := by
  have second := follow_safe rules checks sem permitted R Run Valid undefined laws lawful
    definition definition' role summary inputs inputs' body body' distinct' followed F recorded
    values valid required
  have differs : (follow rules checks definition' role summary
      (analyse rules checks definition role summary inputs body) inputs' body').state.differs =
        [] := by
    simp only [Exit.accepted, Bool.and_eq_true, List.isEmpty_iff] at followed
    exact followed.2
  exact ⟨second.1, second.2,
    follow_same rules checks sem permitted Run undefined laws.binding lawful definition
      definition' role summary inputs inputs' body body' differs [] values safe
      (Process.every_mono _ permitted (fun _ _ => trivial) (fun _ stop => stop) second.2)⟩

/-- **A definition that follows an accepted definition is safe and means the same.** For two
bodies with distinct addresses and the same types, of which the first is refused nowhere and the
second follows the first with no refusal and no place that differs, both under a summary, on
valid inputs of which every requirement of the summary holds, and permitted replies: every loop
of the second respects the bound recorded for it, the second never stops `undefined` and returns
valid values of which, with the inputs, every guarantee of the summary holds, and the two
processes mean the same. It is `follow_assured`, the first being safe since the analysis accepts
it (`analyse_safe`). -/
theorem follow_sound (laws : rules.Lawful sem permitted R Run Valid undefined)
    (lawful : checks.Lawful) (definition definition' : Key) (role : Option Role)
    {types outs : List D.Ty} (summary : Summary Raw) (inputs inputs' : Names types)
    (body : Term D (Ctx.empty.extend inputs) outs)
    (body' : Term D (Ctx.empty.extend inputs') outs)
    (distinct : Term.Distinct body) (distinct' : Term.Distinct body')
    (accepted : (analyse rules checks definition role summary inputs body).state.st.refusals = [])
    (followed : (follow rules checks definition' role summary
      (analyse rules checks definition role summary inputs body) inputs' body').accepted = true)
    (F : List (Place × Nat))
    (recorded : ∀ p b, (p, b) ∈ F → p.definition = definition' → p.role = role →
      (p, b) ∈ (follow rules checks definition' role summary
        (analyse rules checks definition role summary inputs body) inputs' body').state.st.bounds)
    (values : HList sem.Val types) (valid : ∀ v, v ∈ sem.dyns values → Valid v)
    (required : ∀ requirement, requirement ∈ summary.requires →
      requirement.Holds (ValidRun sem Run Valid) R (sem.dyns values)) :
    body'.EveryLoop sem permitted (Annotation.Bounded ⟨F⟩ definition' role) [] []
        (Env.empty.extend inputs' values) ∧
      (body'.denote sem [] (Env.empty.extend inputs' values)).Every permitted
        (fun returned => (∀ v, v ∈ sem.dyns returned → Valid v) ∧
          ∀ guarantee, guarantee ∈ summary.ensures →
            guarantee.Holds (ValidRun sem Run Valid) R (sem.dyns values ++ sem.dyns returned))
        (fun stop => ¬ undefined stop) ∧
      Process.SameWhen permitted (body.denote sem [] (Env.empty.extend inputs values))
        (body'.denote sem [] (Env.empty.extend inputs' values)) :=
  follow_assured rules checks sem permitted R Run Valid undefined laws lawful definition
    definition' role summary inputs inputs' body body' distinct' followed F recorded values valid
    required
    (Process.every_mono _ permitted (fun _ _ => trivial) (fun _ stop => stop)
      (analyse_safe rules checks sem permitted R Run Valid undefined laws lawful definition role
        summary inputs body distinct accepted [] (fun _ _ inside => nomatch inside) values valid
        required).2)

/-- **A body that the analysis under a summary refuses nowhere satisfies the summary.** As a
function of its inputs, a body with distinct addresses that the analysis under a summary refuses
nowhere satisfies it in the sense of `Summary.Holds`, with the relation of written operations on
valid values (`ValidRun`): on valid inputs of which every requirement holds, on permitted
replies, it never stops `undefined`, and what it returns is valid and, with the inputs,
satisfies every guarantee. -/
theorem analyse_holds (laws : rules.Lawful sem permitted R Run Valid undefined)
    (lawful : checks.Lawful) (definition : Key) (role : Option Role) {types outs : List D.Ty}
    (summary : Summary Raw) (inputs : Names types) (body : Term D (Ctx.empty.extend inputs) outs)
    (distinct : Term.Distinct body)
    (accepted : (analyse rules checks definition role summary inputs body).state.st.refusals = []) :
    Summary.Holds sem permitted R (ValidRun sem Run Valid) Valid undefined summary
      (fun values => body.denote sem [] (Env.empty.extend inputs values)) :=
  fun values valid required =>
    (analyse_safe rules checks sem permitted R Run Valid undefined laws lawful definition role
      summary inputs body distinct accepted [] (fun _ _ inside => nomatch inside) values valid
      required).2

end

end Zkc.Core.Analysis
