module

public import Zkc.Core.Facts.Body.ChooseSound

@[expose] public section

/-!
The step that binds an instruction's results: `ReturnedBindStatement`, and the three properties of
an exit (`RetGrowsStatement`, `RetRunsStatement`, `RetSoundStatement`) and of a step
(`StepGrowsStatement`, `StepRunsStatement`, `StepSoundStatement`). Nothing in them is about the
kind of instruction: a step uses only the three properties of its instruction and of its rest.
Names bound to identifiers keep the scope (`Scope.bind`), and so does a region's input on a new
leaf, with the invariant (`Scope.enterLeaf`, `Inv.enterLeaf`).
-/

namespace Zkc.Core.BodyAnalysis

/-! ## Binding names -/

section
variable {D : Dialect} {Raw : Type} {sem : Semantics D}
  {Run : Raw → List sem.Dyn → List sem.Dyn → Prop} {R : Reading sem.Dyn}

/-- **One more name bound keeps the scope**, when its identifier reads its value: at the name
bound, the identifier and the value bound; at another name, those of before. -/
theorem Scope.insert {Γ : Ctx D.Ty} {ρ : Leaves sem.Dyn} {ids : Ctx Ident} {env : Env sem.Val Γ}
    {s : State Raw} (scope : Scope sem Run R ρ ids env s) (name : Name) {τ : D.Ty} {v : sem.Val τ}
    {i : Ident} (read : Reads Run R.bool s.values.table ρ i ⟨τ, v⟩) :
    Scope sem Run R ρ (ids.insert name i) (env.insert name v) s := by
  refine ⟨scope.fresh, fun τ' x => ?_, fun name' id found => ?_, scope.wf⟩
  · by_cases same : x.name = name
    · have typed := x.typed
      rw [Ctx.find?_insert, ite_eq_left same] at typed
      cases typed
      refine ⟨i, by rw [Ctx.find?_insert, ite_eq_left same], ?_⟩
      have value := Env.insert_at_bound env name v same x.typed
      have equal : (env.insert name v).get x = v := eq_of_heq value
      rw [equal]
      exact read
    · have typed := x.typed
      rw [Ctx.find?_insert, ite_eq_right same] at typed
      obtain ⟨id, found, one⟩ := scope.agree τ' ⟨x.name, typed⟩
      refine ⟨id, by rw [Ctx.find?_insert, ite_eq_right same]; exact found, ?_⟩
      have equal : (env.insert name v).get x = env.get ⟨x.name, typed⟩ :=
        Env.insert_at_other env name v same x.typed
      rw [equal]
      exact one
  · by_cases same : name' = name
    · exact ⟨τ, by rw [Ctx.find?_insert, ite_eq_left same]⟩
    · rw [Ctx.find?_insert, ite_eq_right same] at found
      obtain ⟨τ', typed⟩ := scope.bound name' id found
      exact ⟨τ', by rw [Ctx.find?_insert, ite_eq_right same]; exact typed⟩

/-- **The names of a binding bound to identifiers that read the values bound keep the scope**: the
one place where names are bound. -/
theorem Scope.bind {Γ : Ctx D.Ty} {ρ : Leaves sem.Dyn} {ids : Ctx Ident} {env : Env sem.Val Γ}
    {s : State Raw} (scope : Scope sem Run R ρ ids env s) :
    ∀ {mid : List D.Ty} (results : Names mid) (returned : List Ident) (values : HList sem.Val mid),
      ReadsAll Run R.bool s.values.table ρ returned (sem.dyns values) →
      Scope sem Run R ρ (bindIds ids results returned) (env.extend results values) s
  | [], .nil, _, .nil, _ => scope
  | _ :: _, .cons name rest, returned, .cons v vs, reads => by
      have reads' : ReadsAll Run R.bool s.values.table ρ returned (⟨_, v⟩ :: sem.dyns vs) := reads
      cases reads' with
      | cons first others => exact (scope.insert name first).bind rest _ vs others

/-- **A region's input on a new leaf keeps the scope**: the leaf at the counter set to the value of
the input, the input's name bound to that leaf and to the value, the counter one more. -/
theorem Scope.enterLeaf {Γ : Ctx D.Ty} {ρ : Leaves sem.Dyn} {ids : Ctx Ident}
    {env : Env sem.Val Γ} {s : State Raw} (scope : Scope sem Run R ρ ids env s) {τ : D.Ty}
    (inputs : Names [τ]) (v : sem.Val τ) :
    Scope sem Run R (ρ.setFrom s.leaves [⟨τ, v⟩]) (bindIds ids inputs [.leaf s.leaves])
      (env.extend inputs (.cons v .nil)) { s with leaves := s.leaves + 1 } := by
  have widened : Scope sem Run R (ρ.setFrom s.leaves [⟨τ, v⟩]) ids env
      { s with leaves := s.leaves + 1 } :=
    ⟨Leaves.setFrom_fresh scope.fresh [⟨τ, v⟩], fun τ' x => by
        obtain ⟨id, found, read⟩ := scope.agree τ' x
        exact ⟨id, found, Reads.mono (Table.Le.refl _) (Leaves.le_setFrom scope.fresh _) read⟩,
      scope.bound, scope.wf⟩
  exact widened.bind inputs [.leaf s.leaves] (.cons v .nil)
    (ReadsAll.setFrom (Run := Run) (truth := R.bool) ρ s.leaves [⟨τ, v⟩])

end

section
variable {D : Dialect} {Raw : Type} {σ : Setting D Raw}

/-- **A region's input on a new leaf keeps the invariant**, with the domain told of the leaf and
its type: the input's value is valid. -/
theorem Inv.enterLeaf {Γ : Ctx D.Ty} {ρ : Leaves σ.sem.Dyn} {ids : Ctx Ident}
    {env : Env σ.sem.Val Γ} {k : σ.cfg.domain.State} {s : State Raw} (inv : Inv σ ρ ids env k s)
    {τ : D.Ty} (inputs : Names [τ]) (v : σ.sem.Val τ) (valid : σ.Valid ⟨τ, v⟩) :
    Inv σ (ρ.setFrom s.leaves [⟨τ, v⟩]) (bindIds ids inputs [.leaf s.leaves])
      (env.extend inputs (.cons v .nil)) (σ.cfg.domain.leaves k [(.leaf s.leaves, τ)])
      { s with leaves := s.leaves + 1 } := by
  have le := Leaves.le_setFrom inv.fresh [(⟨τ, v⟩ : σ.sem.Dyn)]
  refine ⟨inv.toScope.enterLeaf inputs v, Leaves.setFrom_valid inv.valid fun x m => ?_,
    σ.domain.leaves inv.wf.slots (σ.domain.mono (Table.Le.refl _) le inv.means) fun p m => ?_⟩
  · rcases List.mem_cons.mp m with rfl | m
    · exact valid
    · cases m
  · rcases List.mem_cons.mp m with rfl | m
    · have at_ := Leaves.setFrom_at ρ s.leaves [(⟨τ, v⟩ : σ.sem.Dyn)] (j := 0) (Nat.zero_lt_succ _)
      rw [Nat.add_zero] at at_
      exact ⟨⟨τ, v⟩, .leaf at_, valid, rfl⟩
    · cases m

end

section
variable {D : Dialect} {Raw : Type} (σ : Setting D Raw)

/-- **What `Returned` says is the invariant of the results bound to the names.** -/
theorem returnedBind : ReturnedBindStatement σ := by
  intro Γ mid ρ ids env k s returned values ret
  obtain ⟨ρ', le, inv, reads⟩ := ret
  exact ⟨ρ', le, fun results => ⟨inv.toScope.bind results returned values reads, inv.valid,
    inv.means⟩⟩


end

/-! ## An exit -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw]

/-- An exit grows nothing. -/
theorem retGrows (cfg : Config D Raw) (notes : Annotations Raw) : RetGrowsStatement cfg notes :=
  fun _ _ _ _ _ s _ wf => Grew.of_entered cfg _ (State.Entered.refl (s := s) wf)

/-- An exit runs its skeleton: it reads its names' values, and the rests run from the same
leaves. -/
theorem retRuns (σ : Setting D Raw) : RetRunsStatement σ := by
  intro _ cursor Γ outs exit path ρ ids env s k table outs' after cont
  dsimp only
  intro scope sub notUndefined next
  exact Skel.Runs.ret (env.all exit)
    (ReadsAll.mono sub (fun _ _ h => h) (scope.idsOf_reads exit))
    (next ρ (env.all exit) (fun _ _ h => h) scope.fresh (scope.idsOf_reads exit) notUndefined)

/-- An exit is sound: it returns the values of its names, which its identifiers read. -/
theorem retSound (σ : Setting D Raw) : RetSoundStatement σ := by
  intro _ cursor Γ outs exit path ρ ids env s k
  dsimp only
  intro inv _ _ _
  exact ⟨⟨ρ, fun _ _ h => h, inv, inv.toScope.idsOf_reads exit⟩, trivial, fun _ _ _ => trivial⟩

end

/-! ## A step -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw]

/-- **A step grows the state** as its instruction does, then the rest. -/
theorem stepGrows (cfg : Config D Raw) (notes : Annotations Raw) : StepGrowsStatement cfg notes := by
  intro cursor Γ mid outs key i results rest growsI growsR ids s k wf
  have one := growsI ids s k wf
  have two := growsR (bindIds ids results (walkInstr cfg notes cursor key i ids s k).returned)
    (walkInstr cfg notes cursor key i ids s k).state (walkInstr cfg notes cursor key i ids s k).known
    one.2.1
  exact (one.widen (fun a m => List.mem_append_left _ m)).trans
    (two.widen fun a m => List.mem_append_right _ m)

/-- **A step runs its skeleton** when its instruction runs its entry and the rest runs its
skeleton: what follows the instruction is the rest, run from the leaves at every exit of the
instruction with its results bound to the step's names. -/
theorem stepRuns (σ : Setting D Raw) : StepRunsStatement σ := by
  intro _ cursor Γ mid outs key i results rest growsI growsR runsI runsR
  intro path ρ ids env s k table outs' after cont
  dsimp only
  intro scope sub notUndefined next
  rw [Term.denote_step, Process.bind_assoc] at notUndefined ⊢
  simp only [walk] at sub next ⊢
  have one := growsI ids s k scope.wf
  have runsOne := runsI path ρ ids env s k table
    (walk σ.cfg σ.notes cursor.next rest (bindIds ids results (walkInstr σ.cfg σ.notes cursor key i ids s k).returned)
      (walkInstr σ.cfg σ.notes cursor key i ids s k).state
      (walkInstr σ.cfg σ.notes cursor key i ids s k).known).skel after
    (fun values => (rest.denote σ.sem path (env.extend results values)).bind cont)
  have two := fun ids' => growsR ids' (walkInstr σ.cfg σ.notes cursor key i ids s k).state
    (walkInstr σ.cfg σ.notes cursor key i ids s k).known one.2.1
  have runsTwo := fun ρ' values => runsR path ρ' (bindIds ids results
    (walkInstr σ.cfg σ.notes cursor key i ids s k).returned) (env.extend results values)
    (walkInstr σ.cfg σ.notes cursor key i ids s k).state
    (walkInstr σ.cfg σ.notes cursor key i ids s k).known table after cont
  generalize walkInstr σ.cfg σ.notes cursor key i ids s k = first
    at sub next one two runsOne runsTwo ⊢
  have twoHere := two (bindIds ids results first.returned)
  generalize walk σ.cfg σ.notes cursor.next rest (bindIds ids results first.returned) first.state
    first.known = second at sub next twoHere runsOne runsTwo ⊢
  refine runsOne scope (twoHere.1.trans sub) notUndefined
    fun ρ' values le fresh reads undefined => ?_
  have scopeOne : Scope σ.sem σ.Run σ.R ρ' ids env first.state :=
    ⟨fresh, fun τ x => by
        obtain ⟨id, found, read⟩ := scope.agree τ x
        exact ⟨id, found, Reads.mono one.1 le read⟩,
      scope.bound, one.2.1⟩
  exact runsTwo ρ' values (scopeOne.bind results first.returned values reads) sub undefined
    fun ρ'' values' le' fresh' reads' undefined' =>
      next ρ'' values' (fun n v h => le' n v (le n v h)) fresh' reads' undefined'

/-- **A step is sound** when its instruction and the rest are: the rest from what `Returned` says
of the instruction, with its results bound to the step's names (`Scope.bind`); what the rest
returns is what `Returned` says for the scope of before the step, whose identifiers still read
their values. -/
theorem stepSound (σ : Setting D Raw) : StepSoundStatement σ := by
  intro _ cursor Γ mid outs key i results rest growsI growsR soundI soundR
  intro path ρ ids env s k
  dsimp only
  intro inv defined everyFact unchanged
  obtain ⟨steps, definedI, definedR⟩ := defined
  obtain ⟨factsI, everyFactI, everyFactR⟩ := everyFact
  simp only [walk] at unchanged ⊢
  have one := growsI ids s k inv.wf
  have soundOne := soundI path ρ ids env s k inv steps definedI factsI everyFactI
  have two := fun ids' => growsR ids' (walkInstr σ.cfg σ.notes cursor key i ids s k).state
    (walkInstr σ.cfg σ.notes cursor key i ids s k).known one.2.1
  have soundTwo := fun ρ' values => soundR path ρ' (bindIds ids results
    (walkInstr σ.cfg σ.notes cursor key i ids s k).returned) (env.extend results values)
    (walkInstr σ.cfg σ.notes cursor key i ids s k).state
    (walkInstr σ.cfg σ.notes cursor key i ids s k).known
  generalize walkInstr σ.cfg σ.notes cursor key i ids s k = first
    at unchanged one two soundOne soundTwo ⊢
  have twoHere := two (bindIds ids results first.returned)
  generalize walk σ.cfg σ.notes cursor.next rest (bindIds ids results first.returned) first.state
    first.known = second at unchanged twoHere soundTwo ⊢
  obtain ⟨firstUnchanged, secondUnchanged⟩ :=
    refusals_split one.2.2.2.2.1 twoHere.2.2.2.2.1 unchanged
  obtain ⟨everyI, requiredI, everyRequiredI, loopsI⟩ := soundOne firstUnchanged
  -- What the rest gives, at every value that the instruction returns.
  have perValue := Process.every_mono _ _ (Q := fun values =>
      (rest.denote σ.sem path (env.extend results values)).Every σ.permitted
          (Returned σ ρ ids env second.known second.state second.returned)
          (fun stop => ¬ σ.undefined stop) ∧
        Term.EveryRequired σ cursor.next rest path (env.extend results values) ∧
        ((Term.addresses cursor.blocks rest).Nodup →
          BoundsApart σ first.state (Term.addresses cursor.blocks rest) →
          Recorded σ (Term.addresses cursor.blocks rest) second.state →
          Term.EveryLoop σ.sem σ.permitted σ.Bounded rest path cursor.blocks
            (env.extend results values)))
    (T := fun stop => ¬ σ.undefined stop)
    (fun values both => by
      obtain ⟨⟨ρ₁, le, inv₁, reads₁⟩, factsR⟩ := both
      obtain ⟨everyR, requiredR, loopsR⟩ := soundTwo ρ₁ values
        ⟨inv₁.toScope.bind results first.returned values reads₁, inv₁.valid, inv₁.means⟩
        definedR factsR secondUnchanged
      refine ⟨Process.every_mono _ _ (fun returned ret => ?_) (fun _ h => h) everyR, requiredR,
        loopsR⟩
      obtain ⟨ρ₂, le₂, inv₂, reads₂⟩ := ret
      refine ⟨ρ₂, fun n v h => le₂ n v (le n v h), ⟨⟨inv₂.fresh, fun τ x => ?_, inv.bound, inv₂.wf⟩,
        inv₂.valid, inv₂.means⟩, reads₂⟩
      obtain ⟨id, found, read⟩ := inv₁.agree τ x
      exact ⟨id, found, Reads.mono twoHere.1 le₂ read⟩)
    (fun _ both => both.1)
    (Process.every_and _ _ everyI everyFactR)
  refine ⟨?_, ⟨requiredI, everyRequiredI,
    Process.every_mono _ _ (fun _ each => each.2.1) (fun _ _ => trivial) perValue⟩,
    fun nodup apart recorded => ?_⟩
  · rw [Term.denote_step, Process.every_bind]
    exact Process.every_mono _ _ (fun _ each => each.1) (fun _ h => h) perValue
  · obtain ⟨nodupI, nodupR, disjoint⟩ := nodup_append_parts nodup
    obtain ⟨-, -, -, -, -, newI, boundsI, addedI⟩ := one
    obtain ⟨-, -, -, -, -, newR, boundsR, addedR⟩ := twoHere
    refine ⟨loopsI nodupI (fun q m bl key' place at_ =>
        apart q m bl key' place (List.mem_append_left _ at_))
      (Recorded.before recorded (fun a m => List.mem_append_left _ m) disjoint
        ⟨newR, boundsR, addedR⟩), ?_⟩
    refine Process.every_mono _ _ (fun _ each => each.2.2 nodupR ?_ ?_) (fun _ _ => trivial) perValue
    · exact BoundsApart.after apart (fun a m => List.mem_append_right _ m)
        (fun a inR inI => disjoint a inI inR) ⟨newI, boundsI, addedI⟩
    · exact Recorded.before (B := []) recorded (fun a m => List.mem_append_right _ m)
        (fun _ _ m => nomatch m) ⟨[], rfl, fun _ m => nomatch m⟩

end

end Zkc.Core.BodyAnalysis
