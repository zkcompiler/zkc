module

public import Zkc.Core.Facts.Body.GuardSound

@[expose] public section

/-!
The three properties of the arms of a case analysis (`ArmsNilGrowsStatement`,
`ArmsConsGrowsStatement`, `ArmsNilRunsStatement`, `ArmsConsRunsStatement`,
`ArmsNilSoundStatement`, `ArmsConsSoundStatement`) and of a case analysis from those of its arms
(`CasesGrowsStatement`, `CasesRunsStatement`, `CasesSoundStatement`).
-/

namespace Zkc.Core.BodyAnalysis

/-! ## Growth -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw) (notes : Annotations Raw)

/-- No arms grow nothing. -/
theorem armsNilGrows : ArmsNilGrowsStatement cfg notes := by
  intro cursor Γ mid ids s k wf
  simp only [walkArms, Arms.leafCount]
  exact Grew.of_entered cfg _ (State.Entered.refl wf)

/-- **Arms grow the state when the first arm and the others do**: by the leaf of the first arm's
payload, the first arm's leaves and the others'. -/
theorem armsConsGrows : ArmsConsGrowsStatement cfg notes := by
  intro cursor Γ mid payload payloads inputs arm rest growsArm growsRest ids s k wf
  simp only [walkArms, Arms.leafCount, Arms.addresses]
  have one : Grew cfg (Term.addresses cursor.blocks arm ++ Arms.addresses cursor.blocks rest) s
      { s with leaves := s.leaves + 1 } 1 := Grew.leaves 1 wf
  have two := Grew.discount (cfg.domain.leaves k [(.leaf s.leaves, payload)])
    (growsArm (bindIds ids inputs [.leaf s.leaves]) { s with leaves := s.leaves + 1 }
      (cfg.domain.leaves k [(.leaf s.leaves, payload)]) wf)
  have three := growsRest ids _ k two.2.1
  exact (one.trans (two.widen fun _ m => List.mem_append_left _ m)).trans
    (three.widen fun _ m => List.mem_append_right _ m)

/-- **A case analysis grows the state when its arms do**: by its arms' leaves and its results. -/
theorem casesGrows : CasesGrowsStatement cfg notes := by
  intro cursor key Γ mid payloads t w x ok gives arms growsArms ids s k wf
  have entry := atEntry_entered cfg notes (.instruction cursor key) ids s k wf
  simp only [walkInstr, casesExit, Instr.leafCount]
  have armsGrew := growsArms ids _ (atEntry cfg notes (.instruction cursor key) ids s k).2 entry.wf
  exact (((Grew.of_entered cfg _ entry).trans
    (armsGrew.widen fun _ m => List.mem_cons_of_mem _ m)).trans
    (Grew.leaves mid.length armsGrew.2.1)).count (by rw [Nat.zero_add])

end

/-! ## Running the skeleton -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

/-- No arms run, there being no alternative. -/
theorem armsNilRuns : ArmsNilRunsStatement σ := by
  intro cursor Γ mid path ρ ids env s k table pick
  exact nomatch pick

/-- **Arms run their skeletons when the first arm and the others do**: at the first alternative
the first arm runs alone, its payload on its input leaf; at another, the others run from the state
after the first arm. -/
theorem armsConsRuns : ArmsConsRunsStatement σ := by
  intro cursor Γ mid payload payloads inputs arm rest growsArm growsRest runsArm runsRest
  intro path ρ ids env s k table pick
  dsimp only
  intro scope sub notUndefined
  simp only [walkArms] at sub ⊢
  have armGrew := growsArm (bindIds ids inputs [.leaf s.leaves]) { s with leaves := s.leaves + 1 }
    (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)]) scope.wf
  have runsOne := fun v => runsArm path (ρ.setFrom s.leaves [⟨payload, v⟩])
    (bindIds ids inputs [.leaf s.leaves]) (env.extend inputs (.cons v .nil))
    { s with leaves := s.leaves + 1 } (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)]) table
    .nil (fun values => .done values)
  generalize walk σ.cfg σ.notes cursor.arm arm (bindIds ids inputs [.leaf s.leaves])
    { s with leaves := s.leaves + 1 } (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)]) = inner
    at armGrew runsOne sub ⊢
  have armDiscounted := Grew.discount (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)]) armGrew
  have restGrew := growsRest ids _ k armDiscounted.2.1
  have innerLe : inner.state.values.table.Le
      (discount σ.cfg (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)])
        { s with leaves := s.leaves + 1 } inner.state).values.table := by
    rw [discount_values]
    exact Table.Le.refl _
  cases pick with
  | here v =>
      rw [Arms.denote_cons] at notUndefined ⊢
      refine SkelArms.Runs.here ?_
      have runs := runsOne v
      rw [Process.bind_pure] at runs
      refine runs (scope.enterLeaf inputs v) ((innerLe.trans restGrew.1).trans sub) ?_
        fun _ values _ _ _ _ => .done values
      exact notUndefined
  | there p =>
      rw [Arms.denote_cons] at notUndefined ⊢
      refine SkelArms.Runs.there ?_
      obtain ⟨table₁, wf₁, next₁, leaves₁, -⟩ := (Grew.leaves (cfg := σ.cfg)
        (addresses := Term.addresses cursor.blocks arm) 1 scope.wf).trans armDiscounted
      exact runsRest path ρ ids env _ k table p
        (scope.grow ⟨table₁, wf₁, next₁⟩ (by rw [leaves₁]; exact Nat.le_add_right _ _)) sub
        notUndefined

/-- **A case analysis runs its entry of the skeleton when its arms run theirs**: the arm of the
subject's alternative runs alone; what follows runs from every value that it can return, on the
case analysis's result leaves. -/
theorem casesRuns : CasesRunsStatement σ := by
  intro cursor key Γ mid payloads t w x ok gives arms growsArms runsArms
  intro path ρ ids env s k table mid₀ outs rest after cont
  dsimp only
  intro scope sub notUndefined next
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k scope.wf
  have subject := scope.idOf_reads x
  rw [Instr.denote_cases] at notUndefined ⊢
  simp only [walkInstr, casesExit, Skel.stepOf] at sub next ⊢
  have armsGrew := growsArms ids (atEntry σ.cfg σ.notes (.instruction cursor key) ids s k).1
    (atEntry σ.cfg σ.notes (.instruction cursor key) ids s k).2 entry.wf
  have runs := runsArms path ρ ids env (atEntry σ.cfg σ.notes (.instruction cursor key) ids s k).1
    (atEntry σ.cfg σ.notes (.instruction cursor key) ids s k).2 table (σ.sem.pick ok (env.get x))
  generalize walkArms σ.cfg σ.notes (cursor.region key) arms ids (atEntry σ.cfg σ.notes (.instruction cursor key) ids s k).1
    (atEntry σ.cfg σ.notes (.instruction cursor key) ids s k).2 = armsExit at armsGrew runs sub next ⊢
  have fresh : ∀ n, armsExit.state.leaves ≤ n → ρ n = none := fun n above =>
    scope.fresh n (by
      rw [armsGrew.2.2.2.1, entry.2.1] at above
      exact Nat.le_trans (Nat.le_add_right _ _) above)
  refine Skel.Runs.cases (env.get x)
    (Reads.mono ((entry.1.1.trans armsGrew.1).trans sub) (fun _ _ h => h) subject)
    (runs (scope.grow entry.1 (Nat.le_of_eq entry.2.1.symm)) sub
      (Process.Every.of_bind notUndefined)) fun returned returns => ?_
  obtain ⟨le, fresh', reads⟩ := Leaves.results (Run := σ.Run) (R := σ.R)
    (table := armsExit.state.values.table) fresh returned
  exact next _ returned le fresh' reads (Process.Every.of_bind_canReturn notUndefined returns)

end

/-! ## Soundness -/

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

/-- No arms are sound, there being no alternative. -/
theorem armsNilSound : ArmsNilSoundStatement σ := by
  intro cursor Γ mid path ρ ids env s k pick
  exact nomatch pick

/-- **Arms are sound when the first arm and the others are.** At the first alternative the first
arm runs from its payload on a new leaf, from a domain's state that means it, so that state is not
dead and the arm's refusals count; what it returns is what `Returned` says of its exit, under the
state after all arms. At another alternative the others run from the state after the first arm,
whose refusals, counted or dropped, are none. -/
theorem armsConsSound : ArmsConsSoundStatement σ := by
  intro cursor Γ mid payload payloads inputs arm rest growsArm growsRest soundArm soundRest
  intro path ρ ids env s k pick
  dsimp only
  intro pickValid inv defined everyFact unchanged
  simp only [walkArms, Arms.addresses] at unchanged ⊢
  have armGrew := growsArm (bindIds ids inputs [.leaf s.leaves]) { s with leaves := s.leaves + 1 }
    (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)]) inv.wf
  have soundOne := fun v => soundArm path (ρ.setFrom s.leaves [⟨payload, v⟩])
    (bindIds ids inputs [.leaf s.leaves]) (env.extend inputs (.cons v .nil))
    { s with leaves := s.leaves + 1 } (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)])
  generalize walk σ.cfg σ.notes cursor.arm arm (bindIds ids inputs [.leaf s.leaves])
    { s with leaves := s.leaves + 1 } (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)]) = inner
    at armGrew soundOne unchanged ⊢
  have one := (Grew.leaves (cfg := σ.cfg) (addresses := Term.addresses cursor.blocks arm) 1
    inv.wf).trans (Grew.discount (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)]) armGrew)
  have restGrew := growsRest ids _ k one.2.1
  have soundTwo := soundRest path ρ ids env
    (discount σ.cfg (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)])
      { s with leaves := s.leaves + 1 } inner.state) k
  generalize walkArms σ.cfg σ.notes cursor.next rest ids
    (discount σ.cfg (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)])
      { s with leaves := s.leaves + 1 } inner.state) k = others
    at restGrew soundTwo unchanged ⊢
  obtain ⟨discountUnchanged, othersUnchanged⟩ :=
    refusals_split one.2.2.2.2.1 restGrew.2.2.2.2.1 unchanged
  have sTable : s.values.table.Le others.state.values.table := one.1.trans restGrew.1
  cases pick with
  | here v =>
      have inv₁ := inv.enterLeaf inputs v pickValid
      have alive := σ.alive inv₁.means
      rw [discount_alive alive] at one restGrew discountUnchanged
      simp only [Arms.EveryFact, Arms.EveryStep] at everyFact
      obtain ⟨every, required, loops⟩ := soundOne v inv₁ defined.1 everyFact discountUnchanged
      have innerOthers : inner.state.leaves ≤ others.state.leaves := by
        rw [restGrew.2.2.2.1]
        exact Nat.le_add_right _ _
      rw [Arms.denote_cons]
      simp only [Arms.EveryRequired, Arms.EveryStep, Arms.EveryLoop]
      refine ⟨Process.every_mono _ _ (fun values ret => ?_) (fun _ h => h) every, required,
        fun nodup apart recorded => ?_⟩
      · obtain ⟨ρ₂, le₂, inv₂, reads₂⟩ := ret
        refine ⟨inner.known, inner.returned,
          List.mem_append_left _ (mem_live σ (σ.alive inv₂.means) _), ρ₂,
          fun n w h => le₂ n w (Leaves.le_setFrom inv.fresh _ n w h),
          ⟨⟨fun n above => inv₂.fresh n (Nat.le_trans innerOthers above), fun τ x => ?_,
            inv.bound, restGrew.2.1⟩, inv₂.valid, σ.domain.mono restGrew.1 (fun _ _ h => h)
              inv₂.means⟩,
          ReadsAll.mono restGrew.1 (fun _ _ h => h) reads₂⟩
        obtain ⟨id, found, read⟩ := inv.agree τ x
        exact ⟨id, found, Reads.mono sTable
          (fun n w h => le₂ n w (Leaves.le_setFrom inv.fresh _ n w h)) read⟩
      · obtain ⟨nodupArm, -, disjoint⟩ := nodup_append_parts nodup
        obtain ⟨-, -, -, -, -, new, bounds, added⟩ := restGrew
        exact loops nodupArm
          (fun q m bl key place at_ => apart q m bl key place (List.mem_append_left _ at_))
          (Recorded.before recorded (fun a m => List.mem_append_left _ m) disjoint
            ⟨new, bounds, added⟩)
  | there p =>
      obtain ⟨table₁, wf₁, next₁, leaves₁, -, new, bounds, added⟩ := one
      have inv' : Inv σ ρ ids env k
          (discount σ.cfg (σ.cfg.domain.leaves k [(.leaf s.leaves, payload)])
            { s with leaves := s.leaves + 1 } inner.state) :=
        ⟨inv.toScope.grow ⟨table₁, wf₁, next₁⟩ (by rw [leaves₁]; exact Nat.le_add_right _ _),
          inv.valid, σ.domain.mono table₁ (fun _ _ h => h) inv.means⟩
      simp only [Arms.EveryFact, Arms.EveryStep] at everyFact
      obtain ⟨every, required, loops⟩ := soundTwo p pickValid inv' defined.2 everyFact
        othersUnchanged
      rw [Arms.denote_cons]
      simp only [Arms.EveryRequired, Arms.EveryStep, Arms.EveryLoop]
      refine ⟨Process.every_mono _ _ (fun values found => ?_) (fun _ h => h) every, required,
        fun nodup apart recorded => ?_⟩
      · obtain ⟨known, returned, member, ret⟩ := found
        exact ⟨known, returned, List.mem_append_right _ member, ret⟩
      · obtain ⟨-, nodupRest, disjoint⟩ := nodup_append_parts nodup
        exact loops nodupRest
          (BoundsApart.after apart (fun a m => List.mem_append_right _ m)
            (fun a inRest inArm => disjoint a inArm inRest) ⟨new, bounds, added⟩)
          (Recorded.before (B := []) recorded (fun a m => List.mem_append_right _ m)
            (fun _ _ m => nomatch m) ⟨[], rfl, fun _ m => nomatch m⟩)

/-- **A case analysis is sound when its arms are**: the subject's alternative is valid, the arm
that runs returns what `Returned` says of one of the exits told to `after`, an exit that asks
nobody, and the case analysis's results are new leaves that read what that arm returned. -/
theorem casesSound : CasesSoundStatement σ := by
  intro laws cursor key Γ mid payloads t w x ok gives arms growsArms soundArms
  intro path ρ ids env s k
  dsimp only
  intro inv steps defined facts everyFact unchanged
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k inv.wf
  have entryInv := fun unchanged => atEntry_inv σ laws cursor key (.cases w x ok gives arms)
    (path := path) inv steps facts unchanged
  have subject := inv.toScope.idOf_reads x
  have pickValid := laws.rules.pick ok (env.get x) (Reads.valid inv.valid subject)
  rw [Instr.denote_cases]
  simp only [walkInstr, casesExit] at unchanged ⊢
  simp only [Instr.site] at entryInv
  generalize atEntry σ.cfg σ.notes (.instruction cursor key) ids s k = e at entry entryInv unchanged ⊢
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry entryInv unchanged ⊢
  have armsGrew := growsArms ids E Ek entry.wf
  have soundA := soundArms path ρ ids env E Ek (σ.sem.pick ok (env.get x)) pickValid
  generalize walkArms σ.cfg σ.notes (cursor.region key) arms ids E Ek = armsExit
    at armsGrew soundA unchanged ⊢
  obtain ⟨entryUnchanged, armsUnchanged⟩ := refusals_split entry.2.2.2 armsGrew.2.2.2.2.1 unchanged
  have inv₁ := entryInv entryUnchanged
  simp only [Instr.EveryFact, Instr.EveryStep] at everyFact
  obtain ⟨every, required, loops⟩ := soundA inv₁ defined everyFact armsUnchanged
  simp only [Instr.EveryRequired, Instr.EveryStep, Instr.EveryLoop]
  refine ⟨Process.every_mono _ _ (fun values found => ?_) (fun _ h => h) every, trivial, required,
    fun nodup apart recorded => ?_⟩
  · obtain ⟨known, returned, member, ρ₂, le, inv₂, reads⟩ := found
    exact Returned.atResults le inv₂.toScope inv₂.valid
      (σ.domain.mono armsGrew.1 le inv₁.means) member inv₂.means reads
  · obtain ⟨-, nodup'⟩ := List.nodup_cons.mp nodup
    refine loops nodup' ?_ fun p b bl key' inF place at_ =>
      recorded p b bl key' inF place (List.mem_cons_of_mem _ at_)
    rw [BoundsApart, entry.2.2.1]
    exact fun q m bl key' place at_ => apart q m bl key' place (List.mem_cons_of_mem _ at_)

end

end Zkc.Core.BodyAnalysis
