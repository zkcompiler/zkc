module

public import Zkc.Core.Facts.Body.BlockSound

@[expose] public section

/-!
The three properties of an attempt from those of its body: `AttemptGrowsStatement`,
`AttemptRunsStatement`, `AttemptSoundStatement`. An attempt makes a leaf for its number, walks its
body, and makes leaves for its results; its body runs alone on every number that its beginning
gives, and what follows it runs from every end of the attempt that can return.
-/

namespace Zkc.Core.BodyAnalysis

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (cfg : Config D Raw) (notes : Annotations Raw)

/-- **An attempt grows the state when its body does**: by the leaf of its number, its body's
leaves and its results, adding bounds at its body's addresses. -/
theorem attemptGrows : AttemptGrowsStatement cfg notes := by
  intro cursor key Γ mid w owns inputs body growsBody ids s k wf
  have entry := atEntry_entered cfg notes (.instruction cursor key) ids s k wf
  simp only [walkInstr, attemptExit, Instr.leafCount, Instr.addresses]
  generalize atEntry cfg notes (.instruction cursor key) ids s k = e at entry ⊢
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry ⊢
  have one : Grew cfg ((cursor.blocks, key) :: Term.addresses cursor.blocks body) E
      { E with leaves := E.leaves + 1 } 1 := Grew.leaves 1 entry.wf
  have two := Grew.discount (cfg.domain.leaves Ek [(.leaf E.leaves, D.index w)])
    (growsBody (bindIds ids inputs [.leaf E.leaves]) { E with leaves := E.leaves + 1 }
      (cfg.domain.leaves Ek [(.leaf E.leaves, D.index w)]) entry.wf)
  exact ((((Grew.of_entered cfg _ entry).trans one).trans
    (two.widen fun _ m => List.mem_cons_of_mem _ m)).trans
    (Grew.leaves mid.length two.2.1)).count (by rw [Nat.zero_add])

end

section
variable {D : Dialect} {Raw : Type} [DecidableEq Raw] (σ : Setting D Raw)

/-- **An attempt runs its entry of the skeleton when its body runs its skeleton**: the body runs
alone on every number that the beginning can give, that number on the attempt's input leaf; what
follows runs from every value that the body can return after a beginning, when the end of the
attempt can return, on the attempt's result leaves. -/
theorem attemptRuns : AttemptRunsStatement σ := by
  intro cursor key Γ mid w owns inputs body growsBody runsBody
  intro path ρ ids env s k table mid₀ outs rest after cont
  dsimp only
  intro scope sub notUndefined next
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k scope.wf
  rw [Instr.denote_attempt] at notUndefined ⊢
  simp only [Process.bind_assoc, Process.bind] at notUndefined ⊢
  simp only [walkInstr, attemptExit, Skel.stepOf] at sub next ⊢
  generalize atEntry σ.cfg σ.notes (.instruction cursor key) ids s k = e at entry sub next ⊢
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry sub next ⊢
  have scopeE := scope.grow entry.1 (Nat.le_of_eq entry.2.1.symm)
  have bodyGrew := growsBody (bindIds ids inputs [.leaf E.leaves]) { E with leaves := E.leaves + 1 }
    (σ.cfg.domain.leaves Ek [(.leaf E.leaves, D.index w)]) entry.wf
  have runsOne := fun (n : σ.sem.Val (D.index w)) => runsBody path
    (ρ.setFrom E.leaves [⟨D.index w, n⟩]) (bindIds ids inputs [.leaf E.leaves])
    (env.extend inputs (.cons n .nil)) { E with leaves := E.leaves + 1 }
    (σ.cfg.domain.leaves Ek [(.leaf E.leaves, D.index w)]) table .nil (fun values => .done values)
  generalize walk σ.cfg σ.notes (cursor.region key) body (bindIds ids inputs [.leaf E.leaves])
    { E with leaves := E.leaves + 1 } (σ.cfg.domain.leaves Ek [(.leaf E.leaves, D.index w)]) = inner
    at bodyGrew runsOne sub next ⊢
  simp only [discount_values, discount_leaves] at sub next ⊢
  have fresh : ∀ n, inner.state.leaves ≤ n → ρ n = none := fun n above => scope.fresh n (by
    rw [bodyGrew.2.2.2.1, entry.2.1] at above
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right _ 1) (Nat.le_add_right _ _)) above)
  refine Skel.Runs.attempt (fun n => body.denote σ.sem path (env.extend inputs (.cons n .nil)))
    (fun number begins => ?_) (fun number returned begins returns settles => ?_)
  · have runs := runsOne number
    rw [Process.bind_pure] at runs
    exact runs (scopeE.enterLeaf inputs number) sub
      (Process.Every.of_bind (Process.Every.of_bind_canReturn notUndefined begins))
      fun _ values _ _ _ _ => .done values
  · obtain ⟨le, fresh', reads⟩ := Leaves.results (Run := σ.Run) (R := σ.R)
      (table := inner.state.values.table) fresh returned
    exact next _ returned le fresh' reads (Process.Every.of_bind_canReturn
      (Process.Every.of_bind_canReturn (Process.Every.of_bind_canReturn notUndefined begins)
        returns) settles)

/-- **An attempt is sound when its body is.** Its beginning gives a valid number and never stops
`undefined`; on that number, on a new leaf, the body's entry state means the leaves, so it is not
dead and the body's refusals count; the end of the attempt never stops `undefined`; and the
attempt's results are new leaves that read what the body returned. -/
theorem attemptSound : AttemptSoundStatement σ := by
  intro laws cursor key Γ mid w owns inputs body growsBody soundBody
  intro path ρ ids env s k
  dsimp only
  intro inv steps defined facts everyFact unchanged
  have entry := atEntry_entered σ.cfg σ.notes (.instruction cursor key) ids s k inv.wf
  have entryInv := fun unchanged => atEntry_inv σ laws cursor key (.attempt w owns inputs body)
    (path := path) inv steps facts unchanged
  rw [Instr.denote_attempt]
  simp only [walkInstr, attemptExit, Instr.addresses] at unchanged ⊢
  simp only [Instr.site] at entryInv
  generalize atEntry σ.cfg σ.notes (.instruction cursor key) ids s k = e at entry entryInv unchanged ⊢
  obtain ⟨E, Ek⟩ := e
  dsimp only at entry entryInv unchanged ⊢
  have bodyGrew := growsBody (bindIds ids inputs [.leaf E.leaves]) { E with leaves := E.leaves + 1 }
    (σ.cfg.domain.leaves Ek [(.leaf E.leaves, D.index w)]) entry.wf
  have soundOne := fun (n : σ.sem.Val (D.index w)) => soundBody path
    (ρ.setFrom E.leaves [⟨D.index w, n⟩]) (bindIds ids inputs [.leaf E.leaves])
    (env.extend inputs (.cons n .nil)) { E with leaves := E.leaves + 1 }
    (σ.cfg.domain.leaves Ek [(.leaf E.leaves, D.index w)])
  generalize walk σ.cfg σ.notes (cursor.region key) body (bindIds ids inputs [.leaf E.leaves])
    { E with leaves := E.leaves + 1 } (σ.cfg.domain.leaves Ek [(.leaf E.leaves, D.index w)]) = inner
    at bodyGrew soundOne unchanged ⊢
  have discounted := Grew.discount (σ.cfg.domain.leaves Ek [(.leaf E.leaves, D.index w)]) bodyGrew
  obtain ⟨entryUnchanged, discountUnchanged⟩ :=
    refusals_split entry.2.2.2 discounted.2.2.2.2.1 unchanged
  have inv₁ := entryInv entryUnchanged
  -- On every number that the beginning gives: the body is sound there.
  have perNumber := fun (n : σ.sem.Val (D.index w)) (valid : σ.Valid ⟨D.index w, n⟩)
      (fact : Term.EveryFact σ (cursor.region key) body path (env.extend inputs (.cons n .nil))) =>
    have inv₂ := inv₁.enterLeaf inputs n valid
    have alive := discount_alive (σ.alive inv₂.means) { E with leaves := E.leaves + 1 } inner.state
    And.intro alive (And.intro inv₂ (soundOne n inv₂ defined fact (by
      rw [← alive]
      exact discountUnchanged)))
  simp only [Instr.EveryFact, Instr.EveryStep] at everyFact
  have begins := Process.every_and _ _ (laws.rules.begin w key path) everyFact
  simp only [Instr.EveryRequired, Instr.EveryStep, Instr.EveryLoop]
  refine ⟨?_, trivial, Process.every_mono _ _ (fun n both => (perNumber n both.1 both.2).2.2.2.1)
    (fun _ _ => trivial) begins, fun nodup apart recorded => Process.every_mono _ _
      (fun n both => (perNumber n both.1 both.2).2.2.2.2 (List.nodup_cons.mp nodup).2
        (fun q m bl key' place at_ =>
          apart q (by rw [← entry.2.2.1]; exact m) bl key' place (List.mem_cons_of_mem _ at_))
        fun p b bl key' inF place at_ => by
          have found := recorded p b bl key' inF place (List.mem_cons_of_mem _ at_)
          rwa [discount_bounds] at found)
      (fun _ _ => trivial) begins⟩
  rw [Process.every_bind]
  refine Process.every_mono _ _ (fun n both => ?_) (fun _ h => h.1) begins
  obtain ⟨alive, inv₂, every, -, -⟩ := perNumber n both.1 both.2
  rw [alive]
  rw [Process.every_bind]
  refine Process.every_mono _ _ (fun mids ret => ?_) (fun _ h => h) every
  rw [Process.every_bind]
  refine Process.every_mono _ _ (fun _ _ => ?_) (fun _ h => h) (laws.rules.settle w key path)
  obtain ⟨ρ₂, le₂, inv₃, reads₃⟩ := ret
  have le : ρ.Le ρ₂ := fun n v h => le₂ n v (Leaves.le_setFrom inv₁.fresh _ n v h)
  exact Returned.atResults le
    ⟨inv₃.fresh, fun τ x => by
        obtain ⟨id, found, read⟩ := inv₁.agree τ x
        exact ⟨id, found, Reads.mono bodyGrew.1 le read⟩, inv₁.bound, inv₃.wf⟩
    inv₃.valid (σ.domain.mono bodyGrew.1 le inv₁.means) (mem_live σ (σ.alive inv₃.means) _)
    inv₃.means reads₃

#print axioms attemptGrows
#print axioms attemptRuns
#print axioms attemptSound

end

end Zkc.Core.BodyAnalysis
